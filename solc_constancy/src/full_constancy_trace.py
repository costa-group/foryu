"""
Given a solc standard-json input, dumps every intermediate compilation revealed by DEFAULT_
OPTIMIZER_SEQUENCE's T/m/c/s occurrences (dump_steps.py) and annotates the constancy each one
reveals (compare_constancy.py), writing the annotated result to --output-dir/results/ and the
before/after pair plus a manifest per occurrence to --output-dir/intermediate/ -- separating the
actual constancy result (safe to hand someone, or point other tooling at, on its own) from the
intermediate compilations and bookkeeping kept alongside it for reference. Each on-disk annotated
file is reshaped back into solc's own standard-json output nesting ({"contracts": {filename:
{contract_name: {"yulCFGJson": ...}}}}) rather than this project's internal flattened
{contract_name: yulCFGJson} shape -- see _wrap_in_original_structure.

If input_path is a directory, it's searched recursively for "*_standard_input.json" files, and
each gets its own subdirectory of --output-dir (mirroring the input directory's own layout) --
the folder-batch mode.

Also writes --output-dir/results.csv, one row per analyzed input file, breaking down wall time
into solc compilation, constancy fact analysis, annotation, and file dumping (see
process_json_input) -- so a batch run's cost can be attributed to a specific phase. See
validate_with_static_foryu.py for a separate, follow-on script that validates this run's
--output-dir/**/results/*_annotated.json files against the external static_foryu checker.

Usage (run from src/, or with src/ on PYTHONPATH):
    python3 full_constancy_trace.py contract.standard-json.json --output-dir out/
    python3 full_constancy_trace.py path/to/many_contracts/ --output-dir out/
"""
import argparse
import csv
import glob
import json
import logging
import os
import sys
import time
import multiprocessing as mp
from pathlib import Path
from typing import Any, Dict, List, Optional

from constancy import compare_constancy, dump_steps
from constancy.seed_extraction import iter_block_scopes
from execution.sol_compilation import DEFAULT_OPTIMIZER_SEQUENCE
from global_params.types import Yul_CFG_T

# results.csv column order -- see process_json_input's returned row shape
RESULTS_CSV_FIELDS = [
    "input_file", "output_dir", "occurrence_count", "manifest_entry_count",
    "compile_seconds", "fact_analysis_seconds", "annotation_seconds", "dump_seconds",
    "total_seconds", "error",
]


def _count_constancy_facts(annotated: Dict[str, Yul_CFG_T]) -> int:
    return sum(len(entry)
               for yul_cfg_json in annotated.values()
               for _, blocks in iter_block_scopes(yul_cfg_json)
               for block in blocks
               for entry in block.get("constancy", []))


def _wrap_in_original_structure(yul_cfg_dict: Dict[str, Yul_CFG_T],
                                structure: Dict[str, List[str]]) -> Dict[str, Any]:
    """
    yul_cfg_dict (the flattened {contract_name: yulCFGJson} shape used throughout this project)
    reshaped back into solc's own standard-json output nesting -- {"contracts": {filename:
    {contract_name: {"yulCFGJson": yulCFGJson}}}} -- using structure (filename -> [contract
    names], captured once from the occurrence's baseline compile -- see dump_steps.dump_occurrence
    -- since the file/contract layout is identical across every occurrence of the same source).
    A contract present in structure but missing from yul_cfg_dict (e.g. it compiled to a null
    yulCFGJson) is simply omitted.
    """
    contracts: Dict[str, Dict[str, Any]] = {}
    for filename, contract_names in structure.items():
        for contract_name in contract_names:
            if contract_name in yul_cfg_dict:
                contracts.setdefault(filename, {})[contract_name] = {"yulCFGJson": yul_cfg_dict[contract_name]}
    return {"contracts": contracts}


def process_standard_json(json_input: Dict[str, Any], output_dir: str,
                          base_sequence: str = DEFAULT_OPTIMIZER_SEQUENCE,
                          solc_executable: str = "solc",
                          stats_out: Optional[Dict[str, float]] = None,
                          compile_timeout: Optional[float] = None) -> List[Dict[str, Any]]:
    """
    Dumps every occurrence's before/after pair (dump_steps.dump_all_occurrences, isolated via
    disable_stack_allocation=True -- this diagnostic tool's whole purpose is isolated per-step
    comparison, see seed_extraction.with_stack_allocation_disabled) into <output_dir>/intermediate/
    and annotates constancy for each (compare_constancy.annotate_constancy_between). An occurrence
    that revealed nothing (no facts, no restructuring warnings) still has its before/after pair on
    disk, but is left out of the annotated output and the manifest.

    Writes <output_dir>/intermediate/manifest.json summarizing every occurrence that did reveal
    something (metadata and file names only), alongside that same directory's before/after files.
    Writes each occurrence's annotated result to <output_dir>/results/<...>_annotated.json,
    reshaped into solc's own output nesting (_wrap_in_original_structure) -- kept separate from
    the intermediate files so the actual constancy results can be handed off or consumed on their
    own. The *returned* manifest additionally carries each entry's in-memory "annotated"
    per-contract yulCFGJson dict (still the flattened shape, not the on-disk nesting), so a caller
    (or a test) can use it directly without a disk round trip.

    stats_out, when given, is threaded into dump_all_occurrences ("compile_seconds",
    "dump_seconds") and every annotate_constancy_between call ("fact_analysis_seconds",
    "annotation_seconds", accumulated across occurrences); also gets "occurrence_count" set to
    the total number of occurrences dumped (manifest, returned separately, is a filtered subset
    of these -- only the ones that revealed something), and "dump_seconds" further extended to
    cover this function's own results/*_annotated.json and manifest.json writes.

    compile_timeout, when given, bounds each solc invocation (seconds) -- an occurrence whose
    compile exceeds it is treated as a compile failure (skipped, logged), rather than left to
    run unbounded; see dump_steps.dump_occurrence.
    """
    results_dir = os.path.join(output_dir, "results")
    intermediate_dir = os.path.join(output_dir, "intermediate")
    os.makedirs(results_dir, exist_ok=True)

    occurrences = dump_steps.dump_all_occurrences(json_input, intermediate_dir, base_sequence=base_sequence,
                                                  solc_executable=solc_executable,
                                                  disable_stack_allocation=True, stats_out=stats_out,
                                                  compile_timeout=compile_timeout)
    if stats_out is not None:
        stats_out["occurrence_count"] = len(occurrences)

    manifest = []
    for occurrence in occurrences:
        print("OCURRENCE:", occurrence['step'], occurrence['step_index'])
        annotated, restructuring_warning_count = compare_constancy.annotate_constancy_between(
            occurrence["before"], occurrence["after"], stats_out=stats_out)
        fact_count = _count_constancy_facts(annotated)
        if fact_count == 0 and restructuring_warning_count == 0:
            continue

        annotated_file = f"occ_{occurrence['index']:03d}_{occurrence['step']}{occurrence['step_index']}_annotated.json"
        dump_start = time.perf_counter()
        with open(os.path.join(results_dir, annotated_file), "w") as f:
            json.dump(_wrap_in_original_structure(annotated, occurrence["structure"]), f, indent=2)
        if stats_out is not None:
            stats_out["dump_seconds"] = stats_out.get("dump_seconds", 0.0) + (time.perf_counter() - dump_start)

        manifest.append({
            "index": occurrence["index"], "step": occurrence["step"], "step_index": occurrence["step_index"],
            "position": occurrence["position"], "fact_count": fact_count,
            "restructuring_warning_count": restructuring_warning_count,
            "before_file": occurrence["before_file"], "after_file": occurrence["after_file"],
            "annotated_file": annotated_file, "annotated": annotated,
        })

    manifest_start = time.perf_counter()
    with open(os.path.join(intermediate_dir, "manifest.json"), "w") as f:
        json.dump([{key: value for key, value in entry.items() if key != "annotated"} for entry in manifest],
                  f, indent=2)
    if stats_out is not None:
        stats_out["dump_seconds"] = stats_out.get("dump_seconds", 0.0) + (time.perf_counter() - manifest_start)

    return manifest


def _find_standard_json_inputs(input_path: str) -> List[str]:
    if os.path.isfile(input_path):
        return [input_path]
    return sorted(glob.glob(os.path.join(input_path, "**", "*_standard_input.json"), recursive=True))


def process_json_input(json_path: str, args: argparse.Namespace) -> Dict[str, Any]:
    """
    Processes one input file and returns its results.csv row (RESULTS_CSV_FIELDS). Any exception
    raised while processing this file is caught here rather than left to propagate -- so one bad
    input in a large folder-batch run produces an error row instead of taking down the whole
    mp.Pool.starmap batch -- and recorded in the row's "error" field, with every timing field
    left at 0.
    """
    start = time.perf_counter()
    subdir = None
    try:
        # Determine whether the input is a JSON path or not
        if os.path.isdir(args.input_path):
            relative_dir = os.path.relpath(os.path.dirname(json_path), args.input_path)
            subdir = os.path.join(args.output_dir, relative_dir) if relative_dir != "." \
                else os.path.join(args.output_dir, Path(json_path).stem)
        else:
            subdir = args.output_dir

        with open(json_path) as f:
            json_input = json.load(f)

        print("Executing ", json_path)
        stats: Dict[str, float] = {}
        manifest = process_standard_json(json_input, subdir, base_sequence=args.base_sequence,
                                         solc_executable=args.solc, stats_out=stats,
                                         compile_timeout=args.compile_timeout)
        print(f"{json_path}: wrote {len(manifest)} occurrence(s) to {subdir}")

        return {
            "input_file": json_path, "output_dir": subdir,
            "occurrence_count": stats.get("occurrence_count", 0),
            "manifest_entry_count": len(manifest),
            "compile_seconds": stats.get("compile_seconds", 0.0),
            "fact_analysis_seconds": stats.get("fact_analysis_seconds", 0.0),
            "annotation_seconds": stats.get("annotation_seconds", 0.0),
            "dump_seconds": stats.get("dump_seconds", 0.0),
            "total_seconds": time.perf_counter() - start,
            "error": "",
        }
    except Exception as e:
        logging.error(f"Failed to process {json_path}: {e}")
        return {
            "input_file": json_path, "output_dir": subdir or "",
            "occurrence_count": 0, "manifest_entry_count": 0,
            "compile_seconds": 0.0, "fact_analysis_seconds": 0.0,
            "annotation_seconds": 0.0, "dump_seconds": 0.0,
            "total_seconds": time.perf_counter() - start,
            "error": str(e),
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_path", help="A solc standard-json input file, or a directory "
                                           "containing one or more (searched recursively for *_standard_input.json)")
    parser.add_argument("--output-dir", default="full_constancy_trace_output",
                        help="Directory to write results to")
    parser.add_argument("--base-sequence", default=DEFAULT_OPTIMIZER_SEQUENCE,
                        help="Yul optimizer step sequence to trace occurrences of")
    parser.add_argument("-cpus", "--num-cpus", default=max(os.cpu_count() // 4 - 1, 1), type=int,
                        help="Determines how many CPUS are executed in parallel (one per input "
                             "file; default: max(cpu_count // 4 - 1, 1))", dest="num_cpus")
    parser.add_argument("--solc", default="solc", help="Path to solc binary (default: solc on PATH)")
    parser.add_argument("--compile-timeout", default=300, type=float, dest="compile_timeout",
                        help="Seconds to allow each solc compile before treating it as a failed "
                             "occurrence (default: 300); pass 0 or a negative value for no timeout")
    args = parser.parse_args()
    if args.compile_timeout is not None and args.compile_timeout <= 0:
        args.compile_timeout = None

    inputs = _find_standard_json_inputs(args.input_path)
    if not inputs:
        logging.error(f"No standard-json input found at {args.input_path}")
        sys.exit(1)

    with mp.Pool(args.num_cpus) as pool:
        rows = pool.starmap(process_json_input, [(json_path, args) for json_path in inputs])

    os.makedirs(args.output_dir, exist_ok=True)
    csv_path = os.path.join(args.output_dir, "results.csv")
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=RESULTS_CSV_FIELDS)
        writer.writeheader()
        writer.writerows(rows)
    print(f"Wrote timing results for {len(rows)} file(s) to {csv_path}")


if __name__ == "__main__":
    main()
