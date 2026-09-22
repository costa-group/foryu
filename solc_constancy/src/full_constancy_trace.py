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

Usage (run from src/, or with src/ on PYTHONPATH):
    python3 full_constancy_trace.py contract.standard-json.json --output-dir out/
    python3 full_constancy_trace.py path/to/many_contracts/ --output-dir out/
"""
import argparse
import glob
import json
import logging
import os
import sys
import multiprocessing as mp
from pathlib import Path
from typing import Any, Dict, List

from constancy import compare_constancy, dump_steps
from constancy.seed_extraction import iter_block_scopes
from execution.sol_compilation import DEFAULT_OPTIMIZER_SEQUENCE
from global_params.types import Yul_CFG_T


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
                          solc_executable: str = "solc") -> List[Dict[str, Any]]:
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
    """
    results_dir = os.path.join(output_dir, "results")
    intermediate_dir = os.path.join(output_dir, "intermediate")
    os.makedirs(results_dir, exist_ok=True)

    occurrences = dump_steps.dump_all_occurrences(json_input, intermediate_dir, base_sequence=base_sequence,
                                                  solc_executable=solc_executable,
                                                  disable_stack_allocation=True)
    manifest = []
    for occurrence in occurrences:
        annotated, restructuring_warning_count = compare_constancy.annotate_constancy_between(
            occurrence["before"], occurrence["after"])
        fact_count = _count_constancy_facts(annotated)
        if fact_count == 0 and restructuring_warning_count == 0:
            continue

        annotated_file = f"occ_{occurrence['index']:03d}_{occurrence['step']}{occurrence['step_index']}_annotated.json"
        with open(os.path.join(results_dir, annotated_file), "w") as f:
            json.dump(_wrap_in_original_structure(annotated, occurrence["structure"]), f, indent=2)

        manifest.append({
            "index": occurrence["index"], "step": occurrence["step"], "step_index": occurrence["step_index"],
            "position": occurrence["position"], "fact_count": fact_count,
            "restructuring_warning_count": restructuring_warning_count,
            "before_file": occurrence["before_file"], "after_file": occurrence["after_file"],
            "annotated_file": annotated_file, "annotated": annotated,
        })

    with open(os.path.join(intermediate_dir, "manifest.json"), "w") as f:
        json.dump([{key: value for key, value in entry.items() if key != "annotated"} for entry in manifest],
                  f, indent=2)

    return manifest


def _find_standard_json_inputs(input_path: str) -> List[str]:
    if os.path.isfile(input_path):
        return [input_path]
    return sorted(glob.glob(os.path.join(input_path, "**", "*_standard_input.json"), recursive=True))


def process_json_input(json_path: str, args: argparse.Namespace):
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
    manifest = process_standard_json(json_input, subdir, base_sequence=args.base_sequence,
                                     solc_executable=args.solc)
    print(f"{json_path}: wrote {len(manifest)} occurrence(s) to {subdir}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_path", help="A solc standard-json input file, or a directory "
                                           "containing one or more (searched recursively for *_standard_input.json)")
    parser.add_argument("--output-dir", default="full_constancy_trace_output",
                        help="Directory to write results to")
    parser.add_argument("--base-sequence", default=DEFAULT_OPTIMIZER_SEQUENCE,
                        help="Yul optimizer step sequence to trace occurrences of")
    parser.add_argument("-cpus", "--num-cpus", default=1, type=int,
                        help="Determines how many CPUS are executed in parallel", dest="num_cpus")
    parser.add_argument("--solc", default="solc", help="Path to solc binary (default: solc on PATH)")
    args = parser.parse_args()

    inputs = _find_standard_json_inputs(args.input_path)
    if not inputs:
        logging.error(f"No standard-json input found at {args.input_path}")
        sys.exit(1)

    with mp.Pool(args.num_cpus) as pool:
        pool.starmap(process_json_input, [(json_path, args) for json_path in inputs])


if __name__ == "__main__":
    main()
