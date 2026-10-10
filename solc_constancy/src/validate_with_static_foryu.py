"""
Given a directory previously written by full_constancy_trace.py (a single --output-dir, whether
from a single-file run -- "results/" directly under it -- or a folder-batch run -- one "results/"
per analyzed input, nested under it), validates every results/*_annotated.json file against the
external reference checker (~/repos/foryu/bin/static_foryu, an independently implemented
liveness/constancy checker -- see PROGRESS.md), recording the verdict and how long each check
took. Every check is independent, so this runs them across a multiprocessing.Pool.

Writes <output_dir>/validation.csv, one row per annotated file checked.

This validates full_constancy_trace.py's own output (results/*_annotated.json), so only
--constancy is passed -- a liveness check here would be redundant (and slower): the annotated
files cover only the T/m/c/s occurrences, a subset of every position full_liveness_trace.py's
sweep already checks liveness for independently.

`static_foryu --constancy --csv -i <file>` prints one CSV line -- filename,
JSON_PROCESSING_OK|JSON_PROCESSING_ERROR, nblocks, ninstrs, preprocess_time_ns,
constancy_extract_time_ns, constancy_check_time_ns, CONSTANCY_VALID|CONSTANCY_INVALID|
CONSTANCY_ERROR. Confirmed directly against the real binary: its exit code is 0 even on
JSON_PROCESSING_ERROR, so pass/fail must be read from the parsed verdict fields, never from the
exit code; empty stdout means it crashed (matching run_experiments.sh's own "CRASH" convention).

Usage (no dependency on this project's own src/ being on PYTHONPATH -- pure stdlib):
    python3 validate_with_static_foryu.py path/to/full_constancy_trace_output/
    python3 validate_with_static_foryu.py path/to/output/ -cpus 8 --static-foryu /path/to/binary
"""
import argparse
import csv
import glob
import json
import os
import subprocess
import tempfile
import time
import multiprocessing as mp
from pathlib import Path
from typing import Any, Dict, List

# .../foryu/solc_constancy/src/validate_with_static_foryu.py -> .../foryu/bin/static_foryu
DEFAULT_STATIC_FORYU = str(Path(__file__).resolve().parents[2] / "bin" / "static_foryu")

VALIDATION_CSV_FIELDS = [
    "annotated_file", "wall_seconds", "returncode", "json_status", "nblocks", "ninstrs",
    "preprocess_ns", "constancy_result", "constancy_extract_ns", "constancy_check_ns", "error",
    "unverified_fact_count", "constancy_result_verified",
]


def _iter_blocks(obj: Any):
    """Every block dict anywhere in an annotated file (any nesting of contracts/objects/functions)."""
    if isinstance(obj, dict):
        for key, value in obj.items():
            if key == "blocks" and isinstance(value, list):
                yield from value
            elif isinstance(value, dict):
                yield from _iter_blocks(value)


def _strip_unverified(data: Any) -> int:
    """
    Removes, in place, every fact listed in a block's "constancy_unverified" from its "constancy"
    (and drops the "constancy_unverified" field itself), leaving only the part the checker can be
    expected to confirm locally. Returns how many facts were removed.
    """
    removed = 0
    for block in _iter_blocks(data):
        unverified = block.pop("constancy_unverified", None)
        if not unverified:
            continue
        for entry, unverified_entry in zip(block.get("constancy", []), unverified):
            for var, value in unverified_entry.items():
                if entry.get(var) == value:
                    del entry[var]
                    removed += 1
    return removed


def _find_annotated_files(output_dir: str) -> List[str]:
    """
    Every results/*_annotated.json under output_dir, at any depth -- matches both a single-file
    run (results/ directly under output_dir) and a folder-batch run (one results/ per analyzed
    input, in its own subdirectory of output_dir) with the same glob.
    """
    return sorted(glob.glob(os.path.join(output_dir, "**", "results", "*_annotated.json"), recursive=True))


def _run_static_foryu(annotated_file: str, static_foryu: str) -> Dict[str, Any]:
    """
    Runs static_foryu against one annotated file and returns its validation.csv row. Never
    trusts the subprocess's own exit code for pass/fail (confirmed unreliable: a malformed input
    still exits 0 under --csv) -- pass/fail lives entirely in the parsed verdict fields.
    """
    row: Dict[str, Any] = {field: "" for field in VALIDATION_CSV_FIELDS}
    row["annotated_file"] = annotated_file

    start = time.perf_counter()
    try:
        result = subprocess.run(
            [static_foryu, "--constancy", "--csv", "-i", annotated_file],
            capture_output=True, text=True, timeout=300,
        )
    except Exception as e:
        row["wall_seconds"] = time.perf_counter() - start
        row["error"] = str(e)
        return row
    row["wall_seconds"] = time.perf_counter() - start
    row["returncode"] = result.returncode

    line = result.stdout.strip()
    if not line:
        # Matches run_experiments.sh's own convention: empty stdout means static_foryu crashed
        row["error"] = f"CRASH (stderr: {result.stderr.strip()[:500]})"
        return row

    fields = line.split(",")
    if len(fields) < 5:
        row["error"] = f"unexpected --csv output shape: {line!r}"
        return row

    row["json_status"] = fields[1]
    row["nblocks"] = fields[2]
    row["ninstrs"] = fields[3]
    row["preprocess_ns"] = fields[4]
    if len(fields) >= 8:
        row["constancy_extract_ns"] = fields[5]
        row["constancy_check_ns"] = fields[6]
        row["constancy_result"] = fields[7]

    _check_verified_subset(annotated_file, static_foryu, row)
    return row


def _check_verified_subset(annotated_file: str, static_foryu: str, row: Dict[str, Any]) -> None:
    """
    Second verdict, on a copy of the file with every "constancy_unverified" fact removed: if the
    full file is CONSTANCY_INVALID but this is CONSTANCY_VALID, the rejection came only from
    facts that are sound but not locally verifiable, not from a wrong one. Skipped (same verdict
    as the full file) when there is nothing to remove.
    """
    if not row["constancy_result"]:
        return  # no verdict on the full file either -- nothing to compare against
    try:
        with open(annotated_file) as f:
            data = json.load(f)
    except (OSError, ValueError):
        return
    removed = _strip_unverified(data)
    row["unverified_fact_count"] = removed
    if removed == 0:
        row["constancy_result_verified"] = row["constancy_result"]
        return

    with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as f:
        json.dump(data, f)
        stripped_path = f.name
    try:
        result = subprocess.run([static_foryu, "--constancy", "--csv", "-i", stripped_path],
                                capture_output=True, text=True, timeout=300)
        fields = result.stdout.strip().split(",")
        row["constancy_result_verified"] = fields[7] if len(fields) >= 8 else "CRASH"
    except Exception as e:
        row["constancy_result_verified"] = f"ERROR: {e}"
    finally:
        os.unlink(stripped_path)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("output_dir", help="A directory previously written by full_constancy_trace.py")
    parser.add_argument("--static-foryu", default=DEFAULT_STATIC_FORYU,
                        help="Path to the static_foryu checker binary")
    parser.add_argument("-cpus", "--num-cpus", default=max(os.cpu_count() // 4 - 1, 1), type=int,
                        help="Determines how many CPUS are executed in parallel (one per "
                             "annotated file; default: max(cpu_count // 4 - 1, 1))", dest="num_cpus")
    args = parser.parse_args()

    if not os.path.isfile(args.static_foryu):
        raise SystemExit(f"static_foryu binary not found at {args.static_foryu}")

    annotated_files = _find_annotated_files(args.output_dir)
    if not annotated_files:
        raise SystemExit(f"No results/*_annotated.json files found under {args.output_dir}")

    with mp.Pool(args.num_cpus) as pool:
        rows = pool.starmap(_run_static_foryu, [(f, args.static_foryu) for f in annotated_files])

    csv_path = os.path.join(args.output_dir, "validation.csv")
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=VALIDATION_CSV_FIELDS)
        writer.writeheader()
        writer.writerows(rows)

    n_valid = sum(1 for row in rows if row["constancy_result"] == "CONSTANCY_VALID")
    n_valid_verified = sum(1 for row in rows if row["constancy_result_verified"] == "CONSTANCY_VALID")
    print(f"Validated {len(rows)} file(s): {n_valid} CONSTANCY_VALID in full, {n_valid_verified} with "
          f"unverified facts stripped, wrote {csv_path}")


if __name__ == "__main__":
    main()
