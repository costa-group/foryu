"""
Given a directory previously written by full_constancy_trace.py (a single --output-dir, whether
from a single-file run -- "results/" directly under it -- or a folder-batch run -- one "results/"
per analyzed input, nested under it), validates every results/*_annotated.json file against the
external reference checker (~/repos/foryu/bin/static_foryu, an independently implemented
liveness/constancy checker -- see PROGRESS.md), recording the verdict and how long each check
took. Every check is independent, so this runs them across a multiprocessing.Pool.

Writes <output_dir>/validation.csv, one row per annotated file checked.

Mirrors the project's own existing validation convention (run_experiments.sh, at the root of the
foryu repo): `static_foryu --liveness subset --constancy --csv -i <file>` prints one CSV line --
filename, JSON_PROCESSING_OK|JSON_PROCESSING_ERROR, nblocks, ninstrs, preprocess_time_ns,
[liveness_extract_time_ns, liveness_check_time_ns, LIVENESS_VALID|...] (if --liveness passed),
[constancy_extract_time_ns, constancy_check_time_ns, CONSTANCY_VALID|...] (if --constancy passed).
Confirmed directly against the real binary: its exit code is 0 even on JSON_PROCESSING_ERROR, so
pass/fail must be read from the parsed verdict fields, never from the exit code; empty stdout
means it crashed (matching run_experiments.sh's own "CRASH" convention).

Usage (no dependency on this project's own src/ being on PYTHONPATH -- pure stdlib):
    python3 validate_with_static_foryu.py path/to/full_constancy_trace_output/
    python3 validate_with_static_foryu.py path/to/output/ -cpus 8 --static-foryu /path/to/binary
"""
import argparse
import csv
import glob
import os
import subprocess
import time
import multiprocessing as mp
from pathlib import Path
from typing import Any, Dict, List

# .../foryu/solc_constancy/src/validate_with_static_foryu.py -> .../foryu/bin/static_foryu
DEFAULT_STATIC_FORYU = str(Path(__file__).resolve().parents[2] / "bin" / "static_foryu")

VALIDATION_CSV_FIELDS = [
    "annotated_file", "wall_seconds", "returncode", "json_status", "nblocks", "ninstrs",
    "preprocess_ns", "liveness_result", "liveness_extract_ns", "liveness_check_ns",
    "constancy_result", "constancy_extract_ns", "constancy_check_ns", "error",
]


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
            [static_foryu, "--liveness", "subset", "--constancy", "--csv", "-i", annotated_file],
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
        row["liveness_extract_ns"] = fields[5]
        row["liveness_check_ns"] = fields[6]
        row["liveness_result"] = fields[7]
    if len(fields) >= 11:
        row["constancy_extract_ns"] = fields[8]
        row["constancy_check_ns"] = fields[9]
        row["constancy_result"] = fields[10]
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("output_dir", help="A directory previously written by full_constancy_trace.py")
    parser.add_argument("--static-foryu", default=DEFAULT_STATIC_FORYU,
                        help="Path to the static_foryu checker binary")
    parser.add_argument("-cpus", "--num-cpus", default=1, type=int,
                        help="Determines how many CPUS are executed in parallel", dest="num_cpus")
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
    print(f"Validated {len(rows)} file(s): {n_valid} CONSTANCY_VALID, wrote {csv_path}")


if __name__ == "__main__":
    main()
