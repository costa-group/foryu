"""
Given a solc standard-json input, a current Yul optimizer step sequence, and the next step(s)
to apply on top of it, compiles both and reports the constancy that one extra application
reveals -- generalizing what used to be two near-duplicate scripts (annotate.py's production
path, always "Tm" at the end of DEFAULT_OPTIMIZER_SEQUENCE; annotate_single_step.py, always one
of T/m/c/s on top of an empty baseline) into a single script driven by explicit flags.

Usage (run from src/, or with src/ on PYTHONPATH):
    python3 next_step_constancy.py contract.standard-json.json --next-step Tm --output out.json
    python3 next_step_constancy.py contract.standard-json.json --sequence "" --next-step s \\
        --disable-stack-allocation --output out.json
"""
import argparse
import json
import logging
import sys

from constancy import compare_constancy, dump_steps
from constancy.seed_extraction import isolate_cleanup_sequence, probe_sequence
from execution.sol_compilation import DEFAULT_OPTIMIZER_SEQUENCE


def compute_constancy_for_next_step(json_input, sequence: str = DEFAULT_OPTIMIZER_SEQUENCE,
                                    next_step: str = "Tm", solc_executable: str = "solc",
                                    disable_stack_allocation: bool = False):
    """
    Compiles json_input with sequence as the baseline and sequence+next_step as the probe
    (dump_steps.dump_occurrence, reused directly rather than duplicating the compile logic),
    then annotates the constancy that one extra application of next_step reveals
    (compare_constancy.annotate_constancy_between).

    Returns (annotated baseline per contract, restructuring_warning_count), or (None, None) if
    either compilation fails.
    """
    occurrence = {
        "step": next_step, "step_index": 0, "index": 0, "position": -1,
        "seq_before": isolate_cleanup_sequence(sequence),
        "seq_after": probe_sequence(sequence, [next_step]),
    }
    dumped = dump_steps.dump_occurrence(json_input, occurrence, solc_executable=solc_executable,
                                        disable_stack_allocation=disable_stack_allocation)
    if dumped is None:
        return None, None

    return compare_constancy.annotate_constancy_between(dumped["before"], dumped["after"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_json", help="Path to a solc standard-json input file")
    parser.add_argument("--sequence", default=DEFAULT_OPTIMIZER_SEQUENCE,
                        help="Current Yul optimizer step sequence to keep/annotate (the baseline)")
    parser.add_argument("--next-step", default="Tm",
                        help="Step(s) to apply on top of --sequence to discover constancy "
                             "(default 'Tm', the production contract; e.g. 's' or 'c' for "
                             "isolated single-step probing)")
    parser.add_argument("--solc", default="solc", help="Path to solc binary (default: solc on PATH)")
    parser.add_argument("--output", default="constancy_output.json",
                        help="Where to write the annotated yulCFGJson output")
    parser.add_argument("--disable-stack-allocation", action="store_true",
                        help="Force solc's StackCompressor off (see seed_extraction."
                             "with_stack_allocation_disabled) -- for isolated single-step "
                             "probing, not the production default")
    args = parser.parse_args()

    with open(args.input_json) as f:
        json_input = json.load(f)

    annotated, restructuring_warning_count = compute_constancy_for_next_step(
        json_input, sequence=args.sequence, next_step=args.next_step, solc_executable=args.solc,
        disable_stack_allocation=args.disable_stack_allocation)
    if annotated is None:
        logging.error("Compilation failed; no output written")
        sys.exit(1)

    with open(args.output, "w") as f:
        json.dump(annotated, f, indent=2)

    print(f"Wrote annotated yulCFGJson (sequence={args.sequence!r}, next_step={args.next_step!r}) "
         f"to {args.output} (restructuring_warning_count={restructuring_warning_count})")


if __name__ == "__main__":
    main()
