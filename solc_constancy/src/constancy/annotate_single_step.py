"""
Diagnostic variant of annotate.py: tests the constancy analysis using a SINGLE constant-
propagating step (T, m, c, or s) as the only thing probed on top of a bare baseline -- by
default, no optimizer steps at all beyond solc's own always-mandatory preprocessing
(Disambiguator, then "hgfo" = FunctionHoister/FunctionGrouper/BlockFlattener/
ForLoopInitRewriter, then NameSimplifier -- see OptimiserSuite::run in libyul/optimiser/
Suite.cpp). These run unconditionally before any user-supplied optimizerSteps and are never
optional, so base_sequence="" already means "preprocessing only, nothing else" -- see
PROGRESS.md's dated entry.

Reuses annotate.py's annotate_constancy_file exactly as-is (no duplicated compile/annotate/
write logic) -- this script only adds a CLI surface for picking a single step and defaulting
the baseline to "no further optimization". Always passes disable_stack_allocation=True, forcing
solc's StackCompressor off (see seed_extraction.with_stack_allocation_disabled) -- without it,
that mandatory phase can duplicate/restructure large amounts of code based on stack-pressure
differences the single step under test can shift, confounding exactly the isolated comparison
this tool exists to make (see PROGRESS.md).

Usage (run from src/, or with src/ on PYTHONPATH):
    python3 constancy/annotate_single_step.py contract.standard-json.json --step s --output out.json
"""
import argparse
import logging
import sys

from constancy.annotate import annotate_constancy_file

# Steps this project's analysis is prepared to test in isolation -- the two production steps
# (T, m), plus the two additional ones occurrence_trace.py also traces (c, s)
TESTABLE_STEPS = ["T", "m", "c", "s"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_json", help="Path to a solc standard-json input file")
    parser.add_argument("--step", required=True, choices=TESTABLE_STEPS,
                        help="Single step to probe in isolation")
    parser.add_argument("--solc", default="solc", help="Path to solc binary (default: solc on PATH)")
    parser.add_argument("--output", default="constancy_output.json",
                        help="Where to write the annotated yulCFGJson output")
    parser.add_argument("--base-sequence", default="",
                        help="Optimizer step sequence to use as the baseline (default: none -- "
                             "just solc's own always-mandatory preprocessing)")
    args = parser.parse_args()

    if not annotate_constancy_file(args.input_json, args.output, solc_executable=args.solc,
                                   base_sequence=args.base_sequence, steps_to_consider=[args.step],
                                   disable_stack_allocation=True):
        logging.error("Compilation failed; no output written")
        sys.exit(1)

    print(f"Wrote annotated yulCFGJson (base_sequence={args.base_sequence!r}, step={args.step}) to {args.output}")


if __name__ == "__main__":
    main()
