"""
Compiles a contract at every occurrence of a small set of Yul optimizer steps
("T"=LiteralRematerialiser, "m"=Rematerialiser, "c"=CommonSubexpressionEliminator,
"s"=ExpressionSimplifier) within a given sequence -- reusing modifications.py's
truncate_sequence/find_occurrences technique (ported here rather than imported, since
modifications.py unconditionally requires the unrelated `deepdiff` package at import time).

Each occurrence's before/after pair shares an identical prefix except for the one extra step
character, so seed_extraction.py's structural comparator (which matches instructions by
unifying a baseline<->probe variable correspondence, not by name -- see that module's docstring)
only needs this one before/after pair to make sense, not consistency across occurrences.
Per-occurrence compilations use their own, mutually incomparable SSA naming (a renaming step
sits between many occurrences) and are never merged across occurrences.

Each occurrence's seq_before/seq_after is passed through seed_extraction.isolate_cleanup_sequence,
which appends an explicit, empty cleanup delimiter (":") whenever the truncated prefix doesn't
already contain one. Without this, solc silently runs its own default cleanup sequence
("fDnTOcmuO" -- itself containing "T" and "m") after any colon-less sequence, which for most
occurrences here (everything before DEFAULT_OPTIMIZER_SEQUENCE's own real colon) would
otherwise confound the comparison with steps neither seq_before nor seq_after asked for. This
is a no-op for the few occurrences that fall after the real colon (their prefix already
contains it) -- see PROGRESS.md for the empirical effect size.

This module only compiles and dumps; it does not compute or annotate constancy (see
compare_constancy.py for that) -- keeping the two concerns independently reusable, per the
main entry scripts (next_step_constancy.py, full_constancy_trace.py) that compose them.
"""
import argparse
import copy
import json
import logging
import os
from typing import Any, Dict, List, Optional, TypedDict

from constancy.seed_extraction import isolate_cleanup_sequence, with_stack_allocation_disabled
from execution.sol_compilation import DEFAULT_OPTIMIZER_SEQUENCE, SolidityCompilation
from global_params.types import Yul_CFG_T

# Steps this project's analysis is built around -- the two production steps (T, m), plus the
# two additional ones this module also traces (c, s)
PROPAGATION_STEPS_TO_TRACE = ["T", "m", "c", "s"]


class Occurrence(TypedDict):
    step: str
    step_index: int
    index: int
    position: int
    seq_before: str
    seq_after: str


def find_occurrences(seq: str, step: str) -> List[int]:
    """
    Every index in seq where the step's abbreviation character occurs. Ported from
    modifications.py (not imported: that module unconditionally requires the `deepdiff`
    package at import time, an unrelated dependency this module doesn't need).
    """
    return [i for i, ch in enumerate(seq) if ch == step]


def truncate_sequence(seq: str, cut_index: int, include_cut: bool) -> str:
    """
    A syntactically valid prefix of seq ending at cut_index (closing any brackets still open at
    that point). If include_cut, the character at cut_index is kept; otherwise the prefix stops
    right before it. Ported from modifications.py, see find_occurrences.
    """
    end = cut_index + 1 if include_cut else cut_index
    prefix = seq[:end]
    depth = 0
    for ch in prefix:
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
    return prefix + "]" * depth


def enumerate_occurrences(base_sequence: str = DEFAULT_OPTIMIZER_SEQUENCE,
                          steps_to_consider: List[str] = PROPAGATION_STEPS_TO_TRACE) -> List[Occurrence]:
    """
    Every occurrence of every step in steps_to_consider within base_sequence, as an isolated
    before/after pair (seq_before/seq_after share an identical prefix except for that one extra
    step character), in chronological (position) order across all steps combined.
    seq_before/seq_after are each passed through isolate_cleanup_sequence -- a no-op for an
    occurrence that falls after base_sequence's own real colon (its truncated prefix already
    contains it), otherwise appending an explicit, empty cleanup delimiter so solc doesn't
    silently run its own default cleanup on top of the truncated content (see the module
    docstring).
    """
    occurrences = []
    for step in steps_to_consider:
        for step_index, position in enumerate(find_occurrences(base_sequence, step)):
            occurrences.append({
                "step": step,
                "step_index": step_index,
                "position": position,
                "seq_before": isolate_cleanup_sequence(
                    truncate_sequence(base_sequence, position, include_cut=False)),
                "seq_after": isolate_cleanup_sequence(
                    truncate_sequence(base_sequence, position, include_cut=True)),
            })

    occurrences.sort(key=lambda occurrence: occurrence["position"])
    for index, occurrence in enumerate(occurrences):
        occurrence["index"] = index

    return occurrences


def dump_occurrence(json_input: Dict[str, Any], occurrence: Occurrence, solc_executable: str = "solc",
                    disable_stack_allocation: bool = False) -> Optional[Dict[str, Dict[str, Yul_CFG_T]]]:
    """
    Compiles occurrence's seq_before/seq_after pair. Returns {"before": {contract: yulCFGJson},
    "after": {contract: yulCFGJson}}, or None if either compilation fails.

    disable_stack_allocation, when True, forces solc's StackCompressor off for both compiles
    (seed_extraction.with_stack_allocation_disabled) -- a mandatory phase, unrelated to any step
    being probed, that can duplicate or restructure large amounts of code based on stack-
    pressure differences a single extra step can shift, confounding an isolated before/after
    comparison (see PROGRESS.md). Defaults to False so this function's default behavior doesn't
    change the kept CFG's actual compiled shape; callers doing isolated per-step probing (e.g.
    full_constancy_trace.py) pass True explicitly.
    """
    prepared_input = with_stack_allocation_disabled(json_input) if disable_stack_allocation else json_input
    try:
        baseline_cfg = SolidityCompilation.from_json_input(copy.deepcopy(prepared_input),
                                                           optimizer_steps=occurrence["seq_before"],
                                                           solc_executable=solc_executable)
        probe_cfg = SolidityCompilation.from_json_input(copy.deepcopy(prepared_input),
                                                        optimizer_steps=occurrence["seq_after"],
                                                        solc_executable=solc_executable)
    except Exception as e:
        logging.warning(f"Occurrence {occurrence['step']}#{occurrence['step_index']} "
                        f"(position {occurrence['position']}) failed to compile: {e}")
        return None

    if baseline_cfg is None or probe_cfg is None:
        return None

    return {"before": baseline_cfg, "after": probe_cfg}


def dump_all_occurrences(json_input: Dict[str, Any], output_dir: str,
                         base_sequence: str = DEFAULT_OPTIMIZER_SEQUENCE,
                         steps_to_consider: List[str] = PROPAGATION_STEPS_TO_TRACE,
                         solc_executable: str = "solc", disable_stack_allocation: bool = False) -> List[Dict[str, Any]]:
    """
    Compiles every occurrence of steps_to_consider in base_sequence (enumerate_occurrences) and
    writes one <output_dir>/occ_XXX_<step><step_index>_before.json / _after.json pair per
    occurrence that compiled successfully.

    Returns a manifest list, one entry per occurrence written, carrying both the occurrence's
    own fields and the in-memory "before"/"after" per-contract yulCFGJson dicts dump_occurrence
    produced -- so a caller (e.g. full_constancy_trace.py) can use them directly without having
    to re-read its own output off disk.
    """
    os.makedirs(output_dir, exist_ok=True)
    manifest = []
    for occurrence in enumerate_occurrences(base_sequence, steps_to_consider):
        dumped = dump_occurrence(json_input, occurrence, solc_executable=solc_executable,
                                 disable_stack_allocation=disable_stack_allocation)
        if dumped is None:
            continue

        prefix = f"occ_{occurrence['index']:03d}_{occurrence['step']}{occurrence['step_index']}"
        before_file = f"{prefix}_before.json"
        after_file = f"{prefix}_after.json"
        with open(os.path.join(output_dir, before_file), "w") as f:
            json.dump(dumped["before"], f, indent=2)
        with open(os.path.join(output_dir, after_file), "w") as f:
            json.dump(dumped["after"], f, indent=2)

        manifest.append({
            **occurrence,
            "before_file": before_file,
            "after_file": after_file,
            "before": dumped["before"],
            "after": dumped["after"],
        })

    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_json", help="Path to a solc standard-json input file")
    parser.add_argument("--output-dir", default="dump_steps_output",
                        help="Directory to write one before/after JSON pair per occurrence")
    parser.add_argument("--solc", default="solc", help="Path to solc binary (default: solc on PATH)")
    parser.add_argument("--base-sequence", default=DEFAULT_OPTIMIZER_SEQUENCE,
                        help="Yul optimizer step sequence to trace occurrences of")
    parser.add_argument("--disable-stack-allocation", action="store_true",
                        help="Force solc's StackCompressor off for isolated per-occurrence probing")
    args = parser.parse_args()

    with open(args.input_json) as f:
        json_input = json.load(f)

    manifest = dump_all_occurrences(json_input, args.output_dir, base_sequence=args.base_sequence,
                                    solc_executable=args.solc,
                                    disable_stack_allocation=args.disable_stack_allocation)
    if not manifest:
        logging.warning("No occurrence compiled successfully; nothing written")

    print(f"Wrote {len(manifest)} occurrence(s) to {args.output_dir}")


if __name__ == "__main__":
    main()
