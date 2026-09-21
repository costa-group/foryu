"""
Diagnostic/verification tool: traces every individual occurrence of a small set of Yul
optimizer steps ("T"=LiteralRematerialiser, "m"=Rematerialiser, "c"=CommonSubexpressionEliminator,
"s"=ExpressionSimplifier) through the real DEFAULT_OPTIMIZER_SEQUENCE, treating each occurrence
as its own isolated before/after probe -- reusing modifications.py's truncate_sequence/
find_occurrences technique (ported here rather than imported, since modifications.py
unconditionally requires the unrelated `deepdiff` package at import time).

This is purely additive: it does not change annotate.py's production single-baseline/probe
mechanism or CLAUDE.md's documented contract (still {"T", "m"} only, applied once at the very
end of the sequence). It exists to see *where* (if anywhere) constant propagation actually
happens across the real pipeline, since a single trailing probe on top of an already-optimized
default sequence often finds nothing (see PROGRESS.md).

Each occurrence's before/after pair shares an identical prefix except for the one extra step
character, so seed_extraction.py's structural comparator (which matches instructions by
unifying a baseline<->probe variable correspondence, not by name -- see that module's docstring
for why name-based matching isn't safe even for "T"/"m"/"c", not only "s") only needs this one
before/after pair to make sense, not consistency across occurrences. Per-occurrence snapshots
use their own, mutually incomparable SSA naming (a renaming step sits between many occurrences)
and are never merged across occurrences.

Every emitted snapshot records how many blocks/scopes went unmatched
("restructuring_warning_count") so a consumer can tell a full/safe alignment from a partial,
best-effort one -- this can be nonzero for any of the four steps, not just "s" (see
PROGRESS.md: under the isolation below, some "T" occurrences also restructure block/scope
numbering). This is a block/scope-level signal, not the only line of defense: within a matched
block, seed_extraction.py's own structural matching (not this module) is what protects against
a coincidental collision producing a wrong fact, for any of the four steps, independent of this
count.

Each occurrence's seq_before/seq_after is passed through seed_extraction.isolate_cleanup_sequence,
which appends an explicit, empty cleanup delimiter (":") whenever the truncated prefix doesn't
already contain one. Without this, solc silently runs its own default cleanup sequence
("fDnTOcmuO" -- itself containing "T" and "m") after any colon-less sequence, which for most
occurrences here (everything before DEFAULT_OPTIMIZER_SEQUENCE's own real colon) would
otherwise confound the comparison with steps neither seq_before nor seq_after asked for. This
is a no-op for the few occurrences that fall after the real colon (their prefix already
contains it) -- see PROGRESS.md for the empirical effect size.

Every compile here also goes through seed_extraction.with_stack_allocation_disabled, forcing
off solc's StackCompressor -- a mandatory phase (unrelated to any specific step being probed)
that can duplicate or restructure large amounts of code to resolve "stack too deep" situations,
sensitive to stack-pressure differences a single extra step can introduce. Confirmed on a real
contract: one extra "T" alone shifted a scope's block count from 142 to 92, producing
conflicting-fact warnings that this setting eliminates entirely (see PROGRESS.md). This only
affects this diagnostic tool's own isolated probes, not the production annotate.py path.
"""
import argparse
import copy
import hashlib
import json
import logging
import os
from typing import Any, Dict, List, Optional, TypedDict

from constancy.annotate import annotate_constancy
from constancy.propagation import compute_constancy_for_cfg
from constancy.seed_extraction import (extract_seed_facts_for_contract, isolate_cleanup_sequence,
                                       with_stack_allocation_disabled)
from execution.sol_compilation import DEFAULT_OPTIMIZER_SEQUENCE, SolidityCompilation
from global_params.types import Yul_CFG_T
from parser.parser import parse_CFG_from_json_dict

# Wider than seed_extraction.CONSTANT_PROPAGATING_STEPS (still {"T", "m"}, untouched, used only
# by the production annotate.py path). seed_extraction.py's structural matching guards every
# one of these four against a coincidental collision producing a wrong fact, independent of
# restructuring_warning_count -- but that count itself can be nonzero for any of them once
# sequences are properly isolated (see the module docstring and PROGRESS.md).
PROPAGATION_STEPS_TO_TRACE = ["T", "m", "c", "s"]


class Occurrence(TypedDict):
    step: str
    step_index: int
    index: int
    position: int
    seq_before: str
    seq_after: str


class ContractSnapshot(TypedDict):
    seed_fact_count: int
    restructuring_warning_count: int
    annotated_yul_cfg: Yul_CFG_T


class OccurrenceSnapshot(TypedDict):
    step: str
    step_index: int
    index: int
    position: int
    seq_before: str
    seq_after: str
    restructuring_warning_count: int
    contracts: Yul_CFG_T
    contracts_aft: Yul_CFG_T


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
    silently run its own default cleanup sequence on top of the truncated content (see the
    module docstring).
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


class _MissingWarningCounter(logging.Handler):
    """
    Counts the "missing from probe" warnings seed_extraction.py already logs when a block/scope
    is unmatched between baseline and probe -- used here only to report, per contract, how much
    of the alignment was actually complete (restructuring_warning_count), without changing
    seed_extraction.py itself.
    """

    def __init__(self):
        super().__init__(level=logging.WARNING)
        self.count = 0

    def emit(self, record: logging.LogRecord) -> None:
        self.count += 1


def _hash_cfg(yul_cfg_json: Yul_CFG_T) -> str:
    return hashlib.sha256(json.dumps(yul_cfg_json, sort_keys=True).encode()).hexdigest()


def trace_occurrence(json_input: Dict[str, Any], occurrence: Occurrence,
                     solc_executable: str = "solc") -> Optional[OccurrenceSnapshot]:
    """
    Compiles occurrence's seq_before/seq_after pair and, for every contract whose compiled CFG
    actually changed between the two (a content-hash check, so a no-op contract does no further
    work), computes and annotates its constancy exactly as annotate.py's production path does --
    but keyed off this one occurrence's before/after pair instead of the whole-sequence
    baseline/probe. Returns None if no contract changed at all for this occurrence.
    """
    try:
        prepared_input = with_stack_allocation_disabled(json_input)
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

    contracts: Dict[str, ContractSnapshot] = {}
    contracts_aft: Dict[str, Yul_CFG_T] = {}
    restructuring_warning_count, seed_fact_count = 0, 0

    for contract_name, baseline_yul_cfg in baseline_cfg.items():
        probe_yul_cfg = probe_cfg.get(contract_name)
        if probe_yul_cfg is None:
            logging.warning(f"Contract {contract_name} is missing from the probe compilation for "
                            f"occurrence {occurrence['step']}#{occurrence['step_index']}; skipping")
            continue

        if _hash_cfg(baseline_yul_cfg) == _hash_cfg(probe_yul_cfg):
            continue

        counter = _MissingWarningCounter()
        logging.getLogger().addHandler(counter)
        try:
            seed_facts = extract_seed_facts_for_contract(baseline_yul_cfg, probe_yul_cfg)
        finally:
            logging.getLogger().removeHandler(counter)

        parsed_cfg = parse_CFG_from_json_dict({contract_name: baseline_yul_cfg})[contract_name]
        constancy_map = compute_constancy_for_cfg(parsed_cfg, seed_facts)
        annotate_constancy(baseline_yul_cfg, constancy_map)

        contracts[contract_name] = baseline_yul_cfg
        contracts_aft[contract_name] = probe_yul_cfg

        seed_fact_count += len(seed_facts)
        restructuring_warning_count += counter.count

    if not contracts:
        return None

    return {
        "step": occurrence["step"],
        "step_index": occurrence["step_index"],
        "index": occurrence["index"],
        "position": occurrence["position"],
        "seq_before": occurrence["seq_before"],
        "seq_after": occurrence["seq_after"],
        "restructuring_warning_count": restructuring_warning_count,
        "seed_fact_count": seed_fact_count,
        "contracts": contracts,
        "contracts_aft": contracts_aft,
    }


def trace_all_occurrences(json_input: Dict[str, Any], base_sequence: str = DEFAULT_OPTIMIZER_SEQUENCE,
                          steps_to_consider: List[str] = PROPAGATION_STEPS_TO_TRACE,
                          solc_executable: str = "solc") -> List[OccurrenceSnapshot]:
    """
    Traces every occurrence of steps_to_consider in base_sequence, returning one
    OccurrenceSnapshot per occurrence that actually changed something for at least one contract
    (in chronological/position order); occurrences that changed nothing are skipped entirely.
    """
    snapshots = []
    for occurrence in enumerate_occurrences(base_sequence, steps_to_consider):
        print(occurrence)
        snapshot = trace_occurrence(json_input, occurrence, solc_executable=solc_executable)
        if snapshot is not None:
            snapshots.append(snapshot)
    return snapshots


def write_occurrence_traces(json_input: Dict[str, Any], output_dir: str,
                            base_sequence: str = DEFAULT_OPTIMIZER_SEQUENCE,
                            solc_executable: str = "solc") -> bool:
    """
    Writes one self-contained JSON file per occurrence that changed something, plus a
    manifest.json summarizing every emitted occurrence. Returns whether any occurrence produced
    output.
    """
    os.makedirs(output_dir, exist_ok=True)
    snapshots = trace_all_occurrences(json_input, base_sequence=base_sequence, solc_executable=solc_executable)

    manifest = []
    for snapshot in snapshots:
        file_name = f"occ_{snapshot['index']:03d}_{snapshot['step']}{snapshot['step_index']}.json"
        file_name_aft = f"occ_{snapshot['index']:03d}_{snapshot['step']}{snapshot['step_index']}_aft.json"

        # We only store the contracts field to preserve the Yul representation
        with open(os.path.join(output_dir, file_name), "w") as f:
            json.dump({key: value for key, value in snapshot.items() if key != "contracts_aft"}, f, indent=2)

        # Same shape as file_name, but "contracts" holds the unannotated probe (seq_after)
        # compilation instead of the annotated baseline -- lets two different executions'
        # probe outputs be compared directly.
        snapshot_aft = {key: value for key, value in snapshot.items() if key != "contracts_aft"}
        snapshot_aft["contracts"] = snapshot["contracts_aft"]
        with open(os.path.join(output_dir, file_name_aft), "w") as f:
            json.dump(snapshot_aft, f, indent=2)

        manifest.append({
            "index": snapshot["index"],
            "step": snapshot["step"],
            "step_index": snapshot["step_index"],
            "position": snapshot["position"],
            "seed_fact_count": snapshot["seed_fact_count"],
            "restructuring_warning_count": snapshot["restructuring_warning_count"],
            "contract_names": list(snapshot["contracts"].keys()),
            "file": file_name,
            "file_aft": file_name_aft,
        })

    with open(os.path.join(output_dir, "manifest.json"), "w") as f:
        json.dump(manifest, f, indent=2)

    return bool(snapshots)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_json", help="Path to a solc standard-json input file")
    parser.add_argument("--solc", default="solc", help="Path to solc binary (default: solc on PATH)")
    parser.add_argument("--output-dir", default="occurrence_trace_output",
                        help="Directory to write one JSON file per occurrence plus manifest.json")
    parser.add_argument("--base-sequence", default=DEFAULT_OPTIMIZER_SEQUENCE,
                        help="Yul optimizer step sequence to trace occurrences of")
    args = parser.parse_args()

    with open(args.input_json) as f:
        json_input = json.load(f)

    if not write_occurrence_traces(json_input, args.output_dir, base_sequence=args.base_sequence,
                                   solc_executable=args.solc):
        logging.warning("No occurrence changed anything; no output written besides manifest.json")

    print(f"Wrote occurrence trace to {args.output_dir}")


if __name__ == "__main__":
    main()
