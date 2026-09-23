"""
Given two already-compiled yulCFGJson sets for the same contract(s) -- a baseline and a probe
compiled with one extra application of a value-substituting step (see seed_extraction.py's
module docstring for why "T"/"m"/"c"/"s" specifically) -- computes and annotates constancy for
every contract present in both.

This module only compares two already-compiled JSONs; it does not compile anything itself (see
dump_steps.py for that) or decide which step sequence to use (see next_step_constancy.py /
full_constancy_trace.py, which compose the two).
"""
import argparse
import copy
import hashlib
import json
import logging
import time
from typing import Dict, Optional, Tuple

from constancy.annotate import annotate_constancy
from constancy.propagation import compute_constancy_for_cfg
from constancy.seed_extraction import count_leading_phis, extract_seed_facts_for_contract, iter_block_scopes
from global_params.types import Yul_CFG_T
from parser.parser import parse_CFG_from_json_dict


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


def _annotate_with_no_facts(yul_cfg_json: Yul_CFG_T) -> None:
    """
    Injects an all-empty "constancy" field directly from the raw JSON's own instruction counts,
    without parsing or running the propagation pass: with zero seed facts there is nothing to
    propagate (compute_constancy_for_cfg would derive exactly this same all-empty result, just at
    the cost of a full parse), so a contract whose baseline and probe compiled byte-identical can
    skip straight to it. Every block still gets the field -- CLAUDE.md's documented shape -- just
    never a non-empty entry.

    Length must match what the full pipeline would produce (count_leading_phis,
    propagation.compute_block_constancy): len(instructions) - leading_phi_count + 1, not
    unconditionally + 1 -- this is a cheap shortcut for the same contract, not a different one.
    """
    for _, blocks in iter_block_scopes(yul_cfg_json):
        for block in blocks:
            instructions = block.get("instructions", [])
            block["constancy"] = [{} for _ in range(len(instructions) - count_leading_phis(instructions) + 1)]


def annotate_constancy_between(baseline_cfg: Dict[str, Yul_CFG_T], probe_cfg: Dict[str, Yul_CFG_T],
                               stats_out: Optional[Dict[str, float]] = None) -> Tuple[Dict[str, Yul_CFG_T], int]:
    """
    For every contract present in both baseline_cfg and probe_cfg (a contract missing from
    probe_cfg is logged and skipped), extracts seed facts (seed_extraction.
    extract_seed_facts_for_contract), computes per-block constancy (propagation.
    compute_constancy_for_cfg) and injects it into the *baseline* CFG (annotate.
    annotate_constancy) -- the baseline is what's meant to be kept; the probe only exists to
    discover facts.

    Parses a *deep copy* of each baseline CFG before computing constancy, never the object
    itself: parser.parser.parse_block mutates its input's block exit "targets" in place
    (prefixing each with its containing scope name, for the parser's own internal
    representation) -- parsing the real object would leak that prefix into the very JSON this
    function returns as output, decoupling each block's own "id" from the "targets" naming
    other blocks use to refer to it.

    A contract whose baseline and probe compiled to byte-identical JSON is still included in the
    result, and every block still gets a "constancy" field (CLAUDE.md's documented shape) -- but
    via the cheap all-empty shortcut (_annotate_with_no_facts) rather than needlessly re-deriving
    "no facts" for a large CFG through the full parse/extract/propagate pipeline.

    stats_out, when given, gets two keys accumulated across every contract processed:
    "fact_analysis_seconds" (time in extract_seed_facts_for_contract) and "annotation_seconds"
    (time spent parsing, computing, and injecting constancy -- including the byte-identical
    shortcut branch, which produces the same field this would have, just cheaper).

    Returns (annotated baseline per contract, total "missing from probe" warning count across
    every contract compared).
    """
    annotated: Dict[str, Yul_CFG_T] = {}
    restructuring_warning_count = 0

    for contract_name, baseline_yul_cfg in baseline_cfg.items():
        probe_yul_cfg = probe_cfg.get(contract_name)
        if probe_yul_cfg is None:
            logging.warning(f"Contract {contract_name} is missing from the probe compilation; skipping")
            continue

        annotated[contract_name] = baseline_yul_cfg
        if _hash_cfg(baseline_yul_cfg) == _hash_cfg(probe_yul_cfg):
            annotation_start = time.perf_counter()
            _annotate_with_no_facts(baseline_yul_cfg)
            if stats_out is not None:
                stats_out["annotation_seconds"] = stats_out.get("annotation_seconds", 0.0) + \
                    (time.perf_counter() - annotation_start)
            continue

        counter = _MissingWarningCounter()
        logging.getLogger().addHandler(counter)
        fact_analysis_start = time.perf_counter()
        try:
            seed_facts = extract_seed_facts_for_contract(baseline_yul_cfg, probe_yul_cfg)
        finally:
            logging.getLogger().removeHandler(counter)
            if stats_out is not None:
                stats_out["fact_analysis_seconds"] = stats_out.get("fact_analysis_seconds", 0.0) + \
                    (time.perf_counter() - fact_analysis_start)

        annotation_start = time.perf_counter()
        parsed_cfg = parse_CFG_from_json_dict({contract_name: copy.deepcopy(baseline_yul_cfg)})[contract_name]
        constancy_map = compute_constancy_for_cfg(parsed_cfg, seed_facts)
        annotate_constancy(baseline_yul_cfg, constancy_map)
        if stats_out is not None:
            stats_out["annotation_seconds"] = stats_out.get("annotation_seconds", 0.0) + \
                (time.perf_counter() - annotation_start)

        restructuring_warning_count += counter.count

    return annotated, restructuring_warning_count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline_json", help="Path to a {contract: yulCFGJson} JSON file (the baseline)")
    parser.add_argument("probe_json", help="Path to a {contract: yulCFGJson} JSON file (the probe)")
    parser.add_argument("--output", default="constancy_output.json",
                        help="Where to write the annotated baseline yulCFGJson")
    args = parser.parse_args()

    with open(args.baseline_json) as f:
        baseline_cfg = json.load(f)
    with open(args.probe_json) as f:
        probe_cfg = json.load(f)

    annotated, restructuring_warning_count = annotate_constancy_between(baseline_cfg, probe_cfg)

    with open(args.output, "w") as f:
        json.dump(annotated, f, indent=2)

    print(f"Wrote annotated yulCFGJson to {args.output} (restructuring_warning_count="
         f"{restructuring_warning_count})")


if __name__ == "__main__":
    main()
