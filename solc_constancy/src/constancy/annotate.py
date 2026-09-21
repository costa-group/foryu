"""
Top-level driver that ties the constancy analysis together: given a solc standard-json
input, compiles it (src/constancy/seed_extraction.py), computes per-block constancy
(src/constancy/propagation.py), and injects the result back into the baseline yulCFGJson as
a "constancy" field on every block, next to its existing "liveness" and "instructions"
fields -- exactly the JSON shape described in CLAUDE.md.

Usage (run from src/, or with src/ on PYTHONPATH, as the rest of this project expects):
    python3 constancy/annotate.py contract.standard-json.json --output annotated.json
"""
import argparse
import json
import logging
import sys
from typing import Dict, List, Optional, Tuple

from constancy.propagation import compute_constancy_for_cfg, instruction_constancy_T
from constancy.seed_extraction import CONSTANT_PROPAGATING_STEPS, extract_seed_facts, iter_block_scopes, scope_path_T
from execution.sol_compilation import DEFAULT_OPTIMIZER_SEQUENCE
from global_params.types import Yul_CFG_T, block_id_T
from parser.parser import parse_CFG_from_json_dict


def _blocks_by_scope_and_id(yul_cfg_json: Yul_CFG_T) -> Dict[Tuple[scope_path_T, block_id_T], Dict]:
    """
    Indexes every block dict in a contract's raw yulCFGJson by (scope_path, block id), so
    it can be looked up and mutated in place
    """
    return {(scope_path, block["id"]): block
           for scope_path, blocks in iter_block_scopes(yul_cfg_json)
           for block in blocks}


def annotate_constancy(yul_cfg_json: Yul_CFG_T,
                       constancy_map: Dict[Tuple[scope_path_T, block_id_T], List[instruction_constancy_T]]) -> \
        Yul_CFG_T:
    """
    Mutates yul_cfg_json in place, injecting a "constancy" field into every block dict that
    has an entry in constancy_map (next to its existing "liveness" and "instructions"
    fields), and returns it for convenience
    """
    blocks_by_key = _blocks_by_scope_and_id(yul_cfg_json)

    for key, constancy in constancy_map.items():
        block = blocks_by_key.get(key)
        if block is None:
            logging.warning(f"Block {key} not found while annotating constancy; skipping")
            continue
        block["constancy"] = constancy

    return yul_cfg_json


def compute_constancy(json_input: Dict, solc_executable: str = "solc",
                      base_sequence: str = DEFAULT_OPTIMIZER_SEQUENCE,
                      steps_to_consider: List[str] = CONSTANT_PROPAGATING_STEPS,
                      disable_stack_allocation: bool = False) -> Tuple[Optional[Dict[str, Yul_CFG_T]], Optional[Dict[str, Yul_CFG_T]]]:
    """
    Compiles json_input, computes constancy for every contract found, and returns the
    baseline yulCFGJson per contract with "constancy" injected into every block and
    the yulCFGJson used for comparison, but with no annotation. Returns
    None, None if compilation fails.

    disable_stack_allocation defaults to False, preserving this production path's behavior
    (the kept baseline should reflect the contract's actual compiled shape); pass True for
    isolated single-step probing, where forcing solc's StackCompressor off avoids the
    confound documented in seed_extraction.with_stack_allocation_disabled.
    """
    extraction = extract_seed_facts(json_input, solc_executable=solc_executable, base_sequence=base_sequence,
                                    steps_to_consider=steps_to_consider,
                                    disable_stack_allocation=disable_stack_allocation)
    if extraction is None:
        return None, None

    baseline_cfg, probed_cfg, seed_facts_per_contract = extraction

    for contract_name, yul_cfg_json in baseline_cfg.items():
        parsed_cfg = parse_CFG_from_json_dict({contract_name: yul_cfg_json})[contract_name]
        constancy_map = compute_constancy_for_cfg(parsed_cfg, seed_facts_per_contract.get(contract_name, {}))
        annotate_constancy(yul_cfg_json, constancy_map)

    return baseline_cfg, probed_cfg


def annotate_constancy_file(input_json_path: str, output_path: str, solc_executable: str = "solc",
                            base_sequence: str = DEFAULT_OPTIMIZER_SEQUENCE,
                            steps_to_consider: List[str] = CONSTANT_PROPAGATING_STEPS,
                            disable_stack_allocation: bool = False) -> bool:
    """
    Reads a solc standard-json input from input_json_path, computes constancy, and writes
    the annotated yulCFGJson per contract to output_path. Returns whether it succeeded.
    """
    with open(input_json_path) as f:
        json_input = json.load(f)

    result, probed = compute_constancy(json_input, solc_executable=solc_executable, base_sequence=base_sequence,
                                       steps_to_consider=steps_to_consider,
                                       disable_stack_allocation=disable_stack_allocation)
    if result is None:
        return False

    with open(output_path, 'w') as f:
        json.dump(result, f, indent=2)

    # UNCOMMENT TO TEST AGAINST THE PROBE CFG WITH THE NEXT PASS
    probed_path = output_path[:-5] + "probed.json"
    with open(probed_path, 'w') as f:
        json.dump(probed, f, indent=2)

    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input_json", help="Path to a solc standard-json input file")
    parser.add_argument("--solc", default="solc", help="Path to solc binary (default: solc on PATH)")
    parser.add_argument("--output", default="constancy_output.json",
                        help="Where to write the annotated yulCFGJson output")
    parser.add_argument("--base-sequence", default=DEFAULT_OPTIMIZER_SEQUENCE,
                        help="Baseline Yul optimizer step sequence to keep/annotate")
    args = parser.parse_args()

    if not annotate_constancy_file(args.input_json, args.output, solc_executable=args.solc,
                                   base_sequence=args.base_sequence):
        logging.error("Compilation failed; no output written")
        sys.exit(1)

    print(f"Wrote annotated yulCFGJson to {args.output}")


if __name__ == "__main__":
    main()
