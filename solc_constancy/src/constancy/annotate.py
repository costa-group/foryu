"""
Injects a "constancy" field into a baseline yulCFGJson's blocks (next to their existing
"liveness" and "instructions" fields), from a constancy map already computed by
propagation.compute_constancy_for_cfg -- exactly the JSON shape described in CLAUDE.md.

Compiling, comparing two compilations, and deciding which step sequence to use live in
dump_steps.py / compare_constancy.py / next_step_constancy.py / full_constancy_trace.py -- this
module only does the injection itself, so it stays reusable independently of how the
constancy_map was produced.
"""
import logging
from typing import Dict, List, Tuple

from constancy.propagation import instruction_constancy_T
from constancy.seed_extraction import iter_block_scopes, scope_path_T
from global_params.types import Yul_CFG_T, block_id_T


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
