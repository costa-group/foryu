#!/usr/bin/env python3
"""
Computes liveness (live-variable) information for a YUL-CFG-SSA smart
contract -- the yulCFGJson produced by solc, as consumed by bin/foryu -- and
writes a new JSON file with a "liveness" key ({"in": [...], "out": [...]})
on every block, overwriting the one solc emits, so that
bin/foryu --liveness optimal|subset can validate it.

The analysis is a backward dataflow fixpoint over the same equations the
checker in theories/liveness.v validates:

    liveout(b) = {}                                  if b terminates (Terminated/MainExit)
               = vars(returnValues(b))               if b is a FunctionReturn
               = U_{s in succs(b)} inv_phi_s(b, livein(s))   otherwise
    livein(b)  = propbkw(instrs(b), liveout(b) U condvar(b))

where instrs(b) excludes the PhiFunction instructions (they are the edge's
phi-function, handled by inv_phi when crossing into the block, exactly like
ocaml_interface/main.ml's split_phi_instr_block), so livein(b) is the set
right *after* the phi assignments. It is intra-procedural (a call is just an
instruction reading its arguments and writing its results), and it starts
from the empty set everywhere, so the result is the least solution of the
equations: exactly what --liveness optimal requires (VarSet.equal), and
hence also accepted by --liveness subset.

Accepts the same inputs as constancy.py (full `solc --standard-json` output
or a bare yulCFGJson object), and reuses its CFG-walking helpers.

Usage:
    python3 liveness.py -i input_cfg.json -o output_cfg.json
"""

import argparse
import json
import re
from collections import deque

from constancy import _find_yul_cfg_jsons, discover_functions_in_yul_cfg_json, split_phi, successors


# ---------------------------------------------------------------------------
# Liveness transfer functions (theories/liveness.v)
# ---------------------------------------------------------------------------

def _vars(sexprs):
    """theories/liveness.v's extract_yul_vars: the variables among a list of
    simple expressions (anything but a '0x..' literal)."""
    return {e for e in sexprs if not e.startswith("0x")}


def prop_live_set_bkw(instrs, s):
    """theories/liveness.v's prop_live_set_bkw: propagates the live set `s`
    backwards through `instrs`, from the last instruction to the first."""
    s = set(s)
    for instr in reversed(instrs):
        s.difference_update(instr["out"])
        s.update(_vars(instr["in"]))
    return s


def add_jump_var_if_applicable(block, s):
    """theories/liveness.v's add_jump_var_if_applicable: a literal condition
    (possible since solc 0.8.36, e.g. "0x00") makes nothing live."""
    exit_info = block["exit"]
    if exit_info["type"] == "ConditionalJump":
        return s | _vars([exit_info["cond"]])
    return s


def apply_inv_phi(pred_bid, next_block, next_phi_instrs, next_live_in):
    """theories/liveness.v's apply_inv_phi for the edge pred_bid -> next_block:
    drops the phi outputs from the successor's live-in and adds the variables
    the phi reads on this specific edge. A predecessor not listed in
    "entries" gets no phi inputs, like main.ml's gen_phi_function'."""
    out_vars = {phi["out"][0] for phi in next_phi_instrs}
    entries = next_block.get("entries", [])
    if next_phi_instrs and pred_bid in entries:
        idx = entries.index(pred_bid)
        in_vars = _vars(phi["in"][idx] for phi in next_phi_instrs)
    else:
        in_vars = set()
    return (next_live_in - out_vars) | in_vars


# ---------------------------------------------------------------------------
# Per-function fixpoint (theories/liveness.v's check_program, run backward
# instead of merely checked)
# ---------------------------------------------------------------------------

def analyze_function(blocks):
    """Runs the liveness fixpoint over one function's blocks. Returns a dict
    block_id -> (live_in, live_out), as Python sets of variable names."""
    blocks_by_id = {b["id"]: b for b in blocks}
    phi_by_id = {}
    real_instrs_by_id = {}
    for bid, b in blocks_by_id.items():
        phi, real = split_phi(b)
        phi_by_id[bid] = phi
        real_instrs_by_id[bid] = real

    preds = {bid: set() for bid in blocks_by_id}
    for bid, b in blocks_by_id.items():
        for succ_bid in successors(b):
            preds[succ_bid].add(bid)

    live_in = {bid: set() for bid in blocks_by_id}
    live_out = {bid: set() for bid in blocks_by_id}

    # Reverse block order tends to visit successors first, which speeds up
    # convergence of a backward analysis; any order reaches the same fixpoint.
    worklist = deque(reversed(list(blocks_by_id)))
    in_worklist = set(worklist)
    while worklist:
        bid = worklist.popleft()
        in_worklist.discard(bid)
        block = blocks_by_id[bid]

        exit_info = block["exit"]
        t = exit_info["type"]
        if t == "FunctionReturn":
            out = _vars(exit_info["returnValues"])
        elif t in ("Jump", "ConditionalJump"):
            out = set()
            for succ_bid in successors(block):
                out |= apply_inv_phi(bid, blocks_by_id[succ_bid], phi_by_id[succ_bid], live_in[succ_bid])
        else:
            out = set()  # Terminated, MainExit: ExitInfo.Terminate in main.ml
        live_out[bid] = out

        new_in = prop_live_set_bkw(real_instrs_by_id[bid], add_jump_var_if_applicable(block, out))
        if new_in != live_in[bid]:
            live_in[bid] = new_in
            for pred_bid in preds[bid]:
                if pred_bid not in in_worklist:
                    worklist.append(pred_bid)
                    in_worklist.add(pred_bid)

    return {bid: (live_in[bid], live_out[bid]) for bid in blocks_by_id}


# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------

def _var_sort_key(v):
    """Orders variables like solc does: phiN before vN, numerically."""
    m = re.fullmatch(r"([A-Za-z_]+)(\d+)", v)
    if m is None:
        return (2, 0, v)
    prefix, num = m.groups()
    return (0 if prefix == "phi" else 1, int(num), v)


def annotate_file(data):
    """Sets the 'liveness' key of every block of every function of every
    yulCFGJson found in `data` (see constancy.py's `_find_yul_cfg_jsons`),
    mutating `data` in place."""
    for yul_cfg_json in _find_yul_cfg_jsons(data):
        for blocks, _entry_bid in discover_functions_in_yul_cfg_json(yul_cfg_json):
            info = analyze_function(blocks)
            for block in blocks:
                live_in, live_out = info[block["id"]]
                block["liveness"] = {
                    "in": sorted(live_in, key=_var_sort_key),
                    "out": sorted(live_out, key=_var_sort_key),
                }


def main():
    parser = argparse.ArgumentParser(
        description="Computes liveness analysis information for a YUL-CFG-SSA JSON file."
    )
    parser.add_argument("-i", "--input", required=True, help="Input yulCFGJson-containing JSON file")
    parser.add_argument("-o", "--output", required=True, help="Output JSON file (input + liveness keys)")
    args = parser.parse_args()

    with open(args.input) as f:
        data = json.load(f)

    annotate_file(data)

    with open(args.output, "w") as f:
        json.dump(data, f, indent=2)


if __name__ == "__main__":
    main()
