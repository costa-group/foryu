#!/usr/bin/env python3
"""
Computes constancy (constant-propagation) information for a YUL-CFG-SSA
smart contract -- the yulCFGJson produced by solc, as consumed by bin/foryu --
and writes a new JSON file with a "constancy" key added to every block, so
that bin/foryu --constancy can validate it.

The analysis is a forward dataflow fixpoint that mirrors, instruction by
instruction and edge by edge, the checker's own ground truth as defined in
theories/constancy.v: it is intra-procedural (every function's entry block
starts with no known constants), it constant-folds the same 25
state-independent EVM opcodes theories/evm_dialect.v marks with
opcode_indep_state (arithmetic/bitwise/comparison ops -- anything touching
memory/storage/environment, or a call to another function, always yields
"unknown"), and at a block with several predecessors it keeps only the facts
that agree across every incoming edge (the meet operation over
theories/constancy.v's subset/entailment order).

Usage:
    python3 constancy.py -i input_cfg.json -o output_cfg.json
"""

import argparse
import json
from collections import deque


MODULUS = 1 << 256


# ---------------------------------------------------------------------------
# U256 arithmetic (theories/evm_dialect.v's U256 module), used to constant-fold
# the state-independent opcodes below. Verified against Rocq directly (`Compute
# (Z.div (-7) (-2))`, etc.): Z.div/Z.modulo floor exactly like Python's //  and
# %, for every sign combination, so no adjustment is needed for sdiv/smod.
# ---------------------------------------------------------------------------

def _to_t(z):
    return z % MODULUS


def _signed(v):
    return ((v + (1 << 255)) % MODULUS) - (1 << 255)


def _op_add(a, b): return _to_t(a + b)
def _op_sub(a, b): return _to_t(a - b)
def _op_mul(a, b): return _to_t(a * b)


def _op_div(a, b):
    return 0 if b == 0 else _to_t(a // b)


def _op_sdiv(a, b):
    if b == 0:
        return 0
    return _to_t(_signed(a) // _signed(b))


def _op_mod(a, b):
    return 0 if b == 0 else _to_t(a % b)


def _op_smod(a, b):
    if b == 0:
        return 0
    return _to_t(_signed(a) % _signed(b))


def _op_exp(a, b): return pow(a, b, MODULUS)
def _op_not(a): return _to_t(MODULUS - a - 1)
def _op_lt(a, b): return 1 if a < b else 0
def _op_gt(a, b): return 1 if a > b else 0
def _op_slt(a, b): return 1 if _signed(a) < _signed(b) else 0
def _op_sgt(a, b): return 1 if _signed(a) > _signed(b) else 0
def _op_eq(a, b): return 1 if a == b else 0
def _op_iszero(a): return 1 if a == 0 else 0
def _op_and(a, b): return a & b
def _op_or(a, b): return a | b
def _op_xor(a, b): return a ^ b


def _op_byte(n, x):
    if n >= 32:
        return 0
    return (x // (256 ** (31 - n))) % 256


def _op_shl(shift, value):
    if shift >= 256:
        return 0
    return _to_t(value * (1 << shift))


def _op_shr(shift, value):
    if shift >= 256:
        return 0
    return _to_t(value // (1 << shift))


def _op_sar(shift, value):
    sv = _signed(value)
    if shift >= 256:
        return MODULUS - 1 if sv < 0 else 0
    return _to_t(sv // (1 << shift))


def _op_addmod(a, b, m):
    return 0 if m == 0 else (a + b) % m


def _op_mulmod(a, b, m):
    return 0 if m == 0 else (a * b) % m


def _op_signextend(i, x):
    if i >= 31:
        return x
    size = 8 * (i + 1)
    byte = (x // (1 << (8 * i))) % 256
    sign_bit = byte // 128
    extend = (MODULUS - (1 << size)) if sign_bit == 1 else 0
    return _to_t((x % (1 << size)) + extend)


# theories/evm_dialect.v's opcode_indep_state opcodes, keyed by the lowercase
# JSON opcode name ocaml_interface/main.ml's evm_opcode_list maps them from.
# "clz" is state-independent in the Rocq model too, but has no entry in
# main.ml's evm_opcode_list, so main.ml itself would treat an instruction
# named "clz" as a call to an unrecognized function rather than an opcode --
# excluded here to match that real behavior.
FOLDABLE_OPS = {
    "add": _op_add, "sub": _op_sub, "mul": _op_mul, "div": _op_div,
    "sdiv": _op_sdiv, "mod": _op_mod, "smod": _op_smod, "exp": _op_exp,
    "not": _op_not, "lt": _op_lt, "gt": _op_gt, "slt": _op_slt,
    "sgt": _op_sgt, "eq": _op_eq, "iszero": _op_iszero, "and": _op_and,
    "or": _op_or, "xor": _op_xor, "byte": _op_byte, "shl": _op_shl,
    "shr": _op_shr, "sar": _op_sar, "addmod": _op_addmod,
    "mulmod": _op_mulmod, "signextend": _op_signextend,
}


# ---------------------------------------------------------------------------
# Constancy transfer function (theories/constancy.v's sym_exec_instr)
# ---------------------------------------------------------------------------

def _eval_sexpr(e, pp):
    """Resolves a simple expression: a '0x..' literal resolves to itself, a
    variable resolves via `pp` (None if not known constant there)."""
    if e.startswith("0x"):
        return int(e, 16)
    return pp.get(e)


def sym_exec_instr(instr, pp):
    """One step of theories/constancy.v's sym_exec_instr: the constancy map
    right after `instr`, given the map `pp` right before it."""
    op = instr["op"]
    ins = instr["in"]
    outs = instr["out"]

    new_pp = dict(pp)
    for v in outs:
        new_pp.pop(v, None)

    if op == "LiteralAssignment":
        for v, e in zip(outs, ins):
            val = _eval_sexpr(e, pp)
            if val is not None:
                new_pp[v] = val
    elif op in FOLDABLE_OPS:
        vals = [_eval_sexpr(e, pp) for e in ins]
        if all(v is not None for v in vals):
            result = FOLDABLE_OPS[op](*vals)
            for v in outs:
                new_pp[v] = result
    # Else: an opcode that depends on dialect state, or a call to another
    # function -- nothing can be derived (outputs already dropped above).

    return new_pp


def meet(a, b):
    """Intersection of two constancy maps: keeps only the facts present,
    with the same value, in both -- theories/constancy.v requires a block's
    claimed entry info to be entailed by *every* predecessor's transformed
    exit, so the maximal sound entry is their intersection."""
    if len(b) < len(a):
        a, b = b, a
    return {k: v for k, v in a.items() if b.get(k) == v}


def apply_phi_transform(pred_exit, out_vars, in_exprs):
    """theories/constancy.v's check_const_successor transform: drop
    `out_vars` from `pred_exit` (they're being overwritten by the phi step),
    then add whatever can be derived for them from `in_exprs` (the phi's
    inputs on this specific predecessor edge)."""
    new_pp = dict(pred_exit)
    for v in out_vars:
        new_pp.pop(v, None)
    for v, e in zip(out_vars, in_exprs):
        val = _eval_sexpr(e, pred_exit)
        if val is not None:
            new_pp[v] = val
    return new_pp


# ---------------------------------------------------------------------------
# CFG helpers
# ---------------------------------------------------------------------------

def split_phi(block):
    """Separates a block's PhiFunction instructions from its regular ones
    (matching ocaml_interface/main.ml's split_phi_instr_block)."""
    phi_instrs = []
    real_instrs = []
    for instr in block.get("instructions", []):
        if instr.get("op") == "PhiFunction":
            phi_instrs.append(instr)
        else:
            real_instrs.append(instr)
    return phi_instrs, real_instrs


def successors(block):
    exit_info = block["exit"]
    t = exit_info["type"]
    if t in ("Jump", "ConditionalJump"):
        return list(exit_info["targets"])
    return []  # Terminated, MainExit, FunctionReturn: no successor edge


def transform_for_edge(pred_bid, pred_exit, next_block, next_phi_instrs):
    if not next_phi_instrs:
        return dict(pred_exit)
    entries = next_block.get("entries", [])
    idx = entries.index(pred_bid)
    out_vars = [phi["out"][0] for phi in next_phi_instrs]
    in_exprs = [phi["in"][idx] for phi in next_phi_instrs]
    return apply_phi_transform(pred_exit, out_vars, in_exprs)


# ---------------------------------------------------------------------------
# Per-function fixpoint (theories/constancy.v's check_const_program, run
# forward instead of merely checked)
# ---------------------------------------------------------------------------

def analyze_function(blocks, entry_bid):
    """Runs the constancy fixpoint over one function's blocks. Returns a
    dict block_id -> list of per-program-point constancy maps (one more
    entry than the block has real instructions), ready to become each
    block's 'constancy' JSON key."""
    blocks_by_id = {b["id"]: b for b in blocks}
    phi_by_id = {}
    real_instrs_by_id = {}
    for bid, b in blocks_by_id.items():
        phi, real = split_phi(b)
        phi_by_id[bid] = phi
        real_instrs_by_id[bid] = real

    entry_map = {bid: None for bid in blocks_by_id}
    entry_map[entry_bid] = {}

    pp_lists = {}

    worklist = deque([entry_bid])
    in_worklist = {entry_bid}
    while worklist:
        bid = worklist.popleft()
        in_worklist.discard(bid)

        cur = dict(entry_map[bid])
        pp_list = [dict(cur)]
        for instr in real_instrs_by_id[bid]:
            cur = sym_exec_instr(instr, cur)
            pp_list.append(dict(cur))
        pp_lists[bid] = pp_list

        block = blocks_by_id[bid]
        for succ_bid in successors(block):
            transformed = transform_for_edge(bid, cur, blocks_by_id[succ_bid], phi_by_id[succ_bid])
            if succ_bid == entry_bid:
                continue  # the function entry's info is always {}
            old = entry_map[succ_bid]
            new = transformed if old is None else meet(old, transformed)
            if new != old:
                entry_map[succ_bid] = new
                if succ_bid not in in_worklist:
                    worklist.append(succ_bid)
                    in_worklist.add(succ_bid)

    # Blocks never reached from the entry (dead code): default to the
    # vacuous {} entry -- always sound, matching how a missing "constancy"
    # key is itself treated by ocaml_interface/main.ml's extract_block_constancy.
    for bid in blocks_by_id:
        if bid not in pp_lists:
            cur = {}
            pp_list = [dict(cur)]
            for instr in real_instrs_by_id[bid]:
                cur = sym_exec_instr(instr, cur)
                pp_list.append(dict(cur))
            pp_lists[bid] = pp_list

    return pp_lists


# ---------------------------------------------------------------------------
# Walking the yulCFGJson object tree to discover every function
# ---------------------------------------------------------------------------

def discover_functions(obj):
    """Recursively walks a yul object (with 'blocks'/'functions'/
    'subObjects', matching solc's Yul object nesting), yielding every
    function as (blocks_list, entry_bid): one for the object's own
    top-level 'blocks' (if any; entry = its first block's id, matching
    ocaml_interface/main.ml's process_blocks_entry), and one for every named
    function under 'functions' (using its own explicit 'entry' key)."""
    blocks = obj.get("blocks")
    if blocks:
        yield blocks, blocks[0]["id"]
    for fbody in (obj.get("functions") or {}).values():
        yield fbody["blocks"], fbody["entry"]
    for subname, subobj in (obj.get("subObjects") or {}).items():
        if subname == "type":
            continue
        yield from discover_functions(subobj)


def discover_functions_in_yul_cfg_json(yul_cfg_json):
    """yul_cfg_json: the top-level {'type': ..., '<objname>': {...}, ...}
    map found at contracts/<file>/<contract>/yulCFGJson."""
    for name, obj in yul_cfg_json.items():
        if name == "type":
            continue
        yield from discover_functions(obj)


def annotate_file(data):
    """Adds a 'constancy' key to every block of every function of every
    contract's yulCFGJson found in `data` (the parsed full solc
    standard-json output), mutating `data` in place."""
    contracts = data.get("contracts", {})
    for file_contracts in contracts.values():
        for contract_data in file_contracts.values():
            yul_cfg_json = contract_data.get("yulCFGJson")
            if yul_cfg_json is None:
                continue
            for blocks, entry_bid in discover_functions_in_yul_cfg_json(yul_cfg_json):
                pp_lists = analyze_function(blocks, entry_bid)
                for block in blocks:
                    block["constancy"] = [
                        {v: hex(val) for v, val in pp.items()}
                        for pp in pp_lists[block["id"]]
                    ]


def main():
    parser = argparse.ArgumentParser(
        description="Computes constancy analysis information for a YUL-CFG-SSA JSON file."
    )
    parser.add_argument("-i", "--input", required=True, help="Input yulCFGJson-containing JSON file")
    parser.add_argument("-o", "--output", required=True, help="Output JSON file (input + constancy keys)")
    args = parser.parse_args()

    with open(args.input) as f:
        data = json.load(f)

    annotate_file(data)

    with open(args.output, "w") as f:
        json.dump(data, f, indent=2)


if __name__ == "__main__":
    main()
