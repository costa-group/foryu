"""
Pins the yulCFGJson argument-order conventions this project relies on against a real solc (0.8.36
or later), so a mistaken convention (or a solc change) fails loudly instead of silently producing
wrong facts:

- raw "in" lists of ordinary instructions are in textual Yul order (sub(a, b) is stored [a, b]; solc
  0.8.34 stored them reversed) -- relied on by evm_arithmetic.evaluate and
  seed_extraction._unused_arg_positions;
- a ConditionalJump goes to targets[0] when its condition is 0 and to targets[1] otherwise --
  relied on by seed_extraction._fold_conditional_exit;
- a PhiFunction's "in" is *not* reversed: in[i] is the value coming from entries[i] -- relied on by
  _reorder_phi_args / _resolve_phi_value and (through the parser, which also leaves phi arguments
  unreversed) propagation's phi rule.

Every operand is a distinct calldataload, so each argument slot can be traced to its source.
"""
import glob
import json
import os
import re
import shutil
import subprocess

import pytest

from constancy.evm_arithmetic import evaluate
from constancy.seed_extraction import _fold_conditional_exit, _ZERO_SIZE_UNUSED_ARGS
from parser.cfg_instruction import CFGInstruction

_SOURCE = """
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;
contract ArgOrder {
    fallback() external {
        assembly {
            let a := calldataload(0)
            let b := calldataload(32)
            let c := calldataload(64)
            sstore(1, sub(a, b)) sstore(2, div(a, b)) sstore(3, sdiv(a, b)) sstore(4, mod(a, b))
            sstore(5, smod(a, b)) sstore(6, exp(a, b)) sstore(7, lt(a, b)) sstore(8, gt(a, b))
            sstore(9, slt(a, b)) sstore(10, sgt(a, b)) sstore(11, shl(a, b)) sstore(12, shr(a, b))
            sstore(13, sar(a, b)) sstore(14, byte(a, b)) sstore(15, signextend(a, b))
            sstore(16, addmod(a, b, c)) sstore(17, mulmod(a, b, c))
            return(a, b)
            if lt(a, b) { sstore(100, 1) }
            let x := a
            if gt(a, c) { x := b }
            sstore(200, x)
        }
    }
}
"""
# return(a, b) above would make what follows unreachable; it is placed in its own copy instead
_SOURCE_NO_RETURN = _SOURCE.replace("            return(a, b)\n", "")

_ASYMMETRIC = ["sub", "div", "sdiv", "mod", "smod", "exp", "lt", "gt", "slt", "sgt", "shl", "shr", "sar",
               "byte", "signextend"]


def _working_solc():
    # the first solc 0.8.36+ found (SOLC, PATH, the usual install locations, solc-select's artifacts)
    candidates = [os.environ.get("SOLC"), shutil.which("solc"), os.path.expanduser("~/.local/bin/solc"),
                  "/usr/local/bin/solc", "/usr/bin/solc"] + \
        sorted(glob.glob(os.path.expanduser("~/.solc-select/artifacts/solc-*/solc-*")), reverse=True)
    for candidate in candidates:
        if not candidate or not os.path.isfile(candidate) or os.path.getsize(candidate) == 0:
            continue
        try:
            version = subprocess.run([candidate, "--version"], capture_output=True, text=True, timeout=20).stdout
        except (OSError, subprocess.TimeoutExpired):
            continue
        match = re.search(r"Version: (\d+)\.(\d+)\.(\d+)", version)
        if match and tuple(map(int, match.groups())) >= (0, 8, 36):
            return candidate
    return None


_SOLC = _working_solc()
pytestmark = pytest.mark.skipif(_SOLC is None, reason="no working solc 0.8.36+ binary found")


def _compile_scope(source):
    inp = {"language": "Solidity", "sources": {"probe.sol": {"content": source}},
           "settings": {"experimental": True, "optimizer": {"enabled": True, "details": {"yulDetails": {"optimizerSteps": ":"}}},
                        "outputSelection": {"*": {"*": ["yulCFGJson"]}}}}
    out = json.loads(subprocess.run([_SOLC, "--standard-json"], input=json.dumps(inp),
                                    capture_output=True, text=True, timeout=120).stdout)
    errors = [e for e in out.get("errors", []) if e["severity"] == "error"]
    assert not errors, errors
    scopes = []

    def walk(comp):
        if comp.get("blocks"):
            scopes.append(comp["blocks"])
        for f in comp.get("functions", {}).values():
            walk(f)
        for s in comp.get("subObjects", {}).values():
            if isinstance(s, dict):
                walk(s)

    for comp in out["contracts"]["probe.sol"]["ArgOrder"]["yulCFGJson"].values():
        if isinstance(comp, dict):
            walk(comp)
    # the fallback body: the only scope reading calldataload three times
    blocks = next(bs for bs in scopes
                  if sum(i["op"] == "calldataload" for b in bs for i in b["instructions"]) >= 3)
    defs = {o: i for b in blocks for i in b["instructions"] for o in i.get("out", [])}

    def literal(var):
        if var.startswith("0x"):
            return var
        ins = defs.get(var)
        return ins["in"][0] if ins and ins["op"] == "LiteralAssignment" else None

    names = {var: {"0x00": "a", "0x20": "b", "0x40": "c"}[literal(ins["in"][0])]
             for var, ins in defs.items()
             if ins["op"] == "calldataload" and literal(ins["in"][0]) in ("0x00", "0x20", "0x40")}
    return blocks, defs, names


@pytest.fixture(scope="module")
def body():
    return _compile_scope(_SOURCE_NO_RETURN)


@pytest.fixture(scope="module")
def body_with_return():
    return _compile_scope(_SOURCE)


def _raw_args(blocks, names, op):
    for b in blocks:
        for ins in b["instructions"]:
            labels = [names.get(arg, arg) for arg in ins["in"]]
            if ins["op"] == op and set(labels) <= {"a", "b", "c"}:
                return labels
    raise AssertionError(f"{op} not found")


@pytest.mark.parametrize("op", _ASYMMETRIC)
def test_two_operand_ops_store_their_arguments_in_textual_order(body, op):
    blocks, _, names = body
    assert _raw_args(blocks, names, op) == ["a", "b"]


@pytest.mark.parametrize("op", ["addmod", "mulmod"])
def test_three_operand_ops_store_their_arguments_in_textual_order(body, op):
    blocks, _, names = body
    assert _raw_args(blocks, names, op) == ["a", "b", "c"]


def test_memory_region_ops_store_their_arguments_in_textual_order(body_with_return):
    # textual return(a, b) = return(offset=a, size=b): raw [offset, size], the indices
    # _ZERO_SIZE_UNUSED_ARGS uses directly
    blocks, _, names = body_with_return
    assert _raw_args(blocks, names, "return") == ["a", "b"]
    assert _ZERO_SIZE_UNUSED_ARGS["return"] == [(1, [0])]


def test_evaluate_reads_raw_operands_in_the_same_textual_order():
    # sub(0x10, 0x01) = 0x0f; shl(0xa0, 0x01) = 1 << 160
    assert evaluate("sub", ["0x10", "0x01"]) == "0x0f"
    assert evaluate("shl", ["0xa0", "0x01"]) == "0x01" + "00" * 20
    assert evaluate("lt", ["0x01", "0x10"]) == "0x01"


def test_a_branch_goes_to_targets_1_when_its_condition_is_nonzero(body):
    blocks, defs, names = body
    by_id = {b["id"]: b for b in blocks}
    jump = next(b for b in blocks if b.get("exit", {}).get("type") == "ConditionalJump"
                and defs[b["exit"]["cond"]]["op"] == "lt")
    zero_target, nonzero_target = jump["exit"]["targets"]
    body_store = ["0x64", "0x01"]  # sstore(100, 1)
    assert any(i["op"] == "sstore" and i["in"] == body_store for i in by_id[nonzero_target]["instructions"])
    assert not any(i["op"] == "sstore" and i["in"] == body_store for i in by_id[zero_target]["instructions"])
    assert _fold_conditional_exit(jump, {jump["exit"]["cond"]: "0x00"})["targets"] == [zero_target]
    assert _fold_conditional_exit(jump, {jump["exit"]["cond"]: "0x01"})["targets"] == [nonzero_target]


def test_a_phi_takes_in_i_from_entries_i_and_the_parser_keeps_that_order(body):
    # x is a on the fall-through edge (the gt branch's zero target) and b through the body
    blocks, defs, names = body
    by_id = {b["id"]: b for b in blocks}
    merge = next(b for b in blocks if any(i["op"] == "PhiFunction" for i in b["instructions"]))
    phi = next(i for i in merge["instructions"] if i["op"] == "PhiFunction")
    branch = next(b for b in blocks if b.get("exit", {}).get("type") == "ConditionalJump"
                  and defs[b["exit"]["cond"]]["op"] == "gt")
    from_value = dict(zip(merge["entries"], (names.get(v, v) for v in phi["in"])))
    assert from_value[branch["id"]] == "a"  # the edge where the body was skipped
    body_block = branch["exit"]["targets"][1]
    assert from_value[body_block] == "b"
    assert by_id[body_block]["exit"]["targets"] == [merge["id"]]
    parsed = CFGInstruction(phi["op"], phi["in"], phi["out"])
    assert parsed.get_in_args() == phi["in"]


def test_a_literal_branch_condition_is_folded():
    # since solc 0.8.35, literals are inlined, so a condition can be a literal itself
    jump = {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "0x01", "targets": ["B1", "B2"]}}
    assert _fold_conditional_exit(jump, {})["targets"] == ["B2"]
    jump["exit"]["cond"] = "0x00"
    assert _fold_conditional_exit(jump, {})["targets"] == ["B1"]


def test_a_memoryguard_without_literal_args_is_kept_as_is():
    # solc 0.8.36+ emits {"in": [], "op": "memoryguard", "out": ["v0"]} with no literalArgs
    instr = CFGInstruction("memoryguard", [], ["v0"])
    instr.translate_opcode({}, 0, "C", {})
    assert instr.get_op_name() == "memoryguard"
