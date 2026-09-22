"""
Extracts "seed" constancy facts by comparing two compilations of the same contract: one
with a baseline Yul optimizer step sequence, and one with that same sequence plus one extra
application of a step (see libyul/optimiser/Suite.cpp) that can substitute a variable's
already-known value into its use sites -- LiteralRematerialiser ('T'), Rematerialiser ('m'),
CommonSubexpressionEliminator ('c'), or ExpressionSimplifier ('s'), used this way both by
next_step_constancy.py's production path and by full_constancy_trace.py's wider per-occurrence
trace.
Wherever a variable that is still symbolic in the baseline shows up as a plain literal at the
same argument position in the probe compilation, that variable is known to have that constant
value.

Matching instructions between the two compilations by output-variable NAME alone is not safe,
and neither is matching by fixed position: any step can shift solc's sequential variable
numbering, or reorder/regroup instructions, well beyond the one thing actually being probed.
`match_block_instructions` instead partitions each block's instructions by *movability* --
solc's own documented optimizer concept (https://docs.soliditylang.org/en/latest/internals/
optimizer.html, libyul/SideEffects.h): an instruction is movable if it's side-effect free and
depends only on variable values and call-constant environment state (pure arithmetic/logic,
reads of things like CALLER/TIMESTAMP/CALLDATALOAD that can't change during a call). Everything
else -- side-effecting opcodes, anything touching memory/storage/transient storage (reads
included: MLOAD/SLOAD/TLOAD), PC/msize/returndatasize-dependent ops, and (per solc's own default)
every call to a generated Yul function -- is non-movable: an "anchor" whose relative order with
respect to other anchors solc's optimizer cannot have changed. Since almost every instruction in
real yulCFGJson data is a call to a generated function rather than a raw EVM opcode, `_MOVABLE_OPS`
is deliberately an allowlist of known-pure primitives; anything not on it defaults to non-movable
-- conservative in the safe direction (it only costs coverage, since an anchor still gets matched,
just without exploiting reordering flexibility it might have actually had).

Anchors are matched order-preservingly (`_match_anchors`): their sequence can't have been
reordered, so a same-shape pairing found out of order is a coincidence, not a correspondence, and
is dropped in favor of the longest order-consistent subset -- a real branch/structural difference
still leaves some anchors unresolved rather than guessed. Movable instructions are matched as one
global pool across the *whole* block (`_match_item_set`), not bracketed between adjacent anchors:
solc is free to reorder a movable instruction across any anchor it has no data or side-effect
dependency on, confirmed directly against a real contract (a pure address-mask computation moved
from before an `SLOAD` to after it, since it doesn't touch storage). Both passes use the same
iterative constraint-propagation primitive: repeatedly commit any instruction with exactly one
remaining structurally-compatible candidate (checking both operand orderings for a commutative op
-- `_COMMUTATIVE_OPS` -- since solc is free to reorder those too), which may newly disambiguate
others via the variable correspondence it confirms; repeat until nothing more resolves. A
periodic/repetitive pattern that looks locally ambiguous (e.g. three structurally-identical
`shl`/`sub` pairs building an address mask) resolves this way once *any* one instruction in the
block has a uniquely-identifiable operand (traced on a real contract: a downstream `and(x, v28)`
where `v28` is already known from outside the block pins one link, which then resolves the rest
by elimination) -- no positional offset-window guessing is needed anywhere.

Known, accepted limitation: solc can also *reassociate* a chain of a commutative+associative op
(e.g. regroup `(0x20+a)+b` into `(b+a)+0x20`), which no per-instruction check can match, since the
intermediate value on one side has no counterpart instruction on the other at all. Confirmed on a
real contract this costs nothing in practice for constancy purposes -- the reassociated region was
itself computing a purely runtime (calldata-dependent) value with no constant to find either way --
and the design correctly declines to force a match there rather than guessing one. Full algebraic-
equivalence checking (flattening associative chains, comparing as multisets) is out of scope.

`extract_seed_facts_for_contract` runs this per scope in dominance-order (mirroring
`parser.cfg_block_list.CFGBlockList.dominant_tree`, built directly off the raw yulCFGJson
block list via the same `graphs.algorithms.compute_dominance_tree`), seeding each block's
matcher with the variable correspondences its already-processed predecessors confirmed. This
is not just extra coverage: if a block's own local match ever produced a correspondence that
contradicts what a dominating predecessor already confirmed for the same variable, the seed
makes that a hard conflict (rejected, not silently trusted) instead of two independently-lucky
per-block answers going unchecked against each other -- exactly the gap that let the
'T'-occurrence contradiction above slip through undetected before this fix.

Matching blocks themselves is not safe by raw id alone either, for the same underlying reason:
`extract_seed_facts_for_contract` establishes a baseline<->probe block correspondence from the
scope's shared entry block, propagated via matching CFG-edge shape (exit type + successor
count, and -- for a ConditionalJump -- the condition variable's own defining instruction, not
just the branch arity) rather than assuming equal ids name the same block. Block-correspondence
resolution and instruction matching are interleaved into one dominance-order walk per scope
(`_match_scope`), not two separate passes: a block's own confirmed `var_map` needs to be ready
*before* its successors' branch conditions are checked against it, and before any `PhiFunction`
in a successor can be aligned by predecessor identity (`_reorder_phi_args`, using the raw
`entries` field solc emits alongside a block's `PhiFunction`s -- one entry per phi input
position, naming the predecessor block that produced it -- rather than trusting `PhiFunction`
`in` lists to line up positionally between baseline and probe, which nothing guarantees). The
branch-condition check itself also recognizes a negated condition (solc wrapping/unwrapping an
`iszero` and swapping the two branch targets accordingly), not just a literal match.

This catches genuinely ambiguous cases, but it cannot catch every one -- a real, previously-
investigated case (see PROGRESS.md) turned out to be caused by solc's `StackCompressor` -- a
mandatory phase, unrelated to any step this module is asked to probe, that can duplicate or
restructure large amounts of code to resolve "stack too deep" situations, sensitive to stack-
pressure differences one extra step can introduce. Since the resulting block-count shift can
happen inside an otherwise-uniform, single-predecessor chain, it produces no observable ambiguity
for any purely local block matcher (id-based or structural) to catch --
`with_stack_allocation_disabled` (below) is the actual fix for that class, used by isolated
probing callers (`dump_steps.py`'s `dump_occurrence`/`dump_all_occurrences`, and
`next_step_constancy.py`'s `--disable-stack-allocation` flag).

A block whose `ConditionalJump` branches on a variable that's provably a compile-time literal
(a `LiteralAssignment`, possibly several blocks up) can get eliminated outright by solc's block-
joiner once an extra constant-propagating step makes that provable, leaving no counterpart block
in probe at all -- traced directly on a real contract (`NFTMarketWrap`, occurrence `T3`, scope
`abi_encode_array_address`). Block-correspondence resolution alone can't see through this (the
eliminated block's other route in is typically a loop back-edge, unavailable in this single-
forward-pass design either way), so `extract_seed_facts_for_contract` normalizes a *copy* of each
scope's blocks before matching (`_merge_trivial_blocks`): fold a `ConditionalJump` whose condition
resolves to a known literal (`_literal_value_table`, a forward dominance-order walk tracking
direct `LiteralAssignment`s only -- deliberately not a general constant-folding engine) into an
unconditional `Jump`, then repeatedly absorb a block into its sole remaining effective predecessor
wherever that's now a trivial 1-in/1-out edge -- never a block that still carries a `PhiFunction`,
even if one of its *other* raw incoming edges happens to fold away elsewhere, since that would
leave a stale, still-ambiguous phi inside a block now pretending to have only one route in. Each
working block tracks which original block/instruction each of its own instructions came from, so
every fact `_match_scope` finds is translated back to the real, unmerged baseline's addressing
before being returned -- the annotated CFG itself is never touched, only how facts are discovered
about it (mirrors `with_stack_allocation_disabled`'s own baseline/discovery split, just at the
block-matching layer instead of the compile layer). This only folds a *directly*-literal
condition; it does not, and isn't meant to, catch a branch that becomes dead for a genuinely
different reason -- e.g. comparing two structurally-identical subexpressions
(`eq(calldataload(x), calldataload(x))`, always true regardless of `x`'s actual runtime value) is
CommonSubexpressionEliminator/ExpressionSimplifier's own value-numbering judgment, not a constant
one, and replicating it here would mean re-deriving a piece of solc's own optimizer logic rather
than comparing its output -- confirmed as the dominant cause of `ExpressionSimplifier`'s much
larger, *unaddressed* block-count collapses (one real function goes from 39 blocks to 1: 18 of 19
branches are exactly this shape, only 1 is a foldable literal comparison).
"""
import copy
import logging
from collections import defaultdict
from typing import Any, Dict, List, Optional, Tuple

import networkx as nx

from execution.sol_compilation import get_yul_details
from global_params.types import block_id_T, component_name_T, constant_T, var_id_T, Yul_CFG_T
from graphs.algorithms import compute_dominance_tree

# Steps that propagate a variable's constant value (see libyul/optimiser/Suite.cpp)
CONSTANT_PROPAGATING_STEPS = ["T", "m"]

# Path identifying a scope that owns a list of blocks: the object name, followed by the
# function name for each level of function nesting (empty tuple element for the object's
# own blocks)
scope_path_T = Tuple[component_name_T, ...]

# A seed fact is identified by the scope it belongs to, the block id, the index of the
# instruction in the baseline block's instruction list, and the variable name
seed_key_T = Tuple[scope_path_T, block_id_T, int, var_id_T]
seed_facts_T = Dict[seed_key_T, constant_T]

# A baseline<->probe variable correspondence confirmed while matching one block, threaded to
# its successors as a seed
var_map_T = Dict[var_id_T, var_id_T]

# Commutative ops: both operand orderings are checked when testing structural compatibility,
# since solc's optimizer is free to reorder these (see the module docstring)
_COMMUTATIVE_OPS = {"add", "mul", "and", "or", "xor", "eq"}

# Allowlist of primitive ops solc's optimizer treats as movable (see the module docstring and
# https://docs.soliditylang.org/en/latest/internals/optimizer.html / libyul/SideEffects.h):
# side-effect free, and depends only on variable values and call-constant environment state.
# Deliberately an allowlist, not a blocklist -- every call to a generated Yul function (the
# majority of instructions in real yulCFGJson data) is non-movable by solc's own default, and
# treating an unrecognized op as non-movable (an anchor) is always the safe direction: it only
# costs coverage, never correctness.
_MOVABLE_OPS = {
    "add", "sub", "mul", "div", "sdiv", "mod", "smod", "exp", "addmod", "mulmod",
    "signextend", "lt", "gt", "slt", "sgt", "eq", "iszero", "and", "or", "xor", "not",
    "shl", "shr", "sar", "byte",
    "address", "origin", "caller", "callvalue", "calldataload", "calldatasize",
    "gasprice", "coinbase", "timestamp", "number", "difficulty", "prevrandao",
    "gaslimit", "chainid", "basefee", "blobbasefee", "codesize", "blobhash",
    "LiteralAssignment", "memoryguard", "datasize", "dataoffset",
}


def is_literal(value: str) -> bool:
    return value.startswith("0x")


def _try_unify_instructions(baseline_instr: Dict[str, Any], probe_instr: Dict[str, Any],
                            var_map: var_map_T) -> Optional[Tuple[List[Tuple[var_id_T, var_id_T]], Dict[var_id_T, constant_T]]]:
    """
    Checks whether baseline_instr and probe_instr can be the "same" instruction (the same one,
    before and after a value-substituting step), given the variable correspondences already
    confirmed in var_map. Every argument position must be explained by one of: the same
    literal on both sides; an already-confirmed (or newly proposed) baseline->probe variable
    correspondence; or a baseline variable that became a literal in the probe (the actual
    substitution this whole analysis looks for). Any other kind of difference -- two different
    symbolic names, two different literals, or a literal turning symbolic -- means these are
    not really the same instruction, just two that happen to look alike after a shift.

    Returns (new_unifications, substitution_facts) if consistent, None otherwise. Does not
    mutate var_map -- the caller commits new_unifications only once the whole match is accepted.
    """
    baseline_out, probe_out = baseline_instr.get("out", []), probe_instr.get("out", [])
    baseline_in, probe_in = baseline_instr.get("in", []), probe_instr.get("in", [])

    if baseline_instr.get("op") != probe_instr.get("op") or len(baseline_out) != len(probe_out) \
            or len(baseline_in) != len(probe_in):
        return None

    pending: List[Tuple[var_id_T, var_id_T]] = []

    for baseline_var, probe_var in zip(baseline_out, probe_out):
        if baseline_var in var_map and var_map[baseline_var] != probe_var:
            return None
        pending.append((baseline_var, probe_var))

    facts: Dict[var_id_T, constant_T] = {}
    for baseline_arg, probe_arg in zip(baseline_in, probe_in):
        baseline_literal, probe_literal = is_literal(baseline_arg), is_literal(probe_arg)
        if baseline_literal and probe_literal:
            if baseline_arg != probe_arg:
                return None
        elif baseline_literal and not probe_literal:
            return None
        elif not baseline_literal and probe_literal:
            facts[baseline_arg] = probe_arg
        else:
            if baseline_arg in var_map and var_map[baseline_arg] != probe_arg:
                return None
            pending.append((baseline_arg, probe_arg))

    return pending, facts


def _instruction_correspondences(baseline_instr: Dict[str, Any], probe_instr: Dict[str, Any], var_map: var_map_T) -> \
        List[Tuple[List[Tuple[var_id_T, var_id_T]], Dict[var_id_T, constant_T]]]:
    """
    The way baseline_instr could correspond to probe_instr given var_map, as a 0- or 1-element
    list. Tries the natural (positional) argument order first (_try_unify_instructions); only if
    that fails, and the op is commutative (_COMMUTATIVE_OPS) with two distinct operands, falls
    back to the swapped order -- solc's optimizer is free to reorder a commutative op's
    operands, but preferring the natural order first avoids treating an already-unambiguous
    instruction as newly ambiguous just because a swap would also happen to parse (e.g.
    add(v2, v0) against add(v2, 0x20): the positional reading is already a clean, unique match;
    checking the swap too would spuriously claim v2 = 0x20 as an equally-valid alternative).

    The swapped order is only offered when none of baseline_instr's own arguments are already
    known in var_map. Otherwise the swap can be used to silently route around a real
    contradiction rather than genuinely explain a reordering: if var_map already says a
    baseline argument corresponds to a specific probe variable, and the natural order conflicts
    with that, swapping operands just to avoid the conflict would fabricate a correspondence
    for the *other* argument instead of correctly rejecting the whole instruction (confirmed
    against a real collision case -- see the module docstring's periodic-block example).
    """
    result = _try_unify_instructions(baseline_instr, probe_instr, var_map)
    if result is not None:
        return [result]

    probe_in = probe_instr.get("in", [])
    baseline_in = baseline_instr.get("in", [])
    already_known = any(arg in var_map for arg in baseline_in if not is_literal(arg))
    if not already_known and probe_instr.get("op") in _COMMUTATIVE_OPS and len(probe_in) == 2 \
            and probe_in[0] != probe_in[1]:
        swapped = {**probe_instr, "in": [probe_in[1], probe_in[0]]}
        result = _try_unify_instructions(baseline_instr, swapped, var_map)
        if result is not None:
            return [result]

    return []


def _is_movable(instr: Dict[str, Any]) -> bool:
    """See _MOVABLE_OPS and the module docstring."""
    return instr.get("op") in _MOVABLE_OPS


def _match_item_set(baseline_items: List[Tuple[int, Dict[str, Any]]], probe_items: List[Tuple[int, Dict[str, Any]]],
                    var_map: var_map_T) -> Tuple[Dict[int, Dict[var_id_T, constant_T]], var_map_T, Dict[int, int]]:
    """
    Structurally matches baseline_items against probe_items (each a list of
    (original_instruction_index, instruction) pairs) independent of position, via iterative
    constraint propagation: repeatedly commit any baseline instruction with exactly one
    remaining structurally-compatible probe candidate (_instruction_correspondences, which
    accounts for commutative operand order), which may newly disambiguate others by adding to
    var_map; repeat until no further commits happen. Two baseline instructions that both
    uniquely want the same probe instruction in the same round are a genuine tie -- neither is
    committed, mirroring "unique candidate or nothing" everywhere else in this module.

    Mutates and returns var_map. Returns (facts keyed by baseline index, var_map, pairing --
    {baseline_index: probe_index} for every committed correspondence, used by _match_anchors to
    check order).
    """
    facts: Dict[int, Dict[var_id_T, constant_T]] = defaultdict(dict)
    pairing: Dict[int, int] = {}
    remaining_baseline = dict(baseline_items)
    remaining_probe = dict(probe_items)

    while remaining_baseline and remaining_probe:
        proposals: Dict[int, List[Tuple[int, List[Tuple[var_id_T, var_id_T]], Dict[var_id_T, constant_T]]]] = \
            defaultdict(list)
        for b_idx, b_instr in remaining_baseline.items():
            matches = [(p_idx, pending, step_facts)
                      for p_idx, p_instr in remaining_probe.items()
                      for pending, step_facts in _instruction_correspondences(b_instr, p_instr, var_map)]
            if len(matches) == 1:
                p_idx, pending, step_facts = matches[0]
                proposals[p_idx].append((b_idx, pending, step_facts))

        commits = [(p_idx, props[0]) for p_idx, props in proposals.items() if len(props) == 1]
        if not commits:
            break

        for p_idx, (b_idx, pending, step_facts) in commits:
            for baseline_var, probe_var in pending:
                var_map[baseline_var] = probe_var
            if step_facts:
                facts[b_idx].update(step_facts)
            pairing[b_idx] = p_idx
            del remaining_baseline[b_idx]
            del remaining_probe[p_idx]

    return dict(facts), var_map, pairing


def _match_anchors(baseline_anchors: List[Tuple[int, Dict[str, Any]]], probe_anchors: List[Tuple[int, Dict[str, Any]]],
                   var_map: var_map_T) -> Tuple[Dict[int, Dict[var_id_T, constant_T]], var_map_T]:
    """
    Matches a block's anchors (non-movable instructions -- see _is_movable) against the probe's.
    Anchors additionally can't have been reordered relative to each other (that is what makes
    them anchors), so order is enforced as an active constraint during the same iterative
    propagation _match_item_set uses for movable instructions, not as a filter applied
    afterward: each not-yet-committed baseline anchor is restricted to a [lo, hi] window of
    probe positions, and committing any anchor narrows every other anchor's window (nothing
    before it can match at or after its probe position, nothing after it can match at or
    before). This lets an anchor with a locally-distinctive match (e.g. a literal argument no
    other candidate shares) resolve first and then pin down neighboring anchors that would
    otherwise be ambiguous on structure alone -- plain "match then keep the longest order-
    preserving subset" can't do this, since if nothing is uniquely resolvable without order
    information in the first place, there is nothing yet to filter. A real branch/structural
    difference (not just movable-instruction churn) can still leave some anchors genuinely
    unresolved rather than guessed.
    """
    baseline_order = [idx for idx, _ in baseline_anchors]
    probe_order = [idx for idx, _ in probe_anchors]
    baseline_by_idx = dict(baseline_anchors)
    probe_by_idx = dict(probe_anchors)

    lo = [0] * len(baseline_order)
    hi = [len(probe_order) - 1] * len(baseline_order)
    committed_probe_position: Dict[int, int] = {}
    facts: Dict[int, Dict[var_id_T, constant_T]] = {}

    progress = True
    while progress:
        progress = False
        proposals: Dict[int, List[Tuple[int, List[Tuple[var_id_T, var_id_T]], Dict[var_id_T, constant_T]]]] = \
            defaultdict(list)

        for b_pos, b_idx in enumerate(baseline_order):
            if b_pos in committed_probe_position:
                continue
            b_instr = baseline_by_idx[b_idx]
            matches = []
            for p_pos in range(lo[b_pos], hi[b_pos] + 1):
                p_instr = probe_by_idx[probe_order[p_pos]]
                for pending, step_facts in _instruction_correspondences(b_instr, p_instr, var_map):
                    matches.append((p_pos, pending, step_facts))
            if len(matches) == 1:
                p_pos, pending, step_facts = matches[0]
                proposals[p_pos].append((b_pos, pending, step_facts))

        commits = [(p_pos, props[0]) for p_pos, props in proposals.items() if len(props) == 1]
        if not commits:
            break

        for p_pos, (b_pos, pending, step_facts) in commits:
            for baseline_var, probe_var in pending:
                var_map[baseline_var] = probe_var
            if step_facts:
                facts[baseline_order[b_pos]] = step_facts
            committed_probe_position[b_pos] = p_pos
            for other_pos in range(len(baseline_order)):
                if other_pos in committed_probe_position:
                    continue
                if other_pos < b_pos:
                    hi[other_pos] = min(hi[other_pos], p_pos - 1)
                elif other_pos > b_pos:
                    lo[other_pos] = max(lo[other_pos], p_pos + 1)
            progress = True

    return facts, var_map


def match_block_instructions(baseline_instrs: List[Dict[str, Any]], probe_instrs: List[Dict[str, Any]],
                             seed_var_map: Optional[var_map_T] = None) -> \
        Tuple[Dict[int, Dict[var_id_T, constant_T]], var_map_T]:
    """
    Matches a block's baseline instructions against its probe instructions (see the module
    docstring for the movable/anchor design), returning ({baseline_instruction_index:
    {var: literal}}, confirmed_var_map). seed_var_map primes the correspondence with facts
    already confirmed elsewhere (e.g. by a dominating predecessor block), feeding the
    constraint propagation from the start.

    Two passes: anchors first (_match_anchors, order-preserving, since their relative order
    can't have changed), then every movable instruction in the block as one global pool
    (_match_item_set, not bracketed per anchor-gap -- a movable instruction can legally be
    reordered across an anchor it doesn't conflict with), seeded by whatever the anchor pass
    and seed_var_map already confirmed.
    """
    var_map: var_map_T = dict(seed_var_map or {})

    baseline_anchors: List[Tuple[int, Dict[str, Any]]] = []
    baseline_movable: List[Tuple[int, Dict[str, Any]]] = []
    for idx, instr in enumerate(baseline_instrs):
        (baseline_movable if _is_movable(instr) else baseline_anchors).append((idx, instr))

    probe_anchors: List[Tuple[int, Dict[str, Any]]] = []
    probe_movable: List[Tuple[int, Dict[str, Any]]] = []
    for idx, instr in enumerate(probe_instrs):
        (probe_movable if _is_movable(instr) else probe_anchors).append((idx, instr))

    anchor_facts, var_map = _match_anchors(baseline_anchors, probe_anchors, var_map)
    movable_facts, var_map, _ = _match_item_set(baseline_movable, probe_movable, var_map)

    facts: Dict[int, Dict[var_id_T, constant_T]] = defaultdict(dict)
    for idx, var_facts in anchor_facts.items():
        facts[idx].update(var_facts)
    for idx, var_facts in movable_facts.items():
        facts[idx].update(var_facts)

    return dict(facts), var_map


def extract_seed_facts_for_instructions(baseline_instrs: List[Dict[str, Any]],
                                        probe_instrs: List[Dict[str, Any]],
                                        seed_var_map: Optional[var_map_T] = None) -> Dict[int, Dict[var_id_T, constant_T]]:
    """
    Compares a single block's instructions between the baseline and the probe compilation,
    returning, for each baseline instruction index, the {var: literal} substitutions
    discovered at that instruction (see match_block_instructions for how).

    Instructions that disappear entirely between baseline and probe (e.g. a literal
    assignment that becomes dead once its only use is inlined) are not reported here: if the
    vanished instruction was a plain literal assignment, its value is already directly
    readable from the (still present) baseline instruction -- the constancy propagation pass
    that consumes these facts (src/constancy/propagation.py) handles that case syntactically,
    with no need for a fact about it.
    """
    facts, _ = match_block_instructions(baseline_instrs, probe_instrs, seed_var_map)
    return facts


def _named_components(container: Dict[str, Any]) -> List[Tuple[str, Dict[str, Any]]]:
    """
    A yulCFGJson container (either the top-level per-contract dict, or a 'subObjects'
    dict) stores its named entries alongside a sibling 'type' key; this filters that out
    """
    return [(name, value) for name, value in container.items() if name != "type" and isinstance(value, dict)]


def _iter_block_scopes(component: Dict[str, Any], path: scope_path_T):
    """
    Recursively walks a parsed CFG object/subObject, yielding (scope_path, blocks) for its
    own blocks, each of its functions' blocks, and recursively every nested subObject
    """
    yield path, component.get("blocks", [])

    for function_name, function_cfg in component.get("functions", {}).items():
        yield path + (function_name,), function_cfg.get("blocks", [])

    for sub_object_name, sub_object_cfg in _named_components(component.get("subObjects", {})):
        yield from _iter_block_scopes(sub_object_cfg, path + (sub_object_name,))


def iter_block_scopes(yul_cfg_json: Yul_CFG_T):
    """
    Yields (scope_path, blocks) for every block-owning scope in a contract's yulCFGJson:
    the top-level object, its functions, and (recursively) its subObjects and their functions
    """
    for object_name, component in _named_components(yul_cfg_json):
        yield from _iter_block_scopes(component, (object_name,))


def _successors(block: Dict[str, Any]) -> List[block_id_T]:
    return list(block.get("exit", {}).get("targets", []) or [])


def _block_dominance_order(blocks: List[Dict[str, Any]]) -> List[block_id_T]:
    """
    Orders a scope's blocks so that (in the common, loop-free case) a block's dominator is
    processed before it -- built directly off the raw yulCFGJson block list, mirroring
    parser.cfg_block_list.CFGBlockList.dominant_tree and reusing the same
    graphs.algorithms.compute_dominance_tree it's built on, rather than a parsed CFG. The
    first block in the list is assumed to be the scope's entry point, matching that same
    class's own stated convention. A block reachable only through a loop back edge may not
    have a computable dominator relative to blocks processed after it; such blocks are simply
    appended at the end, in list order -- callers must treat an unprocessed predecessor as
    unknown, exactly as propagation.py's own block processing already does.
    """
    if not blocks:
        return []

    graph = nx.DiGraph()
    graph.add_nodes_from(block["id"] for block in blocks)
    for block in blocks:
        for successor in _successors(block):
            graph.add_edge(block["id"], successor)

    order = list(nx.topological_sort(compute_dominance_tree(graph, blocks[0]["id"])))

    ordered = set(order)
    order.extend(block["id"] for block in blocks if block["id"] not in ordered)
    return order


def _predecessors(blocks: List[Dict[str, Any]]) -> Dict[block_id_T, List[block_id_T]]:
    predecessors = defaultdict(list)
    for block in blocks:
        for successor in _successors(block):
            predecessors[successor].append(block["id"])
    return predecessors


def _defining_instruction(block: Dict[str, Any], var: var_id_T) -> Optional[Dict[str, Any]]:
    for instr in block.get("instructions", []):
        if var in instr.get("out", []):
            return instr
    return None


def _cond_correspondence(baseline_block: Dict[str, Any], probe_block: Dict[str, Any], baseline_cond: var_id_T,
                         probe_cond: var_id_T, var_map: var_map_T) -> Optional[bool]:
    """
    Whether probe_cond is the same branch condition as baseline_cond (True), a negation of it
    (False -- solc wrapped/unwrapped an `iszero` and swapped the two branch targets
    accordingly), or unrelated (None), given the variable correspondences already confirmed in
    var_map.

    Checks var_map first: if baseline_cond is already known (e.g. confirmed several blocks
    back, not locally re-derivable via _defining_instruction in this block at all), that's
    reused directly rather than re-deriving the correspondence from local instructions alone.
    Only falls back to a local structural check (both sides' own defining instruction, via
    _try_unify_instructions -- now against the real var_map, not a throwaway empty one) when
    baseline_cond isn't yet known.
    """
    if baseline_cond in var_map:
        if var_map[baseline_cond] == probe_cond:
            return True
        probe_cond_instr = _defining_instruction(probe_block, probe_cond)
        if probe_cond_instr is not None and probe_cond_instr.get("op") == "iszero" \
                and probe_cond_instr.get("in") == [var_map[baseline_cond]]:
            return False
        return None

    baseline_cond_instr = _defining_instruction(baseline_block, baseline_cond)
    probe_cond_instr = _defining_instruction(probe_block, probe_cond)
    if baseline_cond_instr is None or probe_cond_instr is None:
        return None

    if _try_unify_instructions(baseline_cond_instr, probe_cond_instr, var_map) is not None:
        return True

    if baseline_cond_instr.get("op") == "iszero" and len(baseline_cond_instr.get("in", [])) == 1:
        inner = baseline_cond_instr["in"][0]
        if not is_literal(inner):
            inner_defining = _defining_instruction(baseline_block, inner)
            if inner_defining is not None and \
                    _try_unify_instructions(inner_defining, probe_cond_instr, var_map) is not None:
                return False

    if probe_cond_instr.get("op") == "iszero" and len(probe_cond_instr.get("in", [])) == 1:
        inner = probe_cond_instr["in"][0]
        if not is_literal(inner):
            inner_defining = _defining_instruction(probe_block, inner)
            if inner_defining is not None and \
                    _try_unify_instructions(baseline_cond_instr, inner_defining, var_map) is not None:
                return False

    return None


def _propose_successor_mapping(baseline_block: Dict[str, Any], probe_block: Optional[Dict[str, Any]],
                               var_map: var_map_T) -> Dict[block_id_T, block_id_T]:
    """
    Proposes a baseline->probe successor-block correspondence from one already-confirmed block
    pairing: valid only if both blocks' exit shape agrees (same exit type, same number of
    targets), in which case corresponding successors are read positionally off each block's own
    (raw JSON, solc-ordered) targets list. Returns {} if the shape disagrees or probe_block is
    unknown -- contributing no candidate rather than a wrong one.

    For a ConditionalJump, also requires the branch condition itself to match (_cond_correspondence,
    using var_map -- the real, already-confirmed correspondence, not a throwaway empty one): a
    negated match (see _cond_correspondence) is accepted too, with the two branch targets
    swapped (targets[0] is the zero/falls_to case, targets[1] the nonzero/jump_to case -- see
    parser.cfg_block.CFGBlock.set_jump_info).
    """
    if probe_block is None:
        return {}
    baseline_exit, probe_exit = baseline_block.get("exit", {}), probe_block.get("exit", {})
    if baseline_exit.get("type") != probe_exit.get("type"):
        return {}

    negated = False
    if baseline_exit.get("type") == "ConditionalJump":
        baseline_cond, probe_cond = baseline_exit.get("cond"), probe_exit.get("cond")
        if baseline_cond is None or probe_cond is None:
            return {}
        if is_literal(baseline_cond) or is_literal(probe_cond):
            if baseline_cond != probe_cond:
                return {}
        else:
            correspondence = _cond_correspondence(baseline_block, probe_block, baseline_cond, probe_cond, var_map)
            if correspondence is None:
                return {}
            negated = not correspondence

    baseline_targets, probe_targets = _successors(baseline_block), _successors(probe_block)
    if len(baseline_targets) != len(probe_targets):
        return {}
    if negated:
        probe_targets = list(reversed(probe_targets))
    return dict(zip(baseline_targets, probe_targets))


def _reorder_phi_args(baseline_block: Dict[str, Any], probe_block: Dict[str, Any],
                      block_correspondence: Dict[block_id_T, block_id_T]) -> List[Dict[str, Any]]:
    """
    A copy of probe_block's instructions with each PhiFunction's `in` list permuted to align by
    predecessor identity rather than by raw position: the raw yulCFGJson gives a block with
    PhiFunctions an `entries` list, one entry per phi input position naming the predecessor
    block that produced it (parser.parser.process_block_entry), in its own compilation's block-id
    namespace. Nothing guarantees solc emits a merge block's predecessor list in the same order
    in both compilations, so a blind positional zip of PhiFunction `in` args (what plain
    instruction matching does for every other op) can silently misalign them.

    A baseline predecessor with no confirmed correspondence yet (a backward edge, not yet
    resolved when this block is processed) keeps its phi input in whatever slot is left over
    once the resolvable ones are placed -- the same blind-positional behavior as before for the
    part that genuinely can't be determined yet, so this is strictly additive, never a
    regression. Falls back to probe_block's instructions unchanged if `entries` is missing on
    either side or the lengths don't line up.
    """
    baseline_entries = baseline_block.get("entries")
    probe_entries = probe_block.get("entries")
    probe_instructions = probe_block.get("instructions", [])
    if not baseline_entries or not probe_entries or len(baseline_entries) != len(probe_entries):
        return probe_instructions

    probe_position_by_id: Dict[block_id_T, int] = {}
    for position, predecessor_id in enumerate(probe_entries):
        probe_position_by_id.setdefault(predecessor_id, position)

    permutation: List[Optional[int]] = [None] * len(baseline_entries)
    used_positions = set()
    for i, baseline_predecessor in enumerate(baseline_entries):
        mapped = block_correspondence.get(baseline_predecessor)
        probe_position = probe_position_by_id.get(mapped) if mapped is not None else None
        if probe_position is not None and probe_position not in used_positions:
            permutation[i] = probe_position
            used_positions.add(probe_position)

    remaining_positions = iter(position for position in range(len(probe_entries)) if position not in used_positions)
    for i in range(len(permutation)):
        if permutation[i] is None:
            permutation[i] = next(remaining_positions)

    reordered = []
    for instr in probe_instructions:
        if instr.get("op") == "PhiFunction" and len(instr.get("in", [])) == len(permutation):
            reordered.append({**instr, "in": [instr["in"][position] for position in permutation]})
        else:
            reordered.append(instr)
    return reordered


def _literal_value_table(blocks: List[Dict[str, Any]]) -> Dict[block_id_T, Dict[var_id_T, constant_T]]:
    """
    Per block, which variables are provably a compile-time literal at that point -- a forward
    dominance-order walk (mirroring the var_map seeding _match_scope already does), seeded from
    predecessors (a disagreement between predecessors drops that variable, same "unknown, not a
    guess" rule used everywhere else in this module) and extended by any block-local
    LiteralAssignment. Deliberately simple: direct LiteralAssignment only, no folding through
    arithmetic (see the module docstring for what this is, and isn't, used for).
    """
    by_id = {block["id"]: block for block in blocks}
    predecessors = _predecessors(blocks)
    table: Dict[block_id_T, Dict[var_id_T, constant_T]] = {}

    for block_id in _block_dominance_order(blocks):
        block = by_id[block_id]
        seed: Dict[var_id_T, constant_T] = {}
        conflicting: set = set()
        for predecessor_id in predecessors.get(block_id, []):
            predecessor_table = table.get(predecessor_id)
            if predecessor_table is None:
                continue  # not yet processed -- e.g. reachable only via a loop back edge
            for var, value in predecessor_table.items():
                if var in seed and seed[var] != value:
                    conflicting.add(var)
                else:
                    seed[var] = value
        for var in conflicting:
            del seed[var]  # predecessors disagree -- unknown, not a guess

        local = dict(seed)
        for instr in block.get("instructions", []):
            if instr.get("op") == "LiteralAssignment":
                out, in_ = instr.get("out", []), instr.get("in", [])
                if len(out) == 1 and len(in_) == 1 and is_literal(in_[0]):
                    local[out[0]] = in_[0]
        table[block_id] = local

    return table


def _fold_conditional_exit(block: Dict[str, Any],
                           literal_table_for_block: Dict[var_id_T, constant_T]) -> Dict[str, Any]:
    """
    block's exit unchanged, unless it's a ConditionalJump whose condition is a literal or
    resolves via literal_table_for_block, in which case an unconditional Jump to the
    corresponding target (targets[0] for "0x00", targets[1] otherwise -- see
    parser.cfg_block.CFGBlock.set_jump_info): solc can prove a branch always goes one way once
    the condition is a known compile-time constant, and eliminate the block that only existed to
    hold that check.
    """
    exit_ = block.get("exit", {})
    if exit_.get("type") != "ConditionalJump":
        return exit_
    cond = exit_.get("cond")
    value = cond if is_literal(cond) else literal_table_for_block.get(cond)
    if value is None:
        return exit_
    target = exit_["targets"][0 if value == "0x00" else 1]
    return {"type": "Jump", "targets": [target]}


def _merge_trivial_blocks(blocks: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """
    A working copy of blocks for matching purposes only (see the module docstring): folds every
    provably-constant ConditionalJump (_fold_conditional_exit) and then repeatedly absorbs a
    block into its sole remaining effective predecessor wherever that's now a trivial 1-in/1-out
    edge -- recomputing effective in-degree from folded exits each round, to a fixpoint, so a
    whole chain of trivial blocks collapses in one call.

    Only ever absorbs a block *into* a predecessor whose own branch was actually folded (directly,
    or transitively -- a predecessor that itself already absorbed a folded block counts too): a
    plain, always-unconditional chain that folding never touched is left alone, matched block by
    block exactly as before. This matters, not just for minimality -- confirmed directly against a
    hand-built regression case (two blocks joined by a completely ordinary Jump, no folding
    involved anywhere) that merging *every* trivial edge, not just ones downstream of a fold,
    silently destroys the block-by-block var_map seeding `_match_scope` otherwise relies on to
    disambiguate an otherwise-ambiguous instruction: pooling two blocks' movable instructions
    together before either is individually resolved can turn a previously-unique match into a
    multi-way tie. Re-validated on the real contract that this restriction changes nothing else --
    every merge outside a fold-triggered chain turned out to be unnecessary anyway, since
    `_match_scope`'s own normal predecessor-by-predecessor resolution already handles a block
    whose *only* structural issue was a now-dead sibling edge, once that edge is gone from its
    predecessor's folded exit.

    Also never absorbs a block that carries a PhiFunction (`entries` truthy), even if one of its
    *other* raw incoming edges happens to fold away elsewhere -- that would leave a stale, still-
    ambiguous phi inside a block now pretending to have only one route in (verified this
    restriction costs nothing on a real contract while closing a real gap).

    Each returned working block carries `_provenance` (one (original_block_id,
    original_instruction_index) pair per instruction, in order -- used to translate a fact found
    against the working copy back to where it really belongs) and `_members` (every original
    block id folded into it, tracked explicitly rather than derived from `_provenance`: an
    absorbed block with zero instructions, e.g. a bare FunctionReturn stub, would otherwise leave
    no trace at all and wrongly look unresolved to a caller checking coverage).
    """
    if not blocks:
        return []

    literal_table = _literal_value_table(blocks)
    by_id = {block["id"]: block for block in blocks}
    order = [block["id"] for block in blocks]
    entry_id = blocks[0]["id"]

    work: Dict[block_id_T, Dict[str, Any]] = {}
    for block in blocks:
        folded_exit = _fold_conditional_exit(block, literal_table.get(block["id"], {}))
        work[block["id"]] = {
            "instrs": [(block["id"], idx, instr) for idx, instr in enumerate(block.get("instructions", []))],
            "exit": folded_exit,
            "members": {block["id"]},
            "was_folded": folded_exit is not block.get("exit", {}),
        }

    def effective_successors(block_id: block_id_T) -> List[block_id_T]:
        return list(work[block_id]["exit"].get("targets", []) or [])

    progress = True
    while progress:
        progress = False
        effective_predecessors: Dict[block_id_T, List[block_id_T]] = defaultdict(list)
        for block_id in work:
            for successor in effective_successors(block_id):
                if successor in work:
                    effective_predecessors[successor].append(block_id)

        for block_id in list(work):
            if block_id == entry_id or by_id[block_id].get("entries"):
                continue
            predecessors = effective_predecessors.get(block_id, [])
            if len(predecessors) != 1:
                continue
            predecessor_id = predecessors[0]
            if predecessor_id == block_id or effective_successors(predecessor_id) != [block_id]:
                continue
            if not work[predecessor_id]["was_folded"]:
                continue  # only chase away blocks left behind by folding a literal branch
            work[predecessor_id]["instrs"] += work[block_id]["instrs"]
            work[predecessor_id]["exit"] = work[block_id]["exit"]
            work[predecessor_id]["members"] |= work[block_id]["members"]
            work[predecessor_id]["was_folded"] = work[predecessor_id]["was_folded"] or work[block_id]["was_folded"]
            del work[block_id]
            progress = True
            break

    working_blocks = []
    for block_id in order:
        if block_id not in work:
            continue
        entry = work[block_id]
        working_blocks.append({
            "id": block_id,
            "entries": by_id[block_id].get("entries"),
            "exit": entry["exit"],
            "instructions": [instr for (_, _, instr) in entry["instrs"]],
            "_provenance": [(origin_id, origin_idx) for (origin_id, origin_idx, _) in entry["instrs"]],
            "_members": entry["members"],
        })
    return working_blocks


def _match_scope(baseline_blocks: List[Dict[str, Any]], probe_blocks: List[Dict[str, Any]]) -> \
        Tuple[Dict[block_id_T, block_id_T], Dict[block_id_T, var_map_T], Dict[block_id_T, Dict[int, Dict[var_id_T, constant_T]]]]:
    """
    One dominance-order walk over a scope's blocks that resolves block correspondence and
    instruction-level facts together (see the module docstring for why these can't be two
    separate passes any more): the scope's shared entry block (position 0 in both lists, the
    same convention _block_dominance_order relies on) anchors the walk; each further block's
    correspondence is proposed by its already-resolved predecessors via
    _propose_successor_mapping, using each predecessor's own confirmed var_map (for the branch-
    condition check) -- a block is left unresolved if none of its predecessors are resolved yet
    (e.g. reachable only via a loop back edge, or via a predecessor that itself never resolved),
    or if its predecessors propose more than one distinct probe counterpart, mirroring the
    "unique candidate or nothing" rule used everywhere else in this module. Once resolved, a
    block's PhiFunctions are realigned by predecessor identity (_reorder_phi_args) and its
    instructions matched (match_block_instructions), seeded with every resolved non-backward
    predecessor's var_map merged together (a predecessor disagreement about a shared variable
    drops that variable from the seed rather than guessing).

    Returns (block_correspondence, var_maps_by_block, facts_by_block) -- facts_by_block only
    contains entries for blocks that actually produced at least one fact.

    This does not, and cannot, protect against every kind of mismatch: a silent single-block
    disappearance inside an otherwise-uniform chain (no branching to create an observable
    ambiguity) still resolves to a confident but unhelpful pairing -- see PROGRESS.md's
    StackCompressor finding, which is the actual fix for that class.
    """
    if not baseline_blocks or not probe_blocks:
        return {}, {}, {}

    baseline_by_id = {block["id"]: block for block in baseline_blocks}
    probe_by_id = {block["id"]: block for block in probe_blocks}
    predecessors = _predecessors(baseline_blocks)

    block_correspondence: Dict[block_id_T, block_id_T] = {baseline_blocks[0]["id"]: probe_blocks[0]["id"]}
    var_maps_by_block: Dict[block_id_T, var_map_T] = {}
    facts_by_block: Dict[block_id_T, Dict[int, Dict[var_id_T, constant_T]]] = {}

    for block_id in _block_dominance_order(baseline_blocks):
        baseline_block = baseline_by_id[block_id]

        if block_id not in block_correspondence:
            candidates = set()
            for predecessor_id in predecessors.get(block_id, []):
                predecessor_var_map = var_maps_by_block.get(predecessor_id)
                predecessor_probe_id = block_correspondence.get(predecessor_id)
                if predecessor_var_map is None or predecessor_probe_id is None:
                    continue  # not yet processed -- e.g. reachable only via a loop back edge
                proposed = _propose_successor_mapping(
                    baseline_by_id[predecessor_id], probe_by_id.get(predecessor_probe_id), predecessor_var_map)
                if block_id in proposed:
                    candidates.add(proposed[block_id])
            if len(candidates) == 1:
                candidate = candidates.pop()
                if candidate in probe_by_id:
                    block_correspondence[block_id] = candidate

        probe_block = probe_by_id.get(block_correspondence.get(block_id))
        if probe_block is None:
            continue

        seed_var_map: var_map_T = {}
        conflicting: set = set()
        for predecessor_id in predecessors.get(block_id, []):
            predecessor_map = var_maps_by_block.get(predecessor_id)
            if predecessor_map is None:
                continue  # not yet processed -- e.g. reachable only via a loop back edge
            for baseline_var, probe_var in predecessor_map.items():
                if baseline_var in seed_var_map and seed_var_map[baseline_var] != probe_var:
                    conflicting.add(baseline_var)
                else:
                    seed_var_map[baseline_var] = probe_var
        for baseline_var in conflicting:
            del seed_var_map[baseline_var]  # predecessors disagree -- unknown, not a guess

        probe_instructions = _reorder_phi_args(baseline_block, probe_block, block_correspondence)
        block_facts, block_var_map = match_block_instructions(
            baseline_block.get("instructions", []), probe_instructions, seed_var_map=seed_var_map)
        var_maps_by_block[block_id] = block_var_map
        if block_facts:
            facts_by_block[block_id] = block_facts

    return block_correspondence, var_maps_by_block, facts_by_block


def extract_seed_facts_for_contract(baseline_yul_cfg: Yul_CFG_T, probe_yul_cfg: Yul_CFG_T) -> seed_facts_T:
    """
    Walks every block scope shared between the baseline and probe yulCFGJson of the same
    contract and extracts all seed facts via _match_scope, matched against a normalized working
    copy of each scope's blocks (_merge_trivial_blocks -- see the module docstring) rather than
    the raw blocks directly. Every fact found (and the "no unique structural correspondence"
    check) is translated back to the real, unmerged baseline's block ids/instruction indices
    before being returned: this function's contract -- and everything downstream, propagation.py
    and annotate.py -- is completely unaffected by the normalization; only what gets discovered
    changes, never the addressing it's reported against or the CFG that gets annotated.
    """
    facts: seed_facts_T = {}

    baseline_scopes = dict(iter_block_scopes(baseline_yul_cfg))
    probe_scopes = dict(iter_block_scopes(probe_yul_cfg))

    for scope_path, baseline_blocks in baseline_scopes.items():
        probe_blocks = probe_scopes.get(scope_path)
        if probe_blocks is None:
            logging.warning(f"Scope {scope_path} is missing from the probe compilation; skipping")
            continue

        working_baseline = _merge_trivial_blocks(baseline_blocks)
        working_probe = _merge_trivial_blocks(probe_blocks)
        working_baseline_by_id = {block["id"]: block for block in working_baseline}

        block_correspondence, _, facts_by_block = _match_scope(working_baseline, working_probe)

        resolved_original_ids: set = set()
        for working_id in block_correspondence:
            resolved_original_ids |= working_baseline_by_id[working_id]["_members"]

        for block in baseline_blocks:
            if block["id"] not in resolved_original_ids:
                logging.warning(f"Block {block['id']} in scope {scope_path} has no unique structural "
                                f"correspondence in the probe compilation; skipping")

        for working_id, block_facts in facts_by_block.items():
            provenance = working_baseline_by_id[working_id]["_provenance"]
            for working_instr_idx, var_facts in block_facts.items():
                origin_block_id, origin_instr_idx = provenance[working_instr_idx]
                for var, value in var_facts.items():
                    facts[(scope_path, origin_block_id, origin_instr_idx, var)] = value

    return facts


def isolate_cleanup_sequence(seq: str) -> str:
    """
    seq with an explicit, empty cleanup sequence appended ("<seq>:") if it doesn't already
    contain a colon. Without this, a colon-less sequence still runs solc's own
    OptimiserSettings::DefaultYulOptimiserCleanupSteps ("fDnTOcmuO",
    libsolidity/interface/OptimiserSettings.h) after it -- silently, since
    StandardCompiler.cpp's checkOptimizerDetailSteps only overrides the cleanup sequence when
    a colon is present, otherwise leaving solc's default cleanup in place. That default
    cleanup itself contains "T" and "m", confounding any comparison meant to isolate the
    effect of one specific extra step (see PROGRESS.md). A sequence that already has a real,
    deliberate colon (e.g. DEFAULT_OPTIMIZER_SEQUENCE) is returned unchanged -- solc allows at
    most one, and this is a no-op exactly where a colon-based occurrence (one after the real
    cleanup delimiter) doesn't need any help.
    """
    return seq if ":" in seq else seq + ":"


def with_stack_allocation_disabled(json_input: Dict[str, Any]) -> Dict[str, Any]:
    """
    A deep copy of json_input with settings.optimizer.details.yulDetails.stackAllocation
    forced to False, disabling solc's StackCompressor (libyul/optimiser/StackCompressor.cpp).
    OptimiserSuite::run invokes it unconditionally between the main optimizer sequence and the
    cleanup sequence (Suite.cpp), and its output can vary substantially -- duplicating or
    restructuring large portions of code to resolve "stack too deep" situations -- based on
    small stack-pressure differences that a single extra step can shift. Confirmed directly: on
    a real contract, one extra "T" changed a scope's block count from 142 to 92; with this
    setting, both land at 92 and the resulting conflicting-fact warnings disappear (see
    PROGRESS.md). Confounds an isolated before/after comparison the same way a hidden default
    cleanup sequence did (see isolate_cleanup_sequence) -- this is not part of the requested
    step sequence at all. Uses get_yul_details (execution.sol_compilation) so any other
    yulDetails setting the caller has already set (e.g. optimizerSteps) is preserved.
    """
    json_input = copy.deepcopy(json_input)
    get_yul_details(json_input.setdefault("settings", {}))["stackAllocation"] = False
    return json_input


def probe_sequence(base_sequence: str, steps_to_consider: List[str] = CONSTANT_PROPAGATING_STEPS) -> str:
    """
    The sequence used to discover constancy facts: the (isolated) baseline sequence with an
    extra, final application of the constant-propagating steps appended. Isolating the
    baseline first (see isolate_cleanup_sequence) means a colon-less base_sequence gets its
    extra steps placed as an explicit, isolated cleanup (e.g. ":T") rather than silently
    running solc's own default cleanup on top of them; a base_sequence that already has a
    real colon (the production DEFAULT_OPTIMIZER_SEQUENCE) is unaffected.
    """
    return isolate_cleanup_sequence(base_sequence) + "".join(steps_to_consider)
