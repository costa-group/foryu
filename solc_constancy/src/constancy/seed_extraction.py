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

`extract_seed_facts_for_contract` runs this per scope in a forward BFS order from the scope's
entry block (`_block_processing_order`, mirroring `propagation.py`'s own traversal of the same
name -- ported rather than imported, since the two operate on different block representations),
seeding each block's matcher with the variable correspondences its already-processed predecessors
confirmed. This is not just extra coverage: if a block's own local match ever produced a
correspondence that contradicts what an already-processed predecessor already confirmed for the
same variable, the seed makes that a hard conflict (rejected, not silently trusted) instead of two
independently-lucky per-block answers going unchecked against each other -- exactly the gap that
let the 'T'-occurrence contradiction above slip through undetected before this fix. (A topological
sort of the *dominator tree* was tried first and seemed like a natural fit, but only guarantees a
block's dominator is processed before it, not its actual CFG predecessors -- for an ordinary
if/else merge whose dominator isn't itself a direct predecessor, that let the merge block be
visited before either branch, permanently failing to resolve it despite both predecessors, once
available, unambiguously agreeing; confirmed on a real contract and fixed by switching to a plain
BFS, see PROGRESS.md.)

Matching blocks themselves is not safe by raw id alone either, for the same underlying reason:
`extract_seed_facts_for_contract` establishes a baseline<->probe block correspondence from the
scope's shared entry block, propagated via matching CFG-edge shape (exit type + successor
count, and -- for a ConditionalJump -- the condition variable's own defining instruction, not
just the branch arity) rather than assuming equal ids name the same block. Block-correspondence
resolution and instruction matching are interleaved into one forward-BFS walk per scope
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
resolves to a known literal (`_literal_value_table`, a forward BFS walk tracking direct
`LiteralAssignment`s only -- deliberately not a general constant-folding engine) into an
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
from typing import Any, Dict, List, Optional, Set, Tuple

from constancy.evm_arithmetic import evaluate as _evaluate_arithmetic
from execution.sol_compilation import get_yul_details
from global_params.types import block_id_T, component_name_T, constant_T, var_id_T, Yul_CFG_T

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


def _direct_literal_table(instructions: List[Dict[str, Any]]) -> Dict[var_id_T, constant_T]:
    """
    {var: literal} for every variable directly assigned a literal (LiteralAssignment) within
    this one instruction list -- a flat scan, no block-processing-order/cross-block threading needed
    (unlike _literal_value_table, which exists for a different concern, cross-block CFG
    normalization; _try_unify_instructions and everything that calls it only ever need to know
    about one block's own instructions). Computed for the *probe* side only and used to resolve
    a probe argument that isn't itself a literal string but is provably one anyway -- e.g. CSE
    hoists what used to be several per-call-site literal copies into one shared, named variable
    -- so structural matching doesn't spuriously reject an argument position where baseline
    inlines a literal directly and probe materializes the identical value through an extra
    variable. Deliberately never computed/used for the baseline side -- see
    _try_unify_instructions for why.
    """
    table: Dict[var_id_T, constant_T] = {}
    for instr in instructions:
        if instr.get("op") == "LiteralAssignment":
            out, in_ = instr.get("out", []), instr.get("in", [])
            if len(out) == 1 and len(in_) == 1 and is_literal(in_[0]):
                table[out[0]] = in_[0]
    return table


def _scope_defining_instructions(blocks: List[Dict[str, Any]]) -> Dict[var_id_T, Dict[str, Any]]:
    """
    {var: instr} for every variable's defining instruction across *all* of a scope's blocks --
    unlike _defining_instruction (one block only), this covers a variable defined in an ancestor
    block and carried live into a descendant one. Feeds _values_provably_equal, which needs to
    trace a variable back to its definition regardless of which block originally computed it.
    """
    defs: Dict[var_id_T, Dict[str, Any]] = {}
    for block in blocks:
        for instr in block.get("instructions", []):
            for var in instr.get("out", []):
                defs[var] = instr
    return defs


def _resolve_scope_literal(var: var_id_T, defs: Dict[var_id_T, Dict[str, Any]]) -> Optional[constant_T]:
    """
    The literal value var is directly assigned (LiteralAssignment), tracing through defs
    (_scope_defining_instructions, scope-wide) rather than _direct_literal_table's block-local
    scan -- so a LiteralAssignment carried in from an ancestor block (confirmed on a real
    contract: baseline inlines a literal directly, probe references a variable whose
    LiteralAssignment lives in a different block than the one where it's actually used) is still
    recognized. Deliberately just LiteralAssignment, matching _direct_literal_table's own stated
    scope -- not a general constant-folding engine, that's _literal_value_table's separate
    concern (used only for block-exit folding).
    """
    instr = defs.get(var)
    if instr is None or instr.get("op") != "LiteralAssignment":
        return None
    out, in_ = instr.get("out", []), instr.get("in", [])
    if len(out) == 1 and len(in_) == 1 and is_literal(in_[0]):
        return in_[0]
    return None


def _values_provably_equal(var_x: var_id_T, var_y: var_id_T,
                           defs: Dict[var_id_T, Dict[str, Any]], _depth: int = 0) -> bool:
    """
    Whether var_x and var_y -- two variables from the *same* compilation (both baseline, or both
    probe; this is never a cross-compilation check) -- are provably the same value, tracing each
    back through defs (_scope_defining_instructions) when they're not literally the same name.

    Exists to see through rematerialization: solc's optimizer can recompute an already-known,
    cheap-to-recompute value fresh at its use site instead of carrying it live across a block
    boundary (confirmed on a real contract: a value carried live across a block boundary and
    reused directly in baseline gets recomputed via a fresh chain of movable ops in probe,
    referencing an already-correctly-matched variable -- e.g. baseline's v18 = and(0x01, v15)
    computed once and reused, vs. probe recomputing and(0x01, v15) again with a new output
    variable at the point of use). Every op along the way must be in _MOVABLE_OPS -- the same
    allowlist this module already trusts as pure/deterministic/side-effect-free to justify
    freely reordering movable instructions within a block, so recursing through a chain of them
    is sound for the same reason. Recursion bottoms out only at direct string equality (the same
    literal, or literally the same variable name) or -- implicitly, via the caller -- an already
    independently confirmed var_map entry; it never invents a new kind of equivalence.

    _depth is a purely defensive recursion guard (SSA form already precludes a real cycle; every
    chain observed on real contracts so far is 1-2 levels deep).
    """
    if var_x == var_y:
        return True
    if is_literal(var_x) or is_literal(var_y) or _depth > 50:
        return False

    instr_x, instr_y = defs.get(var_x), defs.get(var_y)
    if instr_x is None or instr_y is None:
        return False

    op = instr_x.get("op")
    if op != instr_y.get("op") or op not in _MOVABLE_OPS:
        return False

    args_x, args_y = instr_x.get("in", []), instr_y.get("in", [])
    if len(args_x) != len(args_y):
        return False

    def matches(xs: List[var_id_T], ys: List[var_id_T]) -> bool:
        return all(_values_provably_equal(x, y, defs, _depth + 1) for x, y in zip(xs, ys))

    return matches(args_x, args_y) or (op in _COMMUTATIVE_OPS and len(args_x) == 2
                                       and matches(args_x, list(reversed(args_y))))


def _try_unify_instructions(baseline_instr: Dict[str, Any], probe_instr: Dict[str, Any], var_map: var_map_T,
                            probe_literal_table: Dict[var_id_T, constant_T],
                            probe_defs: Optional[Dict[var_id_T, Dict[str, Any]]] = None) -> \
        Optional[Tuple[List[Tuple[var_id_T, var_id_T]], Dict[var_id_T, constant_T]]]:
    """
    Checks whether baseline_instr and probe_instr can be the "same" instruction (the same one,
    before and after a value-substituting step), given the variable correspondences already
    confirmed in var_map. Every argument position must be explained by one of: the same
    literal value on both sides -- a probe argument that isn't itself a literal string is also
    resolved through probe_literal_table first (see _direct_literal_table: e.g. CSE hoists what
    used to be several per-call-site literal copies into one shared, named variable), then, if
    that misses, through probe_defs scope-wide (_resolve_scope_literal: a LiteralAssignment
    carried in from an ancestor block, invisible to probe_literal_table's block-local scan) --
    so a literal baseline inlines directly still matches a probe variable that's provably the
    same literal however far away it was actually assigned; an already-confirmed (or newly
    proposed) baseline->probe variable correspondence;
    or a baseline variable that became a literal in the probe (the actual substitution this
    whole analysis looks for). Any other kind of difference -- two different symbolic names, two
    different literal values, or a literal turning symbolic -- means these are not really the
    same instruction, just two that happen to look alike after a shift.

    Deliberately one-directional (only probe_arg is resolved through a literal table, never
    baseline_arg): resolving baseline_arg the same way would silently break the "a baseline
    variable's own LiteralAssignment vanishes once inlined, and the fact is recorded at its use
    site instead" mechanism (extract_seed_facts_for_instructions's docstring) -- baseline_arg
    has to stay symbolic here even when baseline's own table could resolve it, precisely so a
    probe-side literal at this same position can still be recognized as new information about
    it (confirmed by a regression this caused during development: resolving both sides made
    every already-known-literal baseline variable "trivially consistent" with its own probe
    counterpart instead of reporting the substitution).

    A symbolic argument that conflicts with an already-confirmed var_map entry isn't rejected
    outright either: if probe_arg is provably the same value as var_map[baseline_arg] via a chain
    of movable ops (_values_provably_equal, using probe_defs), that's recognized as
    rematerialization -- solc recomputing an already-known value fresh at its use site instead of
    carrying it live across a block boundary -- rather than a genuine mismatch.

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
        baseline_literal = is_literal(baseline_arg)
        probe_resolved = probe_arg if is_literal(probe_arg) else \
            (probe_literal_table.get(probe_arg) or _resolve_scope_literal(probe_arg, probe_defs or {}))
        probe_literal = probe_resolved is not None
        if baseline_literal and probe_literal:
            if baseline_arg != probe_resolved:
                return None
        elif baseline_literal and not probe_literal:
            return None
        elif not baseline_literal and probe_literal:
            facts[baseline_arg] = probe_resolved
        else:
            if baseline_arg in var_map and var_map[baseline_arg] != probe_arg:
                if not _values_provably_equal(probe_arg, var_map[baseline_arg], probe_defs or {}):
                    return None
                # probe_arg is a rematerialized recomputation of the same already-confirmed
                # value -- explained, but baseline_arg's own correspondence stays as already
                # confirmed, so nothing new is proposed for it here
                continue
            pending.append((baseline_arg, probe_arg))

    return pending, facts


def _instruction_correspondences(baseline_instr: Dict[str, Any], probe_instr: Dict[str, Any], var_map: var_map_T,
                                 probe_literal_table: Dict[var_id_T, constant_T],
                                 probe_defs: Optional[Dict[var_id_T, Dict[str, Any]]] = None) -> \
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
    result = _try_unify_instructions(baseline_instr, probe_instr, var_map, probe_literal_table, probe_defs)
    if result is not None:
        return [result]

    probe_in = probe_instr.get("in", [])
    baseline_in = baseline_instr.get("in", [])
    already_known = any(arg in var_map for arg in baseline_in if not is_literal(arg))
    if not already_known and probe_instr.get("op") in _COMMUTATIVE_OPS and len(probe_in) == 2 \
            and probe_in[0] != probe_in[1]:
        swapped = {**probe_instr, "in": [probe_in[1], probe_in[0]]}
        result = _try_unify_instructions(baseline_instr, swapped, var_map, probe_literal_table, probe_defs)
        if result is not None:
            return [result]

    return []


def _is_movable(instr: Dict[str, Any]) -> bool:
    """See _MOVABLE_OPS and the module docstring."""
    return instr.get("op") in _MOVABLE_OPS


def _match_item_set(baseline_items: List[Tuple[int, Dict[str, Any]]], probe_items: List[Tuple[int, Dict[str, Any]]],
                    var_map: var_map_T, probe_literal_table: Dict[var_id_T, constant_T],
                    probe_defs: Optional[Dict[var_id_T, Dict[str, Any]]] = None) -> \
        Tuple[Dict[int, Dict[var_id_T, constant_T]], var_map_T, Dict[int, int]]:
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
                      for pending, step_facts in _instruction_correspondences(
                          b_instr, p_instr, var_map, probe_literal_table, probe_defs)]
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
                   var_map: var_map_T, probe_literal_table: Dict[var_id_T, constant_T],
                   probe_defs: Optional[Dict[var_id_T, Dict[str, Any]]] = None) -> \
        Tuple[Dict[int, Dict[var_id_T, constant_T]], var_map_T]:
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
                for pending, step_facts in _instruction_correspondences(
                        b_instr, p_instr, var_map, probe_literal_table, probe_defs):
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
                             seed_var_map: Optional[var_map_T] = None,
                             probe_defs: Optional[Dict[var_id_T, Dict[str, Any]]] = None) -> \
        Tuple[Dict[int, Dict[var_id_T, constant_T]], var_map_T]:
    """
    Matches a block's baseline instructions against its probe instructions (see the module
    docstring for the movable/anchor design), returning ({baseline_instruction_index:
    {var: literal}}, confirmed_var_map). seed_var_map primes the correspondence with facts
    already confirmed elsewhere (e.g. by a dominating predecessor block), feeding the
    constraint propagation from the start. probe_defs (_scope_defining_instructions, scope-wide
    -- not just this block's own probe_instrs) lets a conflicting argument still unify when it's
    a rematerialized recomputation of an already-confirmed value (_values_provably_equal, used by
    _try_unify_instructions).

    Two passes: anchors first (_match_anchors, order-preserving, since their relative order
    can't have changed), then every movable instruction in the block as one global pool
    (_match_item_set, not bracketed per anchor-gap -- a movable instruction can legally be
    reordered across an anchor it doesn't conflict with), seeded by whatever the anchor pass
    and seed_var_map already confirmed.
    """
    var_map: var_map_T = dict(seed_var_map or {})
    probe_literal_table = _direct_literal_table(probe_instrs)

    baseline_anchors: List[Tuple[int, Dict[str, Any]]] = []
    baseline_movable: List[Tuple[int, Dict[str, Any]]] = []
    for idx, instr in enumerate(baseline_instrs):
        (baseline_movable if _is_movable(instr) else baseline_anchors).append((idx, instr))

    probe_anchors: List[Tuple[int, Dict[str, Any]]] = []
    probe_movable: List[Tuple[int, Dict[str, Any]]] = []
    for idx, instr in enumerate(probe_instrs):
        (probe_movable if _is_movable(instr) else probe_anchors).append((idx, instr))

    anchor_facts, var_map = _match_anchors(baseline_anchors, probe_anchors, var_map, probe_literal_table, probe_defs)
    movable_facts, var_map, _ = _match_item_set(baseline_movable, probe_movable, var_map, probe_literal_table,
                                                probe_defs)

    facts: Dict[int, Dict[var_id_T, constant_T]] = defaultdict(dict)
    for idx, var_facts in anchor_facts.items():
        facts[idx].update(var_facts)
    for idx, var_facts in movable_facts.items():
        facts[idx].update(var_facts)

    return dict(facts), var_map


def extract_seed_facts_for_instructions(baseline_instrs: List[Dict[str, Any]],
                                        probe_instrs: List[Dict[str, Any]],
                                        seed_var_map: Optional[var_map_T] = None,
                                        probe_defs: Optional[Dict[var_id_T, Dict[str, Any]]] = None) -> \
        Dict[int, Dict[var_id_T, constant_T]]:
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
    facts, _ = match_block_instructions(baseline_instrs, probe_instrs, seed_var_map, probe_defs)
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


def _scope_entry_id(yul_cfg_json: Yul_CFG_T, scope_path: scope_path_T,
                    blocks: List[Dict[str, Any]]) -> Optional[block_id_T]:
    """
    The block id that's actually this scope's entry point -- resolved from the raw yulCFGJson's
    own "entry" field on scope_path's own component dict (walking scope_path[1:] through
    "functions"/"subObjects", mirroring _iter_block_scopes's own path-building) when present, or
    blocks[0]["id"] otherwise.

    "entry" is confirmed (checked against example_json.json) present only at the *function*
    level (parser.parser.parse_function's function_json.get("entry", "")); an object/subObject-
    level scope has no such field at all, so the positional fallback is the only option there --
    and it isn't a fresh assumption either: it's the only rule parser.parser.parser_block_list's
    CFGBlockList.add_block ever actually applies for determining start_block in this codebase's
    real parse path (every block added in raw JSON order, no caller ever passes
    is_start_block=True), just made explicit and centralized here instead of re-derived
    positionally wherever a "the entry block" concept is needed.
    """
    if not scope_path:
        return blocks[0]["id"] if blocks else None

    component = yul_cfg_json[scope_path[0]]
    for name in scope_path[1:]:
        component = component.get("functions", {}).get(name) or component.get("subObjects", {})[name]

    entry = component.get("entry")
    return entry if entry else (blocks[0]["id"] if blocks else None)


def _block_processing_order(blocks: List[Dict[str, Any]],
                            entry_id: Optional[block_id_T] = None) -> List[block_id_T]:
    """
    A forward BFS order from entry_id (defaulting to blocks[0]["id"] when not given -- every
    caller within this module that doesn't have a real one on hand yet, including every test),
    so that (in the common, loop-free case) at least one of a block's real predecessors is
    processed before it -- ported from (not imported from) propagation.py's own
    _block_processing_order, which does the equivalent BFS over a parsed CFGBlockList; this one
    works directly off the raw yulCFGJson block list, via this file's own _successors.

    Replaces an earlier version that ordered blocks via a topological sort of the *dominator
    tree* (networkx's compute_dominance_tree) instead. That only guarantees a block's dominator
    is processed before it, not its actual CFG predecessors -- for an ordinary if/else merge
    whose dominator isn't itself a direct predecessor (the common case whenever either branch has
    more than one block), the merge block could be scheduled before the branch blocks that
    actually feed it. Confirmed directly on a real contract (0x24fcfc492c1393274b6bcd568ac9e
    225bec93584's copy_byte_array_to_storage_from_string_to_string: a FunctionReturn block merging
    two branches sat at dominance-order position 5, while its own two real predecessors sat at
    positions 8 and 13 -- so it was always permanently unresolved by _match_scope's single forward
    pass, despite both predecessors, once available, unambiguously agreeing on the correspondence)
    and quantified across the whole contract's trace: switching to this BFS dropped unresolved-
    block warnings from 2594 to 435 (an 83% reduction). See PROGRESS.md.

    A block reachable only through a loop back edge may still be unprocessed when a successor
    first needs it -- such blocks are simply appended at the end, in list order; callers must
    treat an unprocessed predecessor as unknown, exactly as propagation.py's own block processing
    already does.
    """
    if not blocks:
        return []
    entry_id = entry_id if entry_id is not None else blocks[0]["id"]

    by_id = {block["id"]: block for block in blocks}
    order: List[block_id_T] = []
    visited: Set[block_id_T] = set()
    queue = [entry_id]

    while queue:
        node = queue.pop(0)
        if node in visited or node not in by_id:
            continue
        visited.add(node)
        order.append(node)
        queue.extend(succ for succ in _successors(by_id[node]) if succ in by_id and succ not in visited)

    order.extend(block["id"] for block in blocks if block["id"] not in visited)
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


def _zero_comparison_target(instr: Dict[str, Any]) -> Optional[var_id_T]:
    """
    The operand X if instr computes "X == 0" -- either iszero(X) directly, or eq(0x00, X) /
    eq(X, 0x00) (eq being commutative, both orderings are checked) -- else None. eq(0, X) and
    iszero(X) compute the identical boolean; ExpressionSimplifier is free to canonicalize
    between them, which a plain op-name comparison can't see through on its own.
    """
    op, in_ = instr.get("op"), instr.get("in", [])
    if op == "iszero" and len(in_) == 1:
        return in_[0]
    if op == "eq" and len(in_) == 2:
        a, b = in_
        if is_literal(a) and a == "0x00" and not is_literal(b):
            return b
        if is_literal(b) and b == "0x00" and not is_literal(a):
            return a
    return None


def _cond_correspondence(baseline_block: Dict[str, Any], probe_block: Dict[str, Any], baseline_cond: var_id_T,
                         probe_cond: var_id_T, var_map: var_map_T,
                         probe_defs: Optional[Dict[var_id_T, Dict[str, Any]]] = None) -> Optional[bool]:
    """
    Whether probe_cond is the same branch condition as baseline_cond (True), a negation of it
    (False -- solc wrapped/unwrapped an `iszero` and swapped the two branch targets
    accordingly), or unrelated (None), given the variable correspondences already confirmed in
    var_map.

    Checks var_map first: if baseline_cond is already known (e.g. confirmed several blocks
    back, not locally re-derivable via _defining_instruction in this block at all), that's
    reused directly rather than re-deriving the correspondence from local instructions alone --
    including when probe_cond is a rematerialized recomputation of that already-known value
    rather than the literal same variable (_values_provably_equal, using probe_defs). Only falls
    back to a local structural check (both sides' own defining instruction, via
    _try_unify_instructions -- now against the real var_map, not a throwaway empty one) when
    baseline_cond isn't yet known.

    Also recognizes eq(0x00, X)/eq(X, 0x00) as equivalent to iszero(X) (_zero_comparison_target)
    -- a real ExpressionSimplifier canonicalization, confirmed on a real contract -- as a
    *direct* match (not a negation: both compute the identical boolean), independent of the
    iszero-wrapping checks above.
    """
    if baseline_cond in var_map:
        if var_map[baseline_cond] == probe_cond:
            return True
        if _values_provably_equal(probe_cond, var_map[baseline_cond], probe_defs or {}):
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

    if _try_unify_instructions(baseline_cond_instr, probe_cond_instr, var_map, {}, probe_defs) is not None:
        return True

    if baseline_cond_instr.get("op") == "iszero" and len(baseline_cond_instr.get("in", [])) == 1:
        inner = baseline_cond_instr["in"][0]
        if not is_literal(inner):
            inner_defining = _defining_instruction(baseline_block, inner)
            if inner_defining is not None and \
                    _try_unify_instructions(inner_defining, probe_cond_instr, var_map, {}, probe_defs) is not None:
                return False

    if probe_cond_instr.get("op") == "iszero" and len(probe_cond_instr.get("in", [])) == 1:
        inner = probe_cond_instr["in"][0]
        if not is_literal(inner):
            inner_defining = _defining_instruction(probe_block, inner)
            if inner_defining is not None and \
                    _try_unify_instructions(baseline_cond_instr, inner_defining, var_map, {}, probe_defs) is not None:
                return False

    baseline_zero_target = _zero_comparison_target(baseline_cond_instr)
    probe_zero_target = _zero_comparison_target(probe_cond_instr)
    if baseline_zero_target is not None and probe_zero_target is not None:
        if baseline_zero_target in var_map:
            if var_map[baseline_zero_target] == probe_zero_target:
                return True
        elif not is_literal(baseline_zero_target) and not is_literal(probe_zero_target):
            baseline_inner_defining = _defining_instruction(baseline_block, baseline_zero_target)
            probe_inner_defining = _defining_instruction(probe_block, probe_zero_target)
            if baseline_inner_defining is not None and probe_inner_defining is not None and \
                    _try_unify_instructions(baseline_inner_defining, probe_inner_defining, var_map, {},
                                            probe_defs) is not None:
                return True

    return None


def _propose_successor_mapping(baseline_block: Dict[str, Any], probe_block: Optional[Dict[str, Any]],
                               var_map: var_map_T,
                               probe_defs: Optional[Dict[var_id_T, Dict[str, Any]]] = None) -> Dict[block_id_T, block_id_T]:
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
            correspondence = _cond_correspondence(baseline_block, probe_block, baseline_cond, probe_cond, var_map,
                                                  probe_defs)
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


def _resolve_phi_value(block: Dict[str, Any], instr: Dict[str, Any],
                       table: Dict[block_id_T, Dict[var_id_T, constant_T]]) -> Optional[constant_T]:
    """
    The literal value instr's PhiFunction output is provably equal to, or None if it isn't
    provably one -- using the block's own "entries" list (one predecessor per phi input
    position, the same convention _reorder_phi_args already relies on) to resolve each input
    against *its own originating predecessor's* table (not the block's merged seed, which has
    no notion of "which predecessor" a phi input came from). A predecessor not yet processed
    (e.g. only reachable via a loop back edge) is simply skipped, exactly like the predecessor-
    merge below -- matching CLAUDE.md's documented phi rule (no information unless every visible
    branch agrees on the same constant), just applied edge by edge instead of only stated.
    """
    entries = block.get("entries") or []
    in_ = instr.get("in", [])
    if len(entries) != len(in_):
        return None

    values = set()
    for predecessor_id, phi_input in zip(entries, in_):
        predecessor_table = table.get(predecessor_id)
        if predecessor_table is None:
            continue  # not yet processed -- e.g. reachable only via a loop back edge
        resolved = phi_input if is_literal(phi_input) else predecessor_table.get(phi_input)
        if resolved is None:
            return None  # this predecessor's contribution isn't constant -- neither is the phi
        values.add(resolved)

    return values.pop() if len(values) == 1 else None


def _literal_value_table(blocks: List[Dict[str, Any]],
                         entry_id: Optional[block_id_T] = None) -> Dict[block_id_T, Dict[var_id_T, constant_T]]:
    """
    Per block, which variables are provably a compile-time literal at that point -- a forward
    BFS walk from entry_id (mirroring the var_map seeding _match_scope already does), seeded from
    predecessors (a disagreement between predecessors drops that variable, same "unknown, not a
    guess" rule used everywhere else in this module), then extended, instruction by instruction,
    by: a direct LiteralAssignment; any op evm_arithmetic.evaluate can fold once every one of its
    arguments is already known (via this same, incrementally-built table, so a later instruction
    can use an earlier one's folded result within the same block -- e.g. a whole `shl`/`sub`/`gt`
    chain over literals, not just one direct assignment); or a PhiFunction whose every resolvable
    predecessor agrees (_resolve_phi_value).
    """
    by_id = {block["id"]: block for block in blocks}
    predecessors = _predecessors(blocks)
    table: Dict[block_id_T, Dict[var_id_T, constant_T]] = {}

    for block_id in _block_processing_order(blocks, entry_id):
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
            op, out, in_ = instr.get("op"), instr.get("out", []), instr.get("in", [])
            if op == "LiteralAssignment":
                if len(out) == 1 and len(in_) == 1 and is_literal(in_[0]):
                    local[out[0]] = in_[0]
            elif op == "PhiFunction":
                if len(out) == 1:
                    resolved = _resolve_phi_value(block, instr, table)
                    if resolved is not None:
                        local[out[0]] = resolved
            elif len(out) == 1:
                operands = [arg if is_literal(arg) else local.get(arg) for arg in in_]
                if all(operand is not None for operand in operands):
                    resolved = _evaluate_arithmetic(op, operands)
                    if resolved is not None:
                        local[out[0]] = resolved
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


def _reachable_block_ids(blocks: List[Dict[str, Any]], entry_id: Optional[block_id_T] = None) -> Set[block_id_T]:
    """
    Every block id reachable from the scope's entry using each block's *folded* exit
    (_fold_conditional_exit, via _literal_value_table) rather than its raw one -- a block
    whose only route in was a branch since proven dead (e.g. a revert-only error path behind a
    condition that's now provably always false) is unreachable here even though it's still
    physically present in the raw block list, exactly like it would be at runtime. Used to tell
    genuinely-excluded dead code apart from a real matching failure -- see _merge_trivial_blocks
    and extract_seed_facts_for_contract.
    """
    if not blocks:
        return set()
    entry_id = entry_id if entry_id is not None else blocks[0]["id"]
    literal_table = _literal_value_table(blocks, entry_id)
    by_id = {block["id"]: block for block in blocks}

    reachable = {entry_id}
    frontier = [entry_id]
    while frontier:
        current = frontier.pop()
        folded_exit = _fold_conditional_exit(by_id[current], literal_table.get(current, {}))
        for successor in folded_exit.get("targets", []) or []:
            if successor in by_id and successor not in reachable:
                reachable.add(successor)
                frontier.append(successor)
    return reachable


def _merge_trivial_blocks(blocks: List[Dict[str, Any]],
                          entry_id: Optional[block_id_T] = None) -> List[Dict[str, Any]]:
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

    A working block that's become unreachable from the entry (_reachable_block_ids) -- a dead
    branch target whose only route in was just folded away, e.g. a revert-only error path behind
    a condition proven always-false -- is dropped from the result entirely, on both sides
    independently, rather than kept around as an orphan `_match_scope` could never have a
    predecessor propose a correspondence for regardless of whether it happens to still look
    identical on both sides: dead code can never contribute a live fact either way, so there is
    nothing to gain by attempting to match it and no reason to warn about failing to.
    """
    if not blocks:
        return []

    entry_id = entry_id if entry_id is not None else blocks[0]["id"]
    literal_table = _literal_value_table(blocks, entry_id)
    by_id = {block["id"]: block for block in blocks}
    order = [block["id"] for block in blocks]

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

    reachable = _reachable_block_ids(blocks, entry_id)
    working_blocks = []
    for block_id in order:
        if block_id not in work or block_id not in reachable:
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


def _match_scope(baseline_blocks: List[Dict[str, Any]], probe_blocks: List[Dict[str, Any]],
                 baseline_entry_id: Optional[block_id_T] = None, probe_entry_id: Optional[block_id_T] = None,
                 probe_defs: Optional[Dict[var_id_T, Dict[str, Any]]] = None) -> \
        Tuple[Dict[block_id_T, block_id_T], Dict[block_id_T, var_map_T], Dict[block_id_T, Dict[int, Dict[var_id_T, constant_T]]]]:
    """
    One forward-BFS walk over a scope's blocks that resolves block correspondence and
    instruction-level facts together (see the module docstring for why these can't be two
    separate passes any more): the scope's shared entry block (baseline_entry_id/probe_entry_id,
    defaulting to position 0 in each list -- the same convention _block_processing_order relies
    on -- when not given) anchors the walk; each further block's correspondence is proposed by
    its already-resolved predecessors via
    _propose_successor_mapping, using each predecessor's own confirmed var_map (for the branch-
    condition check) -- a block is left unresolved if none of its predecessors are resolved yet
    (e.g. reachable only via a loop back edge, or via a predecessor that itself never resolved),
    or if its predecessors propose more than one distinct probe counterpart, mirroring the
    "unique candidate or nothing" rule used everywhere else in this module. Once resolved, a
    block's PhiFunctions are realigned by predecessor identity (_reorder_phi_args) and its
    instructions matched (match_block_instructions), seeded with every resolved non-backward
    predecessor's var_map merged together (a predecessor disagreement about a shared variable
    drops that variable from the seed rather than guessing).

    probe_defs (_scope_defining_instructions over probe_blocks) is threaded through to both
    _propose_successor_mapping and match_block_instructions, so a conflicting argument that's a
    rematerialized recomputation of an already-confirmed value is still recognized
    (_values_provably_equal) rather than leaving the block unresolved.

    Returns (block_correspondence, var_maps_by_block, facts_by_block) -- facts_by_block only
    contains entries for blocks that actually produced at least one fact.

    This does not, and cannot, protect against every kind of mismatch: a silent single-block
    disappearance inside an otherwise-uniform chain (no branching to create an observable
    ambiguity) still resolves to a confident but unhelpful pairing -- see PROGRESS.md's
    StackCompressor finding, which is the actual fix for that class.
    """
    if not baseline_blocks or not probe_blocks:
        return {}, {}, {}

    baseline_entry_id = baseline_entry_id if baseline_entry_id is not None else baseline_blocks[0]["id"]
    probe_entry_id = probe_entry_id if probe_entry_id is not None else probe_blocks[0]["id"]

    baseline_by_id = {block["id"]: block for block in baseline_blocks}
    probe_by_id = {block["id"]: block for block in probe_blocks}
    predecessors = _predecessors(baseline_blocks)

    block_correspondence: Dict[block_id_T, block_id_T] = {baseline_entry_id: probe_entry_id}
    var_maps_by_block: Dict[block_id_T, var_map_T] = {}
    facts_by_block: Dict[block_id_T, Dict[int, Dict[var_id_T, constant_T]]] = {}

    for block_id in _block_processing_order(baseline_blocks, baseline_entry_id):
        baseline_block = baseline_by_id[block_id]

        if block_id not in block_correspondence:
            candidates = set()
            for predecessor_id in predecessors.get(block_id, []):
                predecessor_var_map = var_maps_by_block.get(predecessor_id)
                predecessor_probe_id = block_correspondence.get(predecessor_id)
                if predecessor_var_map is None or predecessor_probe_id is None:
                    continue  # not yet processed -- e.g. reachable only via a loop back edge
                proposed = _propose_successor_mapping(
                    baseline_by_id[predecessor_id], probe_by_id.get(predecessor_probe_id), predecessor_var_map,
                    probe_defs)
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
            baseline_block.get("instructions", []), probe_instructions, seed_var_map=seed_var_map,
            probe_defs=probe_defs)
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

    Resolves each scope's real entry block (_scope_entry_id) once here and threads it through
    every call that needs one, rather than letting each of them re-derive/assume it positionally.
    Also computes probe_defs (_scope_defining_instructions over the working probe blocks) once
    per scope and threads it into _match_scope, so a probe argument that's a rematerialized
    recomputation of an already-confirmed value is recognized rather than leaving a block
    unresolved (_values_provably_equal).
    """
    facts: seed_facts_T = {}

    baseline_scopes = dict(iter_block_scopes(baseline_yul_cfg))
    probe_scopes = dict(iter_block_scopes(probe_yul_cfg))

    for scope_path, baseline_blocks in baseline_scopes.items():
        probe_blocks = probe_scopes.get(scope_path)
        if probe_blocks is None:
            logging.warning(f"Scope {scope_path} is missing from the probe compilation; skipping")
            continue

        baseline_entry_id = _scope_entry_id(baseline_yul_cfg, scope_path, baseline_blocks)
        probe_entry_id = _scope_entry_id(probe_yul_cfg, scope_path, probe_blocks)

        working_baseline = _merge_trivial_blocks(baseline_blocks, baseline_entry_id)
        working_probe = _merge_trivial_blocks(probe_blocks, probe_entry_id)
        working_baseline_by_id = {block["id"]: block for block in working_baseline}
        probe_defs = _scope_defining_instructions(working_probe)

        block_correspondence, _, facts_by_block = _match_scope(
            working_baseline, working_probe, baseline_entry_id, probe_entry_id, probe_defs)

        resolved_original_ids: set = set()
        for working_id in block_correspondence:
            resolved_original_ids |= working_baseline_by_id[working_id]["_members"]

        reachable_baseline_ids = _reachable_block_ids(baseline_blocks, baseline_entry_id)
        for block in baseline_blocks:
            if block["id"] not in resolved_original_ids and block["id"] in reachable_baseline_ids:
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
