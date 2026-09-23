"""
Propagates the "seed" constancy facts discovered in src/constancy/seed_extraction.py into a
per-instruction constancy annotation for every block of a parsed CFG, following the rules
from CLAUDE.md:
  - a variable known to be constant stays constant until it becomes dead (its last use in
    the block, or the end of the block if it is live-out);
  - a PhiFunction only propagates a constant for its output if *all* of its inputs resolve
    to the exact same constant value, otherwise no information is inferred;
  - the whole analysis is syntactic and block-by-block: a block only needs the (already
    computed) exit-constants of its predecessors, not a CFG-wide fixpoint.

This intentionally does not reuse the liveness fixpoint machinery in src/analysis/ and
src/liveness/ (BackwardsAnalysis, etc.): blocks are processed in a single forward pass in a
simple BFS order from the block list's start block. A predecessor reachable only through a
back edge (loop) is treated as "not yet known" (empty state) rather than iterating to a
fixpoint -- conservative for the rare case of a phi combining a value carried around a loop,
but keeps the analysis simple, as required by CLAUDE.md's conventions.

Before processing a block, `_seed_facts_conflict_internally` pre-scans its seed facts for any
internal disagreement (two different values for the same variable, or a value that disagrees
with a direct LiteralAssignment elsewhere in the block) and, if found, discards *all* seed
facts for that block rather than just the one variable a conflict happens to surface. A block
mismatch between the baseline and probe compilations (see seed_extraction.py's module
docstring) can produce several wrong facts from the same block at once; without this, only the
one variable with a direct anchor to conflict against would be caught, leaving every other
wrong fact from that same unreliable pairing trusted with no scrutiny at all.
"""
import logging
from collections import defaultdict
from typing import Dict, List, Optional, Set, Tuple

from constancy.seed_extraction import is_literal, scope_path_T, seed_facts_T
from global_params.types import block_id_T, constant_T, var_id_T
from parser.cfg import CFG
from parser.cfg_block import CFGBlock
from parser.cfg_block_list import CFGBlockList
from parser.parser import generate_block_name

# Facts for a single block: instruction index -> {var: literal}
block_seed_facts_T = Dict[int, Dict[var_id_T, constant_T]]

# Known-constant map at the exit of a block: var -> literal
exit_constants_T = Dict[var_id_T, constant_T]

# The constancy annotation for a single instruction: {var: literal}, one per program point
instruction_constancy_T = Dict[var_id_T, constant_T]


def _resolve_phi_input(value: var_id_T, predecessor_id: Optional[block_id_T],
                       predecessor_constants: Dict[block_id_T, exit_constants_T]) -> Optional[constant_T]:
    """
    Resolves a single phi input to a constant value, if known: directly if it is already a
    literal, otherwise by looking up the predecessor block's exit-constants
    """
    if is_literal(value):
        return value
    if predecessor_id is None:
        return None
    return predecessor_constants.get(predecessor_id, {}).get(value)


def _predecessor_consensus(resolve_for_predecessor, predecessors: List[block_id_T]) -> \
        Tuple[Optional[constant_T], bool]:
    """
    Used only by the live-in-passthrough pass below (never by PhiFunction input resolution,
    which stays on its own strict aggregation -- see that branch's own comment for why the two
    cases can't share this).

    The single value that every predecessor *that currently resolves to something* agrees on --
    ignoring a predecessor that doesn't (yet) resolve to anything (not yet processed, e.g. the
    back edge of a loop, or otherwise unknown). A variable with no PhiFunction at this block is
    guaranteed by SSA to carry the same value on every incoming edge (solc's own SSA
    construction only omits a phi when a variable has exactly one reaching definition on every
    path, including back edges), so an unprocessed predecessor has nothing to contribute that an
    already-processed one hasn't already settled -- there is nothing to wait for.

    Returns (value, disagreement): value is the agreed value, or None if nothing currently
    resolves; disagreement is True when two predecessors that *do* currently resolve disagree --
    a genuine inconsistency worth logging (under the same SSA guarantee, this can only mean an
    upstream seed-extraction/matching bug), distinct from simply not having enough information
    yet, which stays quiet.
    """
    resolved = {resolve_for_predecessor(p) for p in predecessors}
    known = resolved - {None}
    if len(known) == 1:
        (value,) = known
        return value, False
    return None, len(known) > 1


def _seed_facts_conflict_internally(instructions: List, seed_facts_for_block: block_seed_facts_T) -> bool:
    """
    True if seed_facts_for_block, on its own, already contains a disagreement for some
    variable -- either two different seed-fact values for it, or a seed-fact value that
    disagrees with a direct LiteralAssignment elsewhere in the same block. This is checked up
    front (before the single forward pass below, and independent of any predecessor-provided
    context) because a block-level mismatch between the baseline and probe compilations (e.g.
    a coincidentally-matched block whose true correspondence was lost -- see
    seed_extraction.py and PROGRESS.md) can produce several wrong seed facts at once; today's
    per-variable conflict check in _record only ever catches the one variable that happens to
    have a direct anchor to conflict against, leaving every other wrong fact from that same
    (evidently unreliable) block trusted with no further scrutiny. When this is true, the
    caller discards every seed fact for the block rather than just the one that collided.
    """
    literal_values: Dict[var_id_T, constant_T] = {
        instr.get_out_args()[0]: instr.get_in_args()[0]
        for instr in instructions if instr.get_op_name() == "LiteralAssignment"
    }

    seed_values: Dict[var_id_T, Set[constant_T]] = defaultdict(set)
    for var_facts in seed_facts_for_block.values():
        for var, value in var_facts.items():
            seed_values[var].add(value)

    for var, values in seed_values.items():
        if len(values) > 1:
            return True
        if var in literal_values and literal_values[var] not in values:
            return True

    return False


def compute_block_constancy(block: CFGBlock, seed_facts_for_block: block_seed_facts_T,
                            predecessor_constants: Optional[Dict[block_id_T, exit_constants_T]] = None,
                            predecessors: Optional[List[block_id_T]] = None) -> \
        Tuple[List[instruction_constancy_T], exit_constants_T]:
    """
    Computes the per-instruction constancy list for a single block (excluding the synthetic
    "functionReturn" CFGBlock._process_instructions_from_function_return appends for a
    FunctionReturn exit -- that instruction never appears in the raw JSON's "instructions" array,
    and its returned variables are always already part of block.liveness["out"] by construction,
    so dropping it loses no information), plus the subset of known constants that are still live
    at the block's exit (for the caller to pass on as predecessor_constants to successors).

    seed_facts_for_block gives, per instruction index, the {var: literal} facts discovered
    for that instruction by the seed extraction pass; predecessor_constants gives, per
    already-processed predecessor block id, the constants known at *its* exit.

    predecessors is the block's real graph predecessors (used for the live-in passthrough pass
    below), deliberately kept separate from block.entries: solc's own yulCFGJson only populates
    a block's "entries" field when it actually contains a PhiFunction (see parser.parser.
    process_block_entry), so it's empty for the common case of a plain block with a single
    predecessor -- entries stays reserved for what it already correctly does, mapping each
    PhiFunction's inputs to the predecessor edge they came from, in that solc-provided order.

    Length is len(instructions) - leading_phi_count + 1, not unconditionally + 1
    (seed_extraction.count_leading_phis): every PhiFunction in a block resolves in parallel with
    the others based on which predecessor edge was actually taken, before any real instruction
    runs, and -- since a block's PhiFunctions are always a leading prefix -- they never get their
    own separate slot the way an ordinary sequential instruction does; they're absorbed entirely
    into the leading live-in slot (index 0). Entry i (i >= 1) is the state immediately after the
    i-th *real* (non-phi) instruction runs.
    """
    predecessor_constants = predecessor_constants or {}
    instructions = [instr for instr in block.get_instructions() if instr.get_op_name() != "functionReturn"]
    out_live = set(block.liveness.get("out", []))

    if _seed_facts_conflict_internally(instructions, seed_facts_for_block):
        logging.warning(f"Seed facts for block {block.get_block_id()} disagree with each other or with a "
                        f"direct LiteralAssignment; discarding all of them for this block")
        seed_facts_for_block = {}

    # Mirrors seed_extraction.count_leading_phis, but over parsed CFGInstruction objects rather
    # than raw yulCFGJson dicts -- the two representations don't share an interface, so this
    # can't just call that helper directly.
    leading_phi_count = 0
    for instr in instructions:
        if instr.get_op_name() != "PhiFunction":
            break
        leading_phi_count += 1

    def result_index(raw_idx: int) -> int:
        # -1 (live-in) and any leading-phi position both collapse to the live-in slot (0) --
        # nothing meaningfully happens until the first real instruction runs
        return max(raw_idx - leading_phi_count + 1, 0)

    known: Dict[var_id_T, constant_T] = {}
    definition_idx: Dict[var_id_T, int] = {}
    last_use_idx: Dict[var_id_T, int] = {}

    for idx, instr in enumerate(instructions):
        for in_arg in instr.get_in_args():
            if not is_literal(in_arg):
                last_use_idx[in_arg] = idx

    def _record(var: var_id_T, value: constant_T) -> None:
        existing = known.get(var)

        if existing is not None and existing != value:
            logging.warning(f"Conflicting constant value for {var} in block {block.get_block_id()}: "
                            f"{existing} vs {value}")
            return
        known[var] = value

    for idx, instr in enumerate(instructions):
        op = instr.get_op_name()
        out_args = instr.get_out_args()

        if op == "LiteralAssignment":
            out_var = out_args[0]
            definition_idx[out_var] = idx
            _record(out_var, instr.get_in_args()[0])

        elif op == "PhiFunction":
            out_var = out_args[0]
            # Deliberately not recorded in definition_idx (unlike every other kind of
            # instruction): every PhiFunction in a block resolves in parallel with the others,
            # selecting a value based on whichever predecessor edge was actually taken, before
            # any real instruction in the block runs -- matching liveness.in, which already
            # lists every phi output as live-in rather than as an in-block-only definition.
            # Leaving it unset makes definition_idx.get(var, -1) default to -1 below, i.e.
            # "already known from the live-in slot", exactly like any other live-in variable.

            fact = seed_facts_for_block.get(idx, {}).get(out_var)
            if fact is not None:
                _record(out_var, fact)
            else:
                resolved = {_resolve_phi_input(in_arg, predecessor_id, predecessor_constants)
                           for in_arg, predecessor_id in zip(instr.get_in_args(), block.entries)}
                if len(resolved) == 1:
                    (value,) = resolved
                    if value is not None:
                        _record(out_var, value)

        else:
            for out_var in out_args:
                definition_idx.setdefault(out_var, idx)
            for var, value in seed_facts_for_block.get(idx, {}).items():
                _record(var, value)

    # A live-in variable with no PhiFunction of its own (the common case: a single
    # predecessor, or a merge where SSA never needed to rename it) still carries whatever
    # value its predecessors already agreed was constant at their exit. Resolved from whichever
    # predecessors are *already processed* (_predecessor_consensus), not requiring all of them:
    # a predecessor reachable only through a not-yet-processed back edge (this pipeline makes a
    # single forward pass, never revisiting a block) is guaranteed by SSA to agree once it is
    # processed anyway, so there's nothing to wait for. Only fills in what the loop above left
    # unresolved, so a direct seed fact or an explicit PhiFunction keeps priority, matching the
    # PhiFunction branch's own precedent.
    phi_outputs = {instr.get_out_args()[0] for instr in instructions if instr.get_op_name() == "PhiFunction"}
    for var in block.liveness.get("in", []):
        if var in known or var in phi_outputs:
            continue
        value, disagreement = _predecessor_consensus(
            lambda predecessor_id, var=var: _resolve_phi_input(var, predecessor_id, predecessor_constants),
            predecessors or [])
        if disagreement:
            logging.warning(f"Predecessors of block {block.get_block_id()} disagree on live-in variable "
                            f"{var}, which has no PhiFunction of its own here; this should be impossible "
                            f"under SSA and likely indicates an upstream seed-extraction/matching bug")
        elif value is not None:
            _record(var, value)

    # A known-constant variable is reported at every program point where it is both known
    # and (per a simple in-block last-use scan, or block-exit liveness) still live. result[0]
    # is the leading live-in slot (state before any real instruction runs, absorbing every
    # leading PhiFunction); result[i] for i >= 1 is the state immediately after the i-th real
    # instruction runs -- see result_index above for the raw-instruction-index -> array-index
    # mapping that accounts for the leading phis not getting their own slot.
    result: List[instruction_constancy_T] = [{} for _ in range(len(instructions) - leading_phi_count + 1)]

    for var, value in known.items():
        start = result_index(definition_idx.get(var, -1))  # -1 for live-in variables, already constant on entry
        if var in out_live:
            end_raw = len(instructions) - 1
        else:
            end_raw = last_use_idx.get(var)
        if end_raw is None:
            continue  # defined but never used in-block and not live-out: never appears

        end = result_index(end_raw)
        if end < start:
            continue

        for i in range(start, end + 1):
            result[i][var] = value

    exit_constants = {var: value for var, value in known.items() if var in out_live}

    block.set_constancy(result)
    return result, exit_constants


def _block_processing_order(block_list: CFGBlockList) -> List[block_id_T]:
    """
    A simple forward BFS order from the block list's start block, so that (in the common,
    loop-free case) every predecessor is processed before its successors. A block reachable
    only through a back edge may still be unprocessed when a successor first needs it -- see
    compute_block_constancy, which simply treats an unknown predecessor as carrying no
    known constants
    """
    graph = block_list.to_graph()
    order: List[block_id_T] = []
    visited: Set[block_id_T] = set()
    queue = [block_list.start_block]

    while queue:
        node = queue.pop(0)
        if node in visited:
            continue
        visited.add(node)
        order.append(node)
        queue.extend(succ for succ in graph.successors(node) if succ not in visited)

    # Blocks unreachable from the start block (shouldn't normally happen) are appended last
    for block_id in block_list.get_blocks_dict():
        if block_id not in visited:
            order.append(block_id)

    return order


def compute_constancy_for_block_list(block_list: CFGBlockList,
                                     seed_facts_by_block: Dict[block_id_T, block_seed_facts_T]) -> \
        Tuple[Dict[block_id_T, List[instruction_constancy_T]], Dict[block_id_T, exit_constants_T]]:
    """
    Computes constancy for every block in a block list, in an order where a predecessor is
    (whenever possible) processed before its successors
    """
    constancy_per_block = {}
    exit_constants_per_block: Dict[block_id_T, exit_constants_T] = {}
    graph = block_list.to_graph()

    for block_id in _block_processing_order(block_list):
        block = block_list.get_block(block_id)
        predecessors = list(graph.predecessors(block_id))
        constancy, exit_constants = compute_block_constancy(block, seed_facts_by_block.get(block_id, {}),
                                                             exit_constants_per_block, predecessors)
        constancy_per_block[block_id] = constancy
        exit_constants_per_block[block_id] = exit_constants

    return constancy_per_block, exit_constants_per_block


def _iter_cfg_block_scopes(cfg: CFG, path: scope_path_T = ()):
    """
    Recursively walks a parsed CFG, yielding (scope_path, component_name, block_list) for
    every object's own blocks, each of its functions' blocks, and recursively every nested
    subObject -- mirroring seed_extraction.iter_block_scopes, but over the parsed CFG
    """
    for object_name, cfg_object in cfg.objectCFG.items():
        yield path + (object_name,), object_name, cfg_object.blocks

        for function_name, cfg_function in cfg_object.functions.items():
            yield path + (object_name, function_name), function_name, cfg_function.blocks

        sub_object = cfg_object.get_subobject()
        if sub_object is not None:
            yield from _iter_cfg_block_scopes(sub_object, path + (object_name,))


def group_seed_facts_by_scope(seed_facts: seed_facts_T) -> \
        Dict[scope_path_T, Dict[block_id_T, block_seed_facts_T]]:
    """
    Regroups the flat seed_facts_T produced by seed_extraction.py (keyed by
    (scope_path, raw_block_id, instr_idx, var)) into a nested per-scope, per-block mapping
    ready to feed into compute_constancy_for_block_list
    """
    grouped: Dict[scope_path_T, Dict[block_id_T, block_seed_facts_T]] = defaultdict(lambda: defaultdict(dict))
    for (scope_path, block_id, instr_idx, var), value in seed_facts.items():
        grouped[scope_path][block_id].setdefault(instr_idx, {})[var] = value
    return grouped


def compute_constancy_for_cfg(cfg: CFG, seed_facts: seed_facts_T) -> \
        Dict[Tuple[scope_path_T, block_id_T], List[instruction_constancy_T]]:
    """
    Computes constancy for every block in a parsed CFG (its objects, their functions, and
    recursively every nested subObject), keyed the same way as seed_extraction.py's
    seed_facts_T scope/block identifiers: (scope_path, raw_block_id)
    """
    grouped_facts = group_seed_facts_by_scope(seed_facts)
    result: Dict[Tuple[scope_path_T, block_id_T], List[instruction_constancy_T]] = {}

    for scope_path, component_name, block_list in _iter_cfg_block_scopes(cfg):
        raw_facts_by_block = grouped_facts.get(scope_path, {})
        seed_facts_by_block = {generate_block_name(component_name, raw_block_id): facts
                               for raw_block_id, facts in raw_facts_by_block.items()}

        constancy_per_block, _ = compute_constancy_for_block_list(block_list, seed_facts_by_block)

        for prefixed_block_id, constancy in constancy_per_block.items():
            raw_block_id = prefixed_block_id[len(component_name) + 1:]
            result[(scope_path, raw_block_id)] = constancy

    return result
