"""
Extracts "seed" constancy facts by comparing two compilations of the same contract: one
with a baseline Yul optimizer step sequence, and one with that same sequence plus one extra
application of a step (see libyul/optimiser/Suite.cpp) that can substitute a variable's
already-known value into its use sites -- LiteralRematerialiser ('T'), Rematerialiser ('m'),
CommonSubexpressionEliminator ('c'), or ExpressionSimplifier ('s'), used this way both by
annotate.py's production path and by occurrence_trace.py's wider per-occurrence trace.
Wherever a variable that is still symbolic in the baseline shows up as a plain literal at the
same argument position in the probe compilation, that variable is known to have that constant
value.

Matching instructions between the two compilations by output-variable NAME alone is not safe:
any step that changes an instruction *count* somewhere in a block -- not just 's', which can
eliminate an instruction via an algebraic rewrite, but also 'T'/'m'/'c' when probed at a point
where they interact with a repeating cleanup phase (see PROGRESS.md's dated entries) -- shifts
solc's sequential variable numbering for everything after that point, so two instructions that
happen to produce the same *name* in both compilations can be completely unrelated. A concrete
example found in this project's own investigation: probing 'T' at its own last, most productive
occurrence in the real default sequence produced three different, mutually contradictory values
for the same global SSA variable across three different blocks -- all wrong, because
by-name matching coincidentally re-matched three unrelated instructions in a function that
decodes a struct field-by-field with a repeating instruction pattern.

Instead, `match_block_instructions` walks a block's baseline/probe instruction lists BACKWARD
from the end, unifying a baseline<->probe variable correspondence structurally (same op, same
argument shape, consistent argument-by-argument) rather than by name. A block's live-out
boundary is unaffected by a purely local, per-block rewrite (successor blocks still need the
same values), so instructions near the end of the block are the most reliable place to start;
walking backward from there, a single position where nothing lines up signals a real
divergence rather than a coincidence. When the immediate next position doesn't unify, a small
window of alternate offsets is tried, each confirmed by requiring several further instructions
to also unify consistently (a lookahead, not just one lucky match); a resync is only accepted
when exactly one candidate offset survives this check -- if none or more than one do, the walk
stops there rather than guessing, so what's reported is either correct or absent, never wrong.

Even an immediate-next-position match can introduce a NEW baseline<->probe variable
correspondence that isn't anchored by anything else -- e.g. two operands that merely happen to
sit at the same argument position in an instruction from a periodic/repetitive block (a
struct's fields being zeroed in a loop-free unrolled sequence is a real example -- see
PROGRESS.md). Such a correspondence is only trusted once checked against the very next
instruction, with and without it: if the next instruction unifies fine without it but
contradicts it once it's added, that proves the correspondence was coincidental, and the match
that proposed it is treated as failed (falling through to the resync search above) rather than
silently believed.

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
`_match_blocks_structurally` establishes a baseline<->probe block correspondence from the
scope's shared entry block, propagated via matching CFG-edge shape (exit type + successor
count), rather than assuming equal ids name the same block. This catches genuinely ambiguous
cases, but it cannot catch every one: a real, previously-investigated case (see PROGRESS.md)
turned out to be caused by solc's `StackCompressor` -- a mandatory phase, unrelated to any step
this module is asked to probe, that can duplicate or restructure large amounts of code to
resolve "stack too deep" situations, sensitive to stack-pressure differences one extra step can
introduce. Since the resulting block-count shift can happen inside an otherwise-uniform,
single-predecessor chain, it produces no observable ambiguity for any purely local block
matcher (id-based or structural) to catch -- `with_stack_allocation_disabled` (below) is the
actual fix for that class, used by isolated probing callers (`occurrence_trace.py`,
`annotate_single_step.py` via `extract_seed_facts`'s `disable_stack_allocation` parameter).
"""
import copy
import logging
from collections import defaultdict
from typing import Any, Dict, List, Optional, Tuple

import networkx as nx

from execution.sol_compilation import SolidityCompilation, DEFAULT_OPTIMIZER_SEQUENCE, get_yul_details
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

# Default tuning for match_block_instructions -- see its docstring
DEFAULT_LOOKAHEAD = 3
DEFAULT_RESYNC_WINDOW = 4


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


def _confirm_resync(baseline_instrs: List[Dict[str, Any]], probe_instrs: List[Dict[str, Any]],
                    baseline_idx: int, probe_idx: int, var_map: var_map_T, lookahead: int) -> \
        Optional[Tuple[var_map_T, Dict[int, Dict[var_id_T, constant_T]], int, int]]:
    """
    Confirms a candidate resync point: checks that baseline_idx/probe_idx, and the `lookahead`
    instructions before them continuing the backward walk, all unify consistently. Returns
    (extended_var_map, facts_by_index, next_baseline_idx, next_probe_idx) covering everything
    consumed by the lookahead if the whole window unifies without contradiction, None otherwise.
    """
    trial_map = dict(var_map)
    facts_by_index: Dict[int, Dict[var_id_T, constant_T]] = {}
    i, j = baseline_idx, probe_idx
    steps = 0

    while steps <= lookahead and i >= 0 and j >= 0:
        result = _try_unify_instructions(baseline_instrs[i], probe_instrs[j], trial_map)
        if result is None:
            return None
        pending, facts = result
        for baseline_var, probe_var in pending:
            trial_map[baseline_var] = probe_var
        if facts:
            facts_by_index[i] = facts
        i -= 1
        j -= 1
        steps += 1

    return trial_map, facts_by_index, i, j


def _contradicted_by_next_instruction(baseline_instrs: List[Dict[str, Any]], probe_instrs: List[Dict[str, Any]],
                                      i: int, j: int, var_map: var_map_T,
                                      result: Tuple[List[Tuple[var_id_T, var_id_T]], Dict[var_id_T, constant_T]]) -> bool:
    """
    Checks whether the match found at (i, j) should be trusted: a NEW baseline<->probe variable
    correspondence it proposes (one not already in var_map) is only trustworthy if it doesn't
    immediately conflict with the very next instruction. Compares that next instruction with
    and without the new correspondence added -- if it unifies fine without but contradicts with,
    the correspondence was coincidental (see the module docstring's periodic-block example), and
    the caller should treat (i, j) as if it hadn't unified at all rather than trust it.
    """
    pending, _ = result
    new_vars = [baseline_var for baseline_var, _ in pending if baseline_var not in var_map]
    if not new_vars or i - 1 < 0 or j - 1 < 0:
        return False

    without_new_vars = _try_unify_instructions(baseline_instrs[i - 1], probe_instrs[j - 1], var_map) is not None

    trial_map = dict(var_map)
    for baseline_var, probe_var in pending:
        trial_map[baseline_var] = probe_var
    with_new_vars = _try_unify_instructions(baseline_instrs[i - 1], probe_instrs[j - 1], trial_map) is not None

    return without_new_vars and not with_new_vars


def match_block_instructions(baseline_instrs: List[Dict[str, Any]], probe_instrs: List[Dict[str, Any]],
                             seed_var_map: Optional[var_map_T] = None,
                             lookahead: int = DEFAULT_LOOKAHEAD,
                             resync_window: int = DEFAULT_RESYNC_WINDOW) -> \
        Tuple[Dict[int, Dict[var_id_T, constant_T]], var_map_T]:
    """
    Matches a block's baseline instructions against its probe instructions by walking both
    lists backward from the end (see the module docstring for the rationale), returning
    ({baseline_instruction_index: {var: literal}}, confirmed_var_map). seed_var_map primes the
    correspondence with facts already confirmed elsewhere (e.g. by a dominating predecessor
    block) -- both as extra context and as a consistency check: a local match that would
    contradict a seeded correspondence is rejected exactly like any other inconsistency.
    """
    var_map: var_map_T = dict(seed_var_map or {})
    facts: Dict[int, Dict[var_id_T, constant_T]] = defaultdict(dict)
    i, j = len(baseline_instrs) - 1, len(probe_instrs) - 1

    while i >= 0 and j >= 0:
        result = _try_unify_instructions(baseline_instrs[i], probe_instrs[j], var_map)
        if result is not None and _contradicted_by_next_instruction(baseline_instrs, probe_instrs, i, j,
                                                                     var_map, result):
            result = None

        if result is not None:
            pending, step_facts = result
            for baseline_var, probe_var in pending:
                var_map[baseline_var] = probe_var
            if step_facts:
                facts[i].update(step_facts)
            i -= 1
            j -= 1
            continue

        candidates = []
        for delta in range(1, resync_window + 1):
            for candidate_j in (j - delta, j + delta):
                if not (0 <= candidate_j < len(probe_instrs)):
                    continue
                outcome = _confirm_resync(baseline_instrs, probe_instrs, i, candidate_j, var_map, lookahead)
                if outcome is not None:
                    candidates.append(outcome)

        if len(candidates) != 1:
            break  # no resync point, or more than one equally plausible -- stop, don't guess

        var_map, resync_facts, i, j = candidates[0]
        for idx, idx_facts in resync_facts.items():
            facts[idx].update(idx_facts)

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


def _propose_successor_mapping(baseline_block: Dict[str, Any],
                               probe_block: Optional[Dict[str, Any]]) -> Dict[block_id_T, block_id_T]:
    """
    Proposes a baseline->probe successor-block correspondence from one already-confirmed block
    pairing: valid only if both blocks' exit shape agrees (same exit type, same number of
    targets), in which case corresponding successors are read positionally off each block's own
    (raw JSON, solc-ordered) targets list. Returns {} if the shape disagrees or probe_block is
    unknown -- contributing no candidate rather than a wrong one.
    """
    if probe_block is None:
        return {}
    if baseline_block.get("exit", {}).get("type") != probe_block.get("exit", {}).get("type"):
        return {}
    baseline_targets, probe_targets = _successors(baseline_block), _successors(probe_block)
    if len(baseline_targets) != len(probe_targets):
        return {}
    return dict(zip(baseline_targets, probe_targets))


def _match_blocks_structurally(baseline_blocks: List[Dict[str, Any]],
                               probe_blocks: List[Dict[str, Any]]) -> Dict[block_id_T, block_id_T]:
    """
    Baseline->probe block correspondence for one scope, established structurally rather than by
    trusting equal raw ids (see the module docstring): the scope's shared entry block (position
    0 in both lists, the same convention _block_dominance_order relies on) anchors the walk, and
    each further block's correspondence is proposed by its already-resolved predecessors via
    _propose_successor_mapping. A block is left unresolved (absent from the result) if none of
    its predecessors are resolved yet, or if its predecessors propose more than one distinct
    probe counterpart -- mirroring the "unique candidate or nothing" rule already used for
    instruction matching and cross-block variable seeding.

    This does not, and cannot, protect against every kind of mismatch: a silent single-block
    disappearance inside an otherwise-uniform chain (no branching to create an observable
    ambiguity) still resolves to a confident but unhelpful pairing -- see PROGRESS.md's
    StackCompressor finding, which is the actual fix for that class.
    """
    if not baseline_blocks or not probe_blocks:
        return {}

    predecessors = _predecessors(baseline_blocks)
    baseline_by_id = {block["id"]: block for block in baseline_blocks}
    probe_by_id = {block["id"]: block for block in probe_blocks}
    correspondence: Dict[block_id_T, block_id_T] = {baseline_blocks[0]["id"]: probe_blocks[0]["id"]}

    for block_id in _block_dominance_order(baseline_blocks):
        if block_id in correspondence:
            continue
        candidates = set()
        for predecessor_id in predecessors.get(block_id, []):
            predecessor_probe_id = correspondence.get(predecessor_id)
            if predecessor_probe_id is None:
                continue
            proposed = _propose_successor_mapping(baseline_by_id[predecessor_id], probe_by_id.get(predecessor_probe_id))
            if block_id in proposed:
                candidates.add(proposed[block_id])
        if len(candidates) == 1:
            correspondence[block_id] = candidates.pop()

    return correspondence


def extract_seed_facts_for_contract(baseline_yul_cfg: Yul_CFG_T, probe_yul_cfg: Yul_CFG_T) -> seed_facts_T:
    """
    Walks every block scope shared between the baseline and probe yulCFGJson of the same
    contract and extracts all seed facts, processing each scope's blocks in dominance order so
    a block's matcher can be seeded with the variable correspondences its already-processed
    predecessors confirmed (see the module docstring).
    """
    facts: seed_facts_T = {}

    baseline_scopes = dict(iter_block_scopes(baseline_yul_cfg))
    probe_scopes = dict(iter_block_scopes(probe_yul_cfg))

    for scope_path, baseline_blocks in baseline_scopes.items():
        probe_blocks = probe_scopes.get(scope_path)
        if probe_blocks is None:
            logging.warning(f"Scope {scope_path} is missing from the probe compilation; skipping")
            continue

        block_correspondence = _match_blocks_structurally(baseline_blocks, probe_blocks)
        baseline_blocks_by_id = {block["id"]: block for block in baseline_blocks}
        probe_blocks_by_id = {block["id"]: block for block in probe_blocks}
        predecessors = _predecessors(baseline_blocks)
        var_maps_by_block: Dict[block_id_T, var_map_T] = {}

        for block_id in _block_dominance_order(baseline_blocks):
            probe_block = probe_blocks_by_id.get(block_correspondence.get(block_id))
            if probe_block is None:
                logging.warning(f"Block {block_id} in scope {scope_path} has no unique structural "
                                f"correspondence in the probe compilation; skipping")
                continue
            baseline_block = baseline_blocks_by_id[block_id]

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

            block_facts, block_var_map = match_block_instructions(
                baseline_block.get("instructions", []), probe_block.get("instructions", []),
                seed_var_map=seed_var_map)
            var_maps_by_block[block_id] = block_var_map

            for instr_idx, var_facts in block_facts.items():
                for var, value in var_facts.items():
                    facts[(scope_path, block_id, instr_idx, var)] = value

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


def extract_seed_facts(json_input: Dict[str, Any], solc_executable: str = "solc",
                       base_sequence: str = DEFAULT_OPTIMIZER_SEQUENCE,
                       steps_to_consider: List[str] = CONSTANT_PROPAGATING_STEPS,
                       disable_stack_allocation: bool = False) -> \
        Optional[Tuple[Dict[str, Yul_CFG_T], Dict[str, Yul_CFG_T], Dict[str, seed_facts_T]]]:
    """
    Compiles json_input with the baseline sequence and with the baseline sequence plus an
    extra application of steps_to_consider, then extracts the seed facts discovered for
    every contract. Returns None if either compilation fails.

    The baseline compilation (first element of the returned tuple) is the yulCFGJson meant
    to be kept/annotated; the probe compilation is only used to discover facts. It is returned
    as the second argument for debugging purposes. base_sequence is isolated (see
    isolate_cleanup_sequence) before compiling, so baseline and probe share an identical,
    explicitly-delimited prefix -- a no-op for the production DEFAULT_OPTIMIZER_SEQUENCE
    default, which already has its own real colon.

    disable_stack_allocation, when True, forces solc's StackCompressor off for both compiles
    (see with_stack_allocation_disabled() above) -- intended for isolated single-step probing
    (annotate_single_step.py), not the production default: forcing it there would change the
    kept baseline's actual compiled shape, not just how facts are discovered about it, which is
    a bigger and separate decision from this function's own job.
    """
    prepared_input = with_stack_allocation_disabled(json_input) if disable_stack_allocation else json_input
    baseline_cfg = SolidityCompilation.from_json_input(copy.deepcopy(prepared_input),
                                                       optimizer_steps=isolate_cleanup_sequence(base_sequence),
                                                       solc_executable=solc_executable)
    probe_cfg = SolidityCompilation.from_json_input(copy.deepcopy(prepared_input),
                                                    optimizer_steps=probe_sequence(base_sequence, steps_to_consider),
                                                    solc_executable=solc_executable)

    if baseline_cfg is None or probe_cfg is None:
        logging.warning("Compilation failed while extracting constancy seed facts")
        return None

    seed_facts_per_contract = {}
    for contract_name, baseline_yul_cfg in baseline_cfg.items():
        probe_yul_cfg = probe_cfg.get(contract_name)
        if probe_yul_cfg is None:
            logging.warning(f"Contract {contract_name} is missing from the probe compilation; skipping")
            continue
        seed_facts_per_contract[contract_name] = extract_seed_facts_for_contract(baseline_yul_cfg, probe_yul_cfg)

    return baseline_cfg, probe_cfg, seed_facts_per_contract
