from parser.cfg_block import CFGBlock
from parser.cfg_block_list import CFGBlockList
from parser.cfg_instruction import CFGInstruction

from constancy.propagation import compute_block_constancy, compute_constancy_for_block_list


def make_instr(op, in_args, out_args):
    return CFGInstruction(op, list(in_args), list(out_args))


def make_block(block_id, instructions, liveness_in=None, liveness_out=None, entries=None):
    block = CFGBlock(block_id, instructions, "BuiltinCall", {})
    block.set_liveness({"in": liveness_in or [], "out": liveness_out or []})
    block.entries = entries or []
    return block


class TestStraightLineLiteral:
    def test_constant_propagates_until_last_use_then_dies(self):
        block = make_block("B1", [
            make_instr("LiteralAssignment", ["0x20"], ["v0"]),
            make_instr("add", ["v1", "v0"], ["v2"]),
            make_instr("mstore", ["v1", "v2"], []),
        ], liveness_in=["v1"])

        constancy, exit_constants = compute_block_constancy(block, {})

        assert constancy[0] == {}  # v0 not yet defined: live-in slot
        assert constancy[1] == {"v0": "0x20"}  # after instruction 0 (the LiteralAssignment)
        assert constancy[2] == {"v0": "0x20"}  # after instruction 1, its last use
        assert constancy[3] == {}  # dead: no further use, not live-out
        assert exit_constants == {}

    def test_result_is_also_stored_on_the_block(self):
        block = make_block("B1", [make_instr("LiteralAssignment", ["0x20"], ["v0"])])

        constancy, _ = compute_block_constancy(block, {})

        assert block.get_constancy() == constancy


class TestSeedFacts:
    def test_seed_fact_confirms_a_non_literal_defined_variable(self):
        # v9 is used but not defined in this block (e.g. defined via a non-trivial
        # expression solc's own optimizer proved constant); the fact is only recorded at
        # the instruction that uses it
        block = make_block("B3", [make_instr("mstore", ["v9", "0x00"], [])], liveness_in=["v9"])

        constancy, _ = compute_block_constancy(block, {0: {"v9": "0x2a"}})

        # v9 is live-in and not defined in-block, so it's already known from the leading
        # live-in slot, through its last use at instruction 0
        assert constancy[0] == {"v9": "0x2a"}
        assert constancy[1] == {"v9": "0x2a"}

    def test_live_in_constant_confirmed_anywhere_is_known_from_block_entry(self):
        # SSA guarantees v9 never changes value, so once confirmed (here, only at
        # instruction 1) it must be treated as already known from the start of the block
        block = make_block("B5", [
            make_instr("iszero", ["v9"], ["v11"]),
            make_instr("add", ["v9", "0x01"], ["v12"]),
        ], liveness_in=["v9"])

        constancy, _ = compute_block_constancy(block, {1: {"v9": "0x2a"}})

        assert constancy[0] == {"v9": "0x2a"}
        assert constancy[1] == {"v9": "0x2a"}
        assert constancy[2] == {"v9": "0x2a"}  # last use is instruction 1

    def test_variable_with_no_use_and_not_live_out_never_appears(self):
        block = make_block("B6", [
            make_instr("LiteralAssignment", ["0x09"], ["v1"]),
            make_instr("stop", [], []),
        ])

        constancy, exit_constants = compute_block_constancy(block, {})

        assert constancy == [{}, {}, {}]
        assert exit_constants == {}


class TestInternalSeedFactConflict:
    def test_a_conflicting_seed_fact_discards_the_whole_blocks_seed_facts(self):
        # Mirrors a real bug found against a real contract (see PROGRESS.md): a block
        # mismatch between the baseline and probe compilations can produce several wrong seed
        # facts from the same block at once. v0's seed fact (0xff) conflicts with its own
        # direct LiteralAssignment (0x20) -- that alone is already caught by the existing
        # per-variable check -- but v9's seed fact (0x2a) is otherwise perfectly clean, with
        # nothing of its own to conflict against. Once the block is known to be unreliable,
        # v9's fact must be dropped too, not trusted just because it happened not to collide
        block = make_block("B1", [
            make_instr("LiteralAssignment", ["0x20"], ["v0"]),
            make_instr("mstore", ["v9", "0x00"], []),
            make_instr("mstore", ["v0", "0x04"], []),
        ], liveness_in=["v9"])

        constancy, _ = compute_block_constancy(block, {0: {"v0": "0xff"}, 1: {"v9": "0x2a"}})

        assert constancy[0] == {}  # v0 not yet defined: live-in slot
        assert constancy[1] == {"v0": "0x20"}  # unaffected: read directly off the LiteralAssignment
        assert "v9" not in constancy[1]  # discarded, even though nothing of its own conflicted
        assert constancy[2] == {"v0": "0x20"}  # still alive, still correct
        assert constancy[3] == {"v0": "0x20"}  # last use is instruction 2

    def test_two_disagreeing_seed_facts_for_the_same_variable_are_also_caught(self):
        block = make_block("B2", [
            make_instr("mstore", ["v9", "0x00"], []),
            make_instr("mstore", ["v9", "0x04"], []),
            make_instr("mstore", ["v5", "0x08"], []),
        ], liveness_in=["v9", "v5"])

        constancy, _ = compute_block_constancy(block, {0: {"v9": "0x2a"}, 1: {"v9": "0x2b"}, 2: {"v5": "0x99"}})

        assert "v9" not in constancy[0]
        assert "v5" not in constancy[2]  # also discarded, despite being internally consistent


class TestPhiFunction:
    def test_matching_predecessor_constants_propagate(self):
        block = make_block("B2", [
            make_instr("PhiFunction", ["v10", "v20"], ["phi1"]),
            make_instr("mstore", ["phi1", "0x00"], []),
        ], entries=["PredA", "PredB"])

        predecessor_constants = {"PredA": {"v10": "0x2a"}, "PredB": {"v20": "0x2a"}}
        constancy, _ = compute_block_constancy(block, {}, predecessor_constants)

        # phi1 resolves in parallel with the block's other phis (here, just itself), so it's
        # already known at the live-in slot, not staggered to start only after its own position.
        # The phi doesn't get its own array slot either -- length is 2 (live-in + mstore), not 3.
        assert constancy[0] == {"phi1": "0x2a"}
        assert constancy[1] == {"phi1": "0x2a"}

    def test_conflicting_predecessor_constants_infer_nothing(self):
        block = make_block("B2", [
            make_instr("PhiFunction", ["v10", "v20"], ["phi1"]),
            make_instr("mstore", ["phi1", "0x00"], []),
        ], entries=["PredA", "PredB"])

        predecessor_constants = {"PredA": {"v10": "0x2a"}, "PredB": {"v20": "0x2b"}}
        constancy, _ = compute_block_constancy(block, {}, predecessor_constants)

        assert constancy[0] == {}
        assert constancy[1] == {}

    def test_unresolved_predecessor_infers_nothing(self):
        # PredB hasn't been processed yet (e.g. reachable only through a loop back edge). The
        # block is just the one phi and no real instructions, so constancy is length 1 (just the
        # live-in slot).
        block = make_block("B2", [make_instr("PhiFunction", ["v10", "v20"], ["phi1"])],
                           entries=["PredA", "PredB"])

        constancy, _ = compute_block_constancy(block, {}, {"PredA": {"v10": "0x2a"}})

        assert constancy[0] == {}

    def test_literal_phi_input_resolves_directly(self):
        block = make_block("B2", [
            make_instr("PhiFunction", ["0x2a", "v20"], ["phi1"]),
            make_instr("mstore", ["phi1", "0x00"], []),
        ], entries=["PredA", "PredB"])

        constancy, _ = compute_block_constancy(block, {}, {"PredB": {"v20": "0x2a"}})

        # already known at the live-in slot, same reasoning as above -- length 2, not 3
        assert constancy[0] == {"phi1": "0x2a"}
        assert constancy[1] == {"phi1": "0x2a"}

    def test_seed_fact_on_phi_output_is_used_directly(self):
        block = make_block("B2", [
            make_instr("PhiFunction", ["v10", "v20"], ["phi1"]),
            make_instr("mstore", ["phi1", "0x00"], []),
        ], entries=["PredA", "PredB"])

        constancy, _ = compute_block_constancy(block, {0: {"phi1": "0x05"}})

        # already known at the live-in slot, same reasoning as above -- length 2, not 3
        assert constancy[0] == {"phi1": "0x05"}
        assert constancy[1] == {"phi1": "0x05"}

    def test_multiple_leading_phis_resolve_in_parallel_and_share_the_live_in_slot(self):
        # Mirrors a real contract (abi_encode_array_uint256's Block1): three leading
        # PhiFunctions followed by one real instruction ("lt"). Every phi resolves at the same
        # program point (the block's live-in state, based purely on which predecessor edge was
        # taken) -- none of them, individually or together, get their own array slot -- so the
        # whole block is exactly two entries: the live-in state (all three phis resolved) and
        # the state after lt runs (that same state plus lt's own new fact, v6).
        block = make_block("B2", [
            make_instr("PhiFunction", ["v10", "v20"], ["phi1"]),
            make_instr("PhiFunction", ["v11", "v21"], ["phi2"]),
            make_instr("PhiFunction", ["v12", "v22"], ["phi3"]),
            make_instr("lt", ["v0", "phi1"], ["v6"]),
        ], entries=["PredA", "PredB"], liveness_out=["phi1", "phi2", "phi3", "v6"])

        predecessor_constants = {
            "PredA": {"v10": "0x2a", "v11": "0x05", "v12": "0x07"},
            "PredB": {"v20": "0x2a", "v21": "0x05", "v22": "0x07"},
        }
        constancy, _ = compute_block_constancy(block, {3: {"v6": "0x99"}}, predecessor_constants)

        resolved_phis = {"phi1": "0x2a", "phi2": "0x05", "phi3": "0x07"}
        assert len(constancy) == 2
        assert constancy[0] == resolved_phis
        assert constancy[1] == {**resolved_phis, "v6": "0x99"}


class TestLiveInPassthrough:
    # predecessors is passed explicitly here (rather than via make_block's entries=), mirroring
    # what compute_constancy_for_block_list derives from the block list's own graph
    # (block_list.to_graph().predecessors(...)): solc's own yulCFGJson "entries" field (which
    # block.entries comes from) is only populated for a block that actually contains a
    # PhiFunction, so it can't be reused for the plain-passthrough case these tests cover.

    def test_single_predecessor_no_phi_carries_the_value_through_unreferenced(self):
        # Mirrors a real bug found against a real contract: a block with a single
        # predecessor and no PhiFunction (the common case -- SSA never needed to rename the
        # variable across that edge) never referencing the live-in variable itself, yet
        # still live-out of it. Nothing in this block's own instructions or seed facts ever
        # mentions v15 -- its only source of truth is predecessor_constants.
        block = make_block("B2", [make_instr("add", ["v1", "v2"], ["v3"])],
                           liveness_in=["v15"], liveness_out=["v15"])

        constancy, exit_constants = compute_block_constancy(block, {}, {"Pred": {"v15": "0x3039"}},
                                                             predecessors=["Pred"])

        assert constancy[0] == {"v15": "0x3039"}
        assert constancy[1] == {"v15": "0x3039"}
        assert exit_constants == {"v15": "0x3039"}

    def test_single_predecessor_no_phi_dies_after_its_last_use(self):
        block = make_block("B2", [make_instr("mstore", ["v15", "0x00"], [])], liveness_in=["v15"])

        constancy, exit_constants = compute_block_constancy(block, {}, {"Pred": {"v15": "0x3039"}},
                                                             predecessors=["Pred"])

        assert constancy[0] == {"v15": "0x3039"}
        assert constancy[1] == {"v15": "0x3039"}  # last use
        assert exit_constants == {}

    def test_two_predecessors_agreeing_on_the_same_variable_name_propagate(self):
        # No phi needed: both predecessors happen to carry the exact same SSA name
        block = make_block("B2", [], liveness_in=["v9"], liveness_out=["v9"])

        predecessor_constants = {"PredA": {"v9": "0x2a"}, "PredB": {"v9": "0x2a"}}
        _, exit_constants = compute_block_constancy(block, {}, predecessor_constants,
                                                     predecessors=["PredA", "PredB"])

        assert exit_constants == {"v9": "0x2a"}

    def test_two_predecessors_disagreeing_infer_nothing(self):
        block = make_block("B2", [], liveness_in=["v9"], liveness_out=["v9"])

        predecessor_constants = {"PredA": {"v9": "0x2a"}, "PredB": {"v9": "0x2b"}}
        _, exit_constants = compute_block_constancy(block, {}, predecessor_constants,
                                                     predecessors=["PredA", "PredB"])

        assert exit_constants == {}

    def test_resolves_from_the_one_processed_predecessor_without_waiting_for_the_other(self):
        # Mirrors the real bug (ERC20_925/clear_storage_range_bytes1/Block6): a block reachable
        # via one already-processed predecessor and one not-yet-processed one (e.g. a loop back
        # edge -- PredB simply isn't a key in predecessor_constants yet). No PhiFunction exists
        # for v9 here, so SSA guarantees PredB would agree once processed anyway -- nothing to
        # wait for.
        block = make_block("B2", [], liveness_in=["v9"], liveness_out=["v9"])

        predecessor_constants = {"PredA": {"v9": "0x2a"}}  # PredB not present: unprocessed
        _, exit_constants = compute_block_constancy(block, {}, predecessor_constants,
                                                     predecessors=["PredA", "PredB"])

        assert exit_constants == {"v9": "0x2a"}

    def test_a_direct_seed_fact_keeps_priority_over_predecessor_resolution(self):
        # v9's own seed fact (discovered directly in this block) disagrees with what
        # predecessor_constants would otherwise resolve -- the main loop's seed-fact value,
        # recorded first, must win rather than being silently replaced by the passthrough pass
        block = make_block("B2", [make_instr("mstore", ["v9", "0x00"], [])], liveness_in=["v9"])

        constancy, _ = compute_block_constancy(block, {0: {"v9": "0x2a"}}, {"Pred": {"v9": "0x2b"}},
                                               predecessors=["Pred"])

        assert constancy[0] == {"v9": "0x2a"}


class TestLiveOut:
    def test_live_out_variable_spans_to_end_of_block(self):
        block = make_block("B4", [
            make_instr("LiteralAssignment", ["0x07"], ["v5"]),
            make_instr("add", ["v5", "v6"], ["v7"]),
        ], liveness_in=["v6"], liveness_out=["v5"])

        constancy, exit_constants = compute_block_constancy(block, {})

        assert constancy[0] == {}  # v5 not yet defined: live-in slot
        assert constancy[1] == {"v5": "0x07"}
        assert constancy[2] == {"v5": "0x07"}
        assert exit_constants == {"v5": "0x07"}


class TestFunctionReturnExit:
    def test_synthetic_function_return_instruction_is_excluded_from_the_result(self):
        # Mirrors what CFGBlock._process_instructions_from_function_return appends for a
        # FunctionReturn exit: a synthetic "functionReturn" instruction that never appears in
        # the raw yulCFGJson block's "instructions" array. The reported constancy list must
        # stay one entry longer than that raw array (one live-in slot, plus one entry per real
        # instruction), not grow by a second one for this synthetic instruction.
        block = make_block("B7", [
            make_instr("LiteralAssignment", ["0x2a"], ["v0"]),
            make_instr("functionReturn", ["v0"], []),
        ], liveness_out=["v0"])

        constancy, exit_constants = compute_block_constancy(block, {})

        assert constancy == [{}, {"v0": "0x2a"}]
        assert exit_constants == {"v0": "0x2a"}

    def test_empty_block_with_only_a_function_return_reports_no_instructions(self):
        block = make_block("B8", [make_instr("functionReturn", ["v0"], [])], liveness_out=["v0"])

        constancy, _ = compute_block_constancy(block, {})

        assert constancy == [{}]  # just the leading live-in slot, no instructions


class TestBlockListIntegration:
    def test_phi_across_a_diamond_propagates_a_matching_literal(self):
        # Start splits into Left/Right, both re-joining at Merge, which combines them via
        # a phi function. Left and Right assign the SAME literal, so Merge's phi should
        # resolve it (needs compute_constancy_for_block_list to have already processed
        # both predecessors before Merge)
        start = make_block("Start", [])
        start.set_jump_to("Left")
        start.set_falls_to("Right")

        left = make_block("Left", [make_instr("LiteralAssignment", ["0x2a"], ["v_left"])],
                          liveness_out=["v_left"])
        left.set_jump_to("Merge")

        right = make_block("Right", [make_instr("LiteralAssignment", ["0x2a"], ["v_right"])],
                           liveness_out=["v_right"])
        right.set_jump_to("Merge")

        merge = make_block("Merge", [
            make_instr("PhiFunction", ["v_left", "v_right"], ["phi_merge"]),
            make_instr("mstore", ["phi_merge", "0x00"], []),
        ], entries=["Left", "Right"])

        block_list = CFGBlockList("test")
        block_list.add_block(start, is_start_block=True)
        block_list.add_block(left)
        block_list.add_block(right)
        block_list.add_block(merge)

        constancy_per_block, _ = compute_constancy_for_block_list(block_list, {})

        # already known at the live-in slot, same reasoning as TestPhiFunction's cases above
        assert constancy_per_block["Merge"][0] == {"phi_merge": "0x2a"}
        assert constancy_per_block["Merge"][1] == {"phi_merge": "0x2a"}

    def test_phi_across_a_diamond_with_different_literals_infers_nothing(self):
        start = make_block("Start", [])
        start.set_jump_to("Left")
        start.set_falls_to("Right")

        left = make_block("Left", [make_instr("LiteralAssignment", ["0x2a"], ["v_left"])],
                          liveness_out=["v_left"])
        left.set_jump_to("Merge")

        right = make_block("Right", [make_instr("LiteralAssignment", ["0x2b"], ["v_right"])],
                           liveness_out=["v_right"])
        right.set_jump_to("Merge")

        merge = make_block("Merge", [make_instr("PhiFunction", ["v_left", "v_right"], ["phi_merge"])],
                           entries=["Left", "Right"])

        block_list = CFGBlockList("test")
        block_list.add_block(start, is_start_block=True)
        block_list.add_block(left)
        block_list.add_block(right)
        block_list.add_block(merge)

        constancy_per_block, _ = compute_constancy_for_block_list(block_list, {})

        assert constancy_per_block["Merge"][0] == {}

    def test_constant_survives_an_intermediate_block_that_never_references_it(self):
        # Entry -> Middle -> Exit, no branching, no phi anywhere. Middle never references v0
        # at all, yet it's live straight through it -- the direct regression test for the
        # real-world bug (see propagation.py's live-in passthrough pass)
        entry = make_block("Entry", [make_instr("LiteralAssignment", ["0x3039"], ["v0"])],
                           liveness_out=["v0"])
        entry.set_jump_to("Middle")

        middle = make_block("Middle", [make_instr("add", ["v1", "v2"], ["v3"])],
                            liveness_in=["v0"], liveness_out=["v0"], entries=["Entry"])
        middle.set_jump_to("Exit")

        exit_block = make_block("Exit", [make_instr("mstore", ["v0", "0x00"], [])],
                                liveness_in=["v0"], entries=["Middle"])

        block_list = CFGBlockList("test")
        block_list.add_block(entry, is_start_block=True)
        block_list.add_block(middle)
        block_list.add_block(exit_block)

        constancy_per_block, _ = compute_constancy_for_block_list(block_list, {})

        assert constancy_per_block["Middle"][0] == {"v0": "0x3039"}
        assert constancy_per_block["Exit"][0] == {"v0": "0x3039"}
        assert constancy_per_block["Exit"][1] == {"v0": "0x3039"}

    def test_non_phi_constant_propagates_into_a_loop_header_from_the_forward_edge_alone(self):
        # Direct regression test for the real bug (ERC20_925/clear_storage_range_bytes1/Block6,
        # occurrence occ_004_T1 for 0x24fcfc492c1393274b6bcd568ac9e225bec93584): a constant
        # defined once before a loop and never reassigned has no PhiFunction at the loop header
        # (SSA never needed one, since it's the same value on every edge, including the back
        # edge) -- it must propagate into the header from the one already-processed (forward)
        # predecessor without waiting for the not-yet-processed back edge from the loop body,
        # and from there into the body too. Confirmed against the real static_foryu binary this
        # produces CONSTANCY_VALID where the old, over-strict unanimity requirement did not.
        entry = make_block("Entry", [make_instr("LiteralAssignment", ["0x2a"], ["v0"])],
                           liveness_out=["v0"])
        entry.set_jump_to("Header")

        header = make_block("Header", [
            make_instr("PhiFunction", ["v1", "v3"], ["v2"]),  # unrelated loop counter
            make_instr("lt", ["v2", "0x0a"], ["v4"]),
        ], liveness_in=["v0", "v1"], liveness_out=["v0", "v2"], entries=["Entry", "Body"])
        header.set_jump_info({"type": "ConditionalJump", "cond": "v4", "targets": ["Body", "Exit"]})

        body = make_block("Body", [
            make_instr("sstore", ["v0", "v2"], []),
            make_instr("add", ["v2", "0x01"], ["v3"]),
        ], liveness_in=["v0", "v2"], liveness_out=["v0", "v3"])
        body.set_jump_to("Header")

        exit_block = make_block("Exit", [], liveness_in=[])
        exit_block.set_jump_info({"type": "Terminated"})

        block_list = CFGBlockList("test")
        block_list.add_block(entry, is_start_block=True)
        block_list.add_block(header)
        block_list.add_block(body)
        block_list.add_block(exit_block)

        constancy_per_block, exit_constants_per_block = compute_constancy_for_block_list(block_list, {})

        assert constancy_per_block["Header"][0] == {"v0": "0x2a"}
        assert exit_constants_per_block["Header"] == {"v0": "0x2a"}
        assert constancy_per_block["Body"][0] == {"v0": "0x2a"}
