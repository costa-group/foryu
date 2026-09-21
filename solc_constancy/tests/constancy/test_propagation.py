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

        assert constancy[0] == {"v0": "0x20"}
        assert constancy[1] == {"v0": "0x20"}  # last use is instruction 1
        assert constancy[2] == {}  # dead: no further use, not live-out
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

        assert constancy[0] == {"v9": "0x2a"}

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

    def test_variable_with_no_use_and_not_live_out_never_appears(self):
        block = make_block("B6", [
            make_instr("LiteralAssignment", ["0x09"], ["v1"]),
            make_instr("stop", [], []),
        ])

        constancy, exit_constants = compute_block_constancy(block, {})

        assert constancy == [{}, {}]
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

        assert constancy[0] == {"v0": "0x20"}  # unaffected: read directly off the LiteralAssignment
        assert constancy[1] == {"v0": "0x20"}  # still alive, still correct
        assert "v9" not in constancy[1]  # discarded, even though nothing of its own conflicted
        assert constancy[2] == {"v0": "0x20"}

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
        # PredB hasn't been processed yet (e.g. reachable only through a loop back edge)
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

        assert constancy[0] == {"phi1": "0x2a"}
        assert constancy[1] == {"phi1": "0x2a"}

    def test_seed_fact_on_phi_output_is_used_directly(self):
        block = make_block("B2", [
            make_instr("PhiFunction", ["v10", "v20"], ["phi1"]),
            make_instr("mstore", ["phi1", "0x00"], []),
        ], entries=["PredA", "PredB"])

        constancy, _ = compute_block_constancy(block, {0: {"phi1": "0x05"}})

        assert constancy[0] == {"phi1": "0x05"}
        assert constancy[1] == {"phi1": "0x05"}


class TestLiveOut:
    def test_live_out_variable_spans_to_end_of_block(self):
        block = make_block("B4", [
            make_instr("LiteralAssignment", ["0x07"], ["v5"]),
            make_instr("add", ["v5", "v6"], ["v7"]),
        ], liveness_in=["v6"], liveness_out=["v5"])

        constancy, exit_constants = compute_block_constancy(block, {})

        assert constancy[0] == {"v5": "0x07"}
        assert constancy[1] == {"v5": "0x07"}
        assert exit_constants == {"v5": "0x07"}


class TestFunctionReturnExit:
    def test_synthetic_function_return_instruction_is_excluded_from_the_result(self):
        # Mirrors what CFGBlock._process_instructions_from_function_return appends for a
        # FunctionReturn exit: a synthetic "functionReturn" instruction that never appears in
        # the raw yulCFGJson block's "instructions" array. The reported constancy list must
        # stay the same length as that raw array (one entry per real instruction), not grow
        # by one for this synthetic instruction.
        block = make_block("B7", [
            make_instr("LiteralAssignment", ["0x2a"], ["v0"]),
            make_instr("functionReturn", ["v0"], []),
        ], liveness_out=["v0"])

        constancy, exit_constants = compute_block_constancy(block, {})

        assert constancy == [{"v0": "0x2a"}]
        assert exit_constants == {"v0": "0x2a"}

    def test_empty_block_with_only_a_function_return_reports_no_instructions(self):
        block = make_block("B8", [make_instr("functionReturn", ["v0"], [])], liveness_out=["v0"])

        constancy, _ = compute_block_constancy(block, {})

        assert constancy == []


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

        assert constancy_per_block["Merge"][0] == {"phi_merge": "0x2a"}

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
