import logging

from constancy.seed_extraction import (_block_processing_order, _fold_conditional_exit, _literal_value_table,
                                       _match_scope, _merge_trivial_blocks, _reachable_block_ids,
                                       _scope_defining_instructions, _scope_entry_id, _values_provably_equal,
                                       extract_seed_facts_for_contract, extract_seed_facts_for_instructions,
                                       is_literal, isolate_cleanup_sequence, iter_block_scopes,
                                       match_block_instructions, probe_sequence, with_stack_allocation_disabled)


def test_is_literal():
    assert is_literal("0x20")
    assert not is_literal("v1")


class TestIsolateCleanupSequence:
    def test_appends_a_colon_when_none_is_present(self):
        assert isolate_cleanup_sequence("dfDv") == "dfDv:"
        assert isolate_cleanup_sequence("") == ":"

    def test_leaves_an_existing_colon_alone(self):
        assert isolate_cleanup_sequence("dfDv:fDnTOcmu") == "dfDv:fDnTOcmu"
        assert isolate_cleanup_sequence(":") == ":"


class TestWithStackAllocationDisabled:
    def test_sets_the_flag_without_clobbering_existing_yul_details(self):
        json_input = {"settings": {"optimizer": {"details": {"yulDetails": {"optimizerSteps": "dfDv"}}}}}

        result = with_stack_allocation_disabled(json_input)

        yul_details = result["settings"]["optimizer"]["details"]["yulDetails"]
        assert yul_details["stackAllocation"] is False
        assert yul_details["optimizerSteps"] == "dfDv"
        # the input itself is untouched (a deep copy was returned)
        assert "stackAllocation" not in json_input["settings"]["optimizer"]["details"]["yulDetails"]

    def test_creates_missing_levels(self):
        result = with_stack_allocation_disabled({})

        assert result["settings"]["optimizer"]["details"]["yulDetails"]["stackAllocation"] is False


class TestMatchScope:
    def test_a_silently_vanished_block_produces_a_confident_but_wrong_pairing(self):
        # Mirrors a real bug found against a real contract (see PROGRESS.md): solc's
        # StackCompressor can silently drop one block from a chain of otherwise-identically-
        # shaped ConditionalJump checks. Structural matching can't tell "B1" was ever there --
        # it just sees a uniform chain and confidently walks one link too far
        cond_instr = {"in": ["v0"], "op": "iszero", "out": ["c"]}
        baseline = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["B1", "D0"]},
             "instructions": [cond_instr]},
            {"id": "B1", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["B2", "D1"]},  # vanishes in probe
             "instructions": [cond_instr]},
            {"id": "B2", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["B3", "D2"]},
             "instructions": [cond_instr]},
            {"id": "B3", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "D0", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "D1", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "D2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]
        probe = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["PB2", "D0"]},  # skips B1
             "instructions": [cond_instr]},
            {"id": "PB2", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["PB3", "D1"]},
             "instructions": [cond_instr]},
            {"id": "PB3", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "D0", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "D1", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]

        correspondence, _, _ = _match_scope(baseline, probe)

        # B2 should really correspond to "PB2" (the real, surviving continuation of the check
        # chain) -- but the matcher, seeing only uniform shapes, confidently resolves it one
        # link too far. This is exactly why StackCompressor needed a different fix (disabling
        # it for isolated probes), not a smarter matcher -- see PROGRESS.md
        assert correspondence["B2"] == "PB3"
        # B3 (past the vanished block's shape boundary) is correctly left unresolved rather
        # than guessed, once the shape genuinely stops lining up
        assert "B3" not in correspondence

    def test_predecessors_disagreeing_leaves_a_block_unresolved(self):
        cond_instr = {"in": ["v0"], "op": "iszero", "out": ["c"]}
        baseline = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["B1", "B2"]},
             "instructions": [cond_instr]},
            {"id": "B1", "exit": {"type": "Jump", "targets": ["B3"]}, "instructions": []},
            {"id": "B2", "exit": {"type": "Jump", "targets": ["B3"]}, "instructions": []},
            {"id": "B3", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]
        probe = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["B1", "B2"]},
             "instructions": [cond_instr]},
            {"id": "B1", "exit": {"type": "Jump", "targets": ["P1"]}, "instructions": []},
            {"id": "B2", "exit": {"type": "Jump", "targets": ["P2"]}, "instructions": []},
            {"id": "P1", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "P2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]

        correspondence, _, _ = _match_scope(baseline, probe)

        assert correspondence["B1"] == "B1"
        assert correspondence["B2"] == "B2"
        # B3's two predecessors propose different probe targets (P1 vs P2) -- unresolved,
        # not guessed
        assert "B3" not in correspondence

    def test_conditional_jump_with_a_different_condition_is_not_matched(self):
        # Same exit shape (ConditionalJump, 2 targets) on both sides, but the condition
        # variable's own defining instruction differs (iszero vs gt) -- the shape check alone
        # would let this through; verifying the condition itself catches it
        baseline = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["B1", "B2"]},
             "instructions": [{"in": ["v0"], "op": "iszero", "out": ["c"]}]},
            {"id": "B1", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "B2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]
        probe = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["P1", "P2"]},
             "instructions": [{"in": ["v0"], "op": "gt", "out": ["c"]}]},
            {"id": "P1", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "P2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]

        correspondence, _, _ = _match_scope(baseline, probe)

        assert correspondence == {"B0": "B0"}
        assert "B1" not in correspondence
        assert "B2" not in correspondence

    def test_a_negated_condition_is_matched_with_targets_swapped(self):
        # Baseline branches on c = iszero(v0); probe branches directly on the un-negated v0
        # (same lt(...) shape), with the two branch targets swapped accordingly. targets[0] is
        # the falls_to (cond == 0) target, targets[1] the jump_to (cond != 0) target -- see
        # parser.cfg_block.CFGBlock.set_jump_info -- so negating the condition means what was
        # falls_to becomes jump_to and vice versa.
        lt_instr = {"in": ["0x0f", "s0"], "op": "lt", "out": ["v0"]}
        baseline = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["B1", "B2"]},
             "instructions": [lt_instr, {"in": ["v0"], "op": "iszero", "out": ["c"]}]},
            {"id": "B1", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "B2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]
        probe = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "x", "targets": ["P_B2", "P_B1"]},
             "instructions": [{"in": ["0x0f", "s0"], "op": "lt", "out": ["x"]}]},
            {"id": "P_B1", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "P_B2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]

        correspondence, _, _ = _match_scope(baseline, probe)

        assert correspondence == {"B0": "B0", "B1": "P_B1", "B2": "P_B2"}

    def test_an_eq_zero_condition_matches_an_iszero_condition_without_swapping_targets(self):
        # eq(0x00, X) and iszero(X) compute the identical boolean -- a real ExpressionSimplifier
        # canonicalization (confirmed directly on a real contract: TUPProxy's
        # fun_verifyCallResultFromTarget), not a negation, so -- unlike the swapped-targets case
        # above -- target order stays untouched.
        baseline = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["B1", "B2"]},
             "instructions": [{"in": ["0x0f", "s0"], "op": "lt", "out": ["v0"]},
                               {"in": ["0x00", "v0"], "op": "eq", "out": ["c"]}]},
            {"id": "B1", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "B2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]
        probe = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "x", "targets": ["P_B1", "P_B2"]},
             "instructions": [{"in": ["0x0f", "s0"], "op": "lt", "out": ["y"]},
                               {"in": ["y"], "op": "iszero", "out": ["x"]}]},
            {"id": "P_B1", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "P_B2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]

        correspondence, _, _ = _match_scope(baseline, probe)

        assert correspondence == {"B0": "B0", "B1": "P_B1", "B2": "P_B2"}

    def test_a_block_whose_sole_route_in_is_a_loop_back_edge_stays_unresolved(self):
        # Mirrors a real case (NFTMarketWrap, occurrence T3, scope abi_encode_array_address):
        # B1's branch condition (v3) is a compile-time-constant LiteralAssignment from B0, not
        # locally defined in B1 -- and here (unlike test_a_negated_condition_is_matched...)
        # B0's own LiteralAssignment doesn't even unify (0x01 vs 0x00), so v3's correspondence
        # is never established at all. solc's block-joiner can eliminate a block like B1
        # outright once its condition is provably always-true, leaving no probe counterpart;
        # B1's own successor B2 then has no other route in except B3, a loop back edge, which
        # this single-forward-pass design cannot use retroactively. B1 itself still gets a
        # confident (and, in a real case like this, wrong) correspondence from B0's plain
        # unconditional Jump -- but that's exactly why the condition check on B1's own branch
        # exists: it correctly refuses to let that confidence propagate any further.
        baseline = [
            {"id": "B0", "exit": {"type": "Jump", "targets": ["B1"]},
             "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
            {"id": "B1", "exit": {"type": "ConditionalJump", "cond": "v3", "targets": ["B4", "B2"]},
             "instructions": []},
            {"id": "B4", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "B2", "exit": {"type": "ConditionalJump", "cond": "c2", "targets": ["B6", "B5"]},
             "instructions": [{"in": ["0x0f", "x"], "op": "lt", "out": ["c2"]}]},
            {"id": "B6", "exit": {"type": "Jump", "targets": ["B3"]}, "instructions": []},
            {"id": "B5", "exit": {"type": "Jump", "targets": ["B4"]}, "instructions": []},
            {"id": "B3", "exit": {"type": "Jump", "targets": ["B1"]}, "instructions": []},  # back edge
        ]
        probe = [
            {"id": "B0", "exit": {"type": "Jump", "targets": ["B2"]},
             "instructions": [{"in": ["0x00"], "op": "LiteralAssignment", "out": ["v2"]}]},
            {"id": "B2", "exit": {"type": "ConditionalJump", "cond": "c2", "targets": ["B6", "B5"]},
             "instructions": [{"in": ["0x0f", "x"], "op": "lt", "out": ["c2"]}]},
            {"id": "B6", "exit": {"type": "Jump", "targets": ["B3"]}, "instructions": []},
            {"id": "B5", "exit": {"type": "Jump", "targets": ["B4"]}, "instructions": []},
            {"id": "B3", "exit": {"type": "Jump", "targets": ["B2"]}, "instructions": []},  # loop header now B2
            {"id": "B4", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]

        correspondence, _, _ = _match_scope(baseline, probe)

        assert "B2" not in correspondence
        assert "B4" not in correspondence

    def test_phi_function_args_are_realigned_by_predecessor_entries_not_position(self):
        # M's two predecessors (P1, P2) are listed in probe's own "entries" in the opposite
        # order from baseline's -- nothing guarantees solc emits them in the same order in both
        # compilations. A blind positional zip of the PhiFunction's "in" args would pair
        # baseline's a1 (from P1) against probe's b2 (from Q2), contradicting the var_map P1's
        # own match already established (a1 <-> b1) -- entries-based realignment avoids that.
        cond_instr = {"in": ["v0"], "op": "iszero", "out": ["c"]}
        baseline = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["P1", "P2"]},
             "instructions": [cond_instr]},
            {"id": "P1", "exit": {"type": "Jump", "targets": ["M"]},
             "instructions": [{"in": ["0x11"], "op": "LiteralAssignment", "out": ["a1"]}]},
            {"id": "P2", "exit": {"type": "Jump", "targets": ["M"]},
             "instructions": [{"in": ["0x22"], "op": "LiteralAssignment", "out": ["a2"]}]},
            {"id": "M", "exit": {"type": "Terminated", "targets": []}, "entries": ["P1", "P2"],
             "instructions": [{"in": ["a1", "a2"], "op": "PhiFunction", "out": ["phi"]}]},
        ]
        probe = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["Q1", "Q2"]},
             "instructions": [cond_instr]},
            {"id": "Q1", "exit": {"type": "Jump", "targets": ["M"]},
             "instructions": [{"in": ["0x11"], "op": "LiteralAssignment", "out": ["b1"]}]},
            {"id": "Q2", "exit": {"type": "Jump", "targets": ["M"]},
             "instructions": [{"in": ["0x22"], "op": "LiteralAssignment", "out": ["b2"]}]},
            {"id": "M", "exit": {"type": "Terminated", "targets": []}, "entries": ["Q2", "Q1"],  # reversed
             "instructions": [{"in": ["b2", "b1"], "op": "PhiFunction", "out": ["phi2"]}]},
        ]

        correspondence, var_maps, _ = _match_scope(baseline, probe)

        assert correspondence["M"] == "M"
        assert var_maps["M"]["phi"] == "phi2"

    def test_cond_check_uses_the_accumulated_var_map_not_just_local_instructions(self):
        # v3 is defined in A, merely passed through B (which touches nothing), and used as C's
        # branch condition -- never locally defined inside C itself. A var_map seeded only from
        # C's own instructions (there are none) could never verify this; the accumulated
        # var_map, threaded forward from A through B, can.
        baseline = [
            {"id": "A", "exit": {"type": "Jump", "targets": ["B"]},
             "instructions": [{"in": ["0x0f", "s0"], "op": "lt", "out": ["v3"]}]},
            {"id": "B", "exit": {"type": "Jump", "targets": ["C"]}, "instructions": []},
            {"id": "C", "exit": {"type": "ConditionalJump", "cond": "v3", "targets": ["T1", "T2"]},
             "instructions": []},
            {"id": "T1", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "T2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]
        probe = [
            {"id": "A", "exit": {"type": "Jump", "targets": ["B"]},
             "instructions": [{"in": ["0x0f", "s0"], "op": "lt", "out": ["w3"]}]},
            {"id": "B", "exit": {"type": "Jump", "targets": ["C"]}, "instructions": []},
            {"id": "C", "exit": {"type": "ConditionalJump", "cond": "w3", "targets": ["U1", "U2"]},
             "instructions": []},
            {"id": "U1", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "U2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]

        correspondence, _, _ = _match_scope(baseline, probe)

        assert correspondence == {"A": "A", "B": "B", "C": "C", "T1": "U1", "T2": "U2"}


class TestFoldConditionalExit:
    def test_folds_a_provably_true_condition_to_the_jump_to_target(self):
        block = {"exit": {"type": "ConditionalJump", "cond": "v3", "targets": ["B4", "B2"]}}
        assert _fold_conditional_exit(block, {"v3": "0x01"}) == {"type": "Jump", "targets": ["B2"]}

    def test_folds_a_provably_false_condition_to_the_falls_to_target(self):
        block = {"exit": {"type": "ConditionalJump", "cond": "v3", "targets": ["B4", "B2"]}}
        assert _fold_conditional_exit(block, {"v3": "0x00"}) == {"type": "Jump", "targets": ["B4"]}

    def test_leaves_an_unresolvable_condition_unchanged(self):
        exit_ = {"type": "ConditionalJump", "cond": "v3", "targets": ["B4", "B2"]}
        assert _fold_conditional_exit({"exit": exit_}, {}) is exit_

    def test_leaves_a_non_conditional_exit_unchanged(self):
        exit_ = {"type": "Jump", "targets": ["B1"]}
        assert _fold_conditional_exit({"exit": exit_}, {"v3": "0x01"}) is exit_


class TestBlockProcessingOrder:
    def test_a_simple_linear_chain_resolves_in_list_order(self):
        blocks = [
            {"id": "B0", "exit": {"targets": ["B1"]}},
            {"id": "B1", "exit": {"targets": ["B2"]}},
            {"id": "B2", "exit": {"targets": []}},
        ]
        assert _block_processing_order(blocks) == ["B0", "B1", "B2"]

    def test_a_merge_block_is_scheduled_after_at_least_one_real_predecessor(self):
        # The real regression this fix is for: a diamond where the short branch (1 block) and
        # the long branch (3 blocks) converge on Merge. A topological sort of the *dominator
        # tree* (the previous implementation) could freely place Merge right after the common
        # dominator B0, before either branch's own blocks -- exactly what was confirmed on a
        # real contract (copy_byte_array_to_storage_from_string_to_string's Block4, permanently
        # unresolved by _match_scope despite both real predecessors, once available,
        # unambiguously agreeing). A forward BFS can only discover Merge once at least one of
        # its real predecessors (here, Short) has actually been visited.
        blocks = [
            {"id": "B0", "exit": {"targets": ["Short", "Long1"]}},
            {"id": "Short", "exit": {"targets": ["Merge"]}},
            {"id": "Long1", "exit": {"targets": ["Long2"]}},
            {"id": "Long2", "exit": {"targets": ["Long3"]}},
            {"id": "Long3", "exit": {"targets": ["Merge"]}},
            {"id": "Merge", "exit": {"targets": []}},
        ]
        order = _block_processing_order(blocks)
        assert order.index("Merge") > order.index("Short")

    def test_a_block_reachable_only_via_a_back_edge_is_appended_at_the_end(self):
        blocks = [
            {"id": "B0", "exit": {"targets": ["B1"]}},
            {"id": "B1", "exit": {"targets": ["B0"]}},  # B0's only other route in is this back edge
        ]
        assert _block_processing_order(blocks) == ["B0", "B1"]

    def test_an_explicit_entry_id_is_honored_over_position_zero(self):
        blocks = [
            {"id": "NotTheEntry", "exit": {"targets": []}},
            {"id": "RealEntry", "exit": {"targets": ["Successor"]}},
            {"id": "Successor", "exit": {"targets": []}},
        ]
        assert _block_processing_order(blocks, entry_id="RealEntry") == \
            ["RealEntry", "Successor", "NotTheEntry"]


class TestLiteralValueTable:
    def test_tracks_a_direct_literal_assignment(self):
        blocks = [
            {"id": "B0", "exit": {"type": "Terminated", "targets": []},
             "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
        ]
        assert _literal_value_table(blocks)["B0"] == {"v3": "0x01"}

    def test_threads_a_literal_forward_through_a_block_with_no_own_literal(self):
        blocks = [
            {"id": "B0", "exit": {"type": "Jump", "targets": ["B1"]},
             "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
            {"id": "B1", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]
        assert _literal_value_table(blocks)["B1"] == {"v3": "0x01"}

    def test_drops_a_variable_when_predecessors_disagree(self):
        blocks = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["B1", "B2"]},
             "instructions": [{"in": ["v0"], "op": "iszero", "out": ["c"]}]},
            {"id": "B1", "exit": {"type": "Jump", "targets": ["B3"]},
             "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
            {"id": "B2", "exit": {"type": "Jump", "targets": ["B3"]},
             "instructions": [{"in": ["0x02"], "op": "LiteralAssignment", "out": ["v3"]}]},
            {"id": "B3", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]
        assert "v3" not in _literal_value_table(blocks)["B3"]

    def test_folds_a_multi_instruction_arithmetic_chain_over_literals(self):
        # Mirrors the real array_allocation_size_bytes_2988 shape: no direct LiteralAssignment
        # for the branch condition itself -- it's a whole shl/sub/gt chain, each instruction's
        # result only known via the table entries the earlier instructions in the same block just
        # built.
        blocks = [
            {"id": "B0", "exit": {"type": "Terminated", "targets": []},
             "instructions": [
                 {"in": ["0x01", "0x40"], "op": "shl", "out": ["v0"]},
                 {"in": ["0x01", "v0"], "op": "sub", "out": ["v1"]},
                 {"in": ["v1", "0x27"], "op": "gt", "out": ["v2"]},
             ]},
        ]
        assert _literal_value_table(blocks)["B0"] == {
            "v0": "0x010000000000000000", "v1": "0xffffffffffffffff", "v2": "0x00",
        }

    def test_resolves_a_phi_function_when_every_predecessor_agrees(self):
        blocks = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["B1", "B2"]},
             "instructions": [{"in": ["v0"], "op": "iszero", "out": ["c"]}]},
            {"id": "B1", "exit": {"type": "Jump", "targets": ["B3"]},
             "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
            {"id": "B2", "exit": {"type": "Jump", "targets": ["B3"]},
             "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v4"]}]},
            {"id": "B3", "entries": ["B1", "B2"], "exit": {"type": "Terminated", "targets": []},
             "instructions": [{"in": ["v3", "v4"], "op": "PhiFunction", "out": ["phi"]}]},
        ]
        assert _literal_value_table(blocks)["B3"]["phi"] == "0x01"

    def test_does_not_resolve_a_phi_function_when_predecessors_disagree(self):
        blocks = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["B1", "B2"]},
             "instructions": [{"in": ["v0"], "op": "iszero", "out": ["c"]}]},
            {"id": "B1", "exit": {"type": "Jump", "targets": ["B3"]},
             "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
            {"id": "B2", "exit": {"type": "Jump", "targets": ["B3"]},
             "instructions": [{"in": ["0x02"], "op": "LiteralAssignment", "out": ["v4"]}]},
            {"id": "B3", "entries": ["B1", "B2"], "exit": {"type": "Terminated", "targets": []},
             "instructions": [{"in": ["v3", "v4"], "op": "PhiFunction", "out": ["phi"]}]},
        ]
        assert "phi" not in _literal_value_table(blocks)["B3"]

    def test_resolves_a_phi_function_from_the_resolved_predecessors_when_one_is_a_loop_back_edge(self):
        # B3's second entry, B4, is only reachable via B3 itself (a loop back edge) -- not yet
        # processed when B3's own table is being built (single forward pass, no fixpoint) -- so
        # it's simply skipped, matching the existing predecessor-merge's "not yet processed" rule.
        blocks = [
            {"id": "B1", "exit": {"type": "Jump", "targets": ["B3"]},
             "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
            {"id": "B3", "entries": ["B1", "B4"], "exit": {"type": "Jump", "targets": ["B4"]},
             "instructions": [{"in": ["v3", "v5"], "op": "PhiFunction", "out": ["phi"]}]},
            {"id": "B4", "exit": {"type": "Jump", "targets": ["B3"]},
             "instructions": [{"in": ["phi"], "op": "iszero", "out": ["v5"]}]},
        ]
        assert _literal_value_table(blocks)["B3"]["phi"] == "0x01"


class TestMergeTrivialBlocks:
    def test_absorbs_a_block_left_behind_by_folding_a_provably_true_condition(self):
        # Mirrors the real abi_encode_array_address shape: B1's branch on v3 (always 0x01,
        # defined in B0) folds to unconditional, and since B2 (the real loop-check content) then
        # has B1 as its sole effective predecessor, B2 gets absorbed into B1. B4 (the dead
        # branch's target) becomes unreachable once that edge folds away, and is dropped
        # entirely (_reachable_block_ids) rather than kept around as an orphan nothing could
        # ever propose a correspondence for anyway.
        blocks = [
            {"id": "B0", "exit": {"type": "Jump", "targets": ["B1"]},
             "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
            {"id": "B1", "exit": {"type": "ConditionalJump", "cond": "v3", "targets": ["B4", "B2"]},
             "instructions": []},
            {"id": "B4", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "B2", "exit": {"type": "ConditionalJump", "cond": "c2", "targets": ["B6", "B5"]},
             "instructions": [{"in": ["0x0f", "x"], "op": "lt", "out": ["c2"]}]},
            {"id": "B6", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "B5", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]

        working = _merge_trivial_blocks(blocks)

        assert [b["id"] for b in working] == ["B0", "B1", "B6", "B5"]
        b1 = next(b for b in working if b["id"] == "B1")
        assert b1["exit"] == {"type": "ConditionalJump", "cond": "c2", "targets": ["B6", "B5"]}
        assert b1["_members"] == {"B1", "B2"}
        assert b1["_provenance"] == [("B2", 0)]

    def test_absorbs_a_block_behind_a_multi_instruction_arithmetic_condition(self):
        # Same shape as test_absorbs_a_block_left_behind_by_folding_a_provably_true_condition,
        # but B0's condition is a two-instruction arithmetic chain (sub then iszero) rather than
        # a direct LiteralAssignment -- the real array_allocation_size_bytes_2988 case this
        # feature was built for has no direct LiteralAssignment for the condition at all.
        blocks = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "v2", "targets": ["B4", "B2"]},
             "instructions": [
                 {"in": ["0x05", "0x05"], "op": "sub", "out": ["v0"]},
                 {"in": ["v0"], "op": "iszero", "out": ["v2"]},
             ]},
            {"id": "B4", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "B2", "exit": {"type": "ConditionalJump", "cond": "c2", "targets": ["B6", "B5"]},
             "instructions": [{"in": ["0x0f", "x"], "op": "lt", "out": ["c2"]}]},
            {"id": "B6", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "B5", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]

        working = _merge_trivial_blocks(blocks)

        assert [b["id"] for b in working] == ["B0", "B6", "B5"]
        b0 = next(b for b in working if b["id"] == "B0")
        assert b0["exit"] == {"type": "ConditionalJump", "cond": "c2", "targets": ["B6", "B5"]}
        assert b0["_members"] == {"B0", "B2"}

    def test_never_absorbs_a_block_with_a_phi_function_even_if_effectively_single_predecessor(self):
        blocks = [
            {"id": "B0", "exit": {"type": "Jump", "targets": ["B1"]},
             "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
            {"id": "B1", "exit": {"type": "ConditionalJump", "cond": "v3", "targets": ["B4", "B2"]},
             "instructions": []},
            {"id": "B4", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "B2", "entries": ["B1"], "exit": {"type": "Terminated", "targets": []},
             "instructions": [{"in": ["v9", "v9"], "op": "PhiFunction", "out": ["phi"]}]},
        ]

        working = _merge_trivial_blocks(blocks)

        assert [b["id"] for b in working] == ["B0", "B1", "B2"]

    def test_never_merges_a_plain_unconditional_chain_folding_never_touched(self):
        # No ConditionalJump anywhere -- nothing to fold -- so B0/B1 stay separate, preserving
        # the block-by-block var_map seeding _match_scope relies on to disambiguate an
        # otherwise-ambiguous instruction (see the module docstring)
        blocks = [
            {"id": "B0", "exit": {"type": "Jump", "targets": ["B1"]},
             "instructions": [{"in": ["v9", "v0"], "op": "sub", "out": ["v10"]}]},
            {"id": "B1", "exit": {"type": "Terminated", "targets": []},
             "instructions": [{"in": ["v9", "v100"], "op": "sub", "out": ["v60"]}]},
        ]

        working = _merge_trivial_blocks(blocks)

        assert [b["id"] for b in working] == ["B0", "B1"]

    def test_members_include_an_absorbed_block_with_zero_instructions(self):
        blocks = [
            {"id": "B0", "exit": {"type": "Jump", "targets": ["B1"]},
             "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
            {"id": "B1", "exit": {"type": "ConditionalJump", "cond": "v3", "targets": ["B4", "B2"]},
             "instructions": []},
            {"id": "B4", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "B2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},  # no instructions
        ]

        working = _merge_trivial_blocks(blocks)

        b1 = next(b for b in working if b["id"] == "B1")
        assert b1["_members"] == {"B1", "B2"}
        assert b1["_provenance"] == []


class TestReachableBlockIds:
    def test_drops_a_block_only_reachable_through_a_provably_dead_branch(self):
        blocks = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "v3", "targets": ["B4", "B2"]},
             "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
            {"id": "B4", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "B2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]
        assert _reachable_block_ids(blocks) == {"B0", "B2"}

    def test_keeps_both_branches_when_the_condition_is_not_provably_constant(self):
        blocks = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["B4", "B2"]},
             "instructions": []},
            {"id": "B4", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
            {"id": "B2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
        ]
        assert _reachable_block_ids(blocks) == {"B0", "B4", "B2"}


class TestExtractSeedFactsForContractNormalization:
    def test_recovers_a_fact_behind_a_block_eliminated_by_folding_a_provably_true_condition(self):
        # Same shape as TestMatchScope.
        # test_a_block_whose_sole_route_in_is_a_loop_back_edge_stays_unresolved's baseline, but
        # probe's literal now agrees with baseline's (both 0x01) -- so, unlike that test, the
        # branch really is the same provable constant on both sides, and solc eliminating the
        # precheck block entirely in probe is something extract_seed_facts_for_contract's
        # normalization can now see through, recovering the downstream fact (v3, used again in
        # B2's `add`, is known to be 0x01) that a block-level mismatch would otherwise hide.
        baseline = {
            "type": "Object",
            "Main": {
                "blocks": [
                    {"id": "A", "exit": {"type": "Jump", "targets": ["B1"]},
                     "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
                    {"id": "B1", "exit": {"type": "ConditionalJump", "cond": "v3", "targets": ["B4", "B2"]},
                     "instructions": []},
                    {"id": "B4", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                    {"id": "B2", "exit": {"type": "ConditionalJump", "cond": "c2", "targets": ["B6", "B5"]},
                     "instructions": [{"in": ["0x0f", "x"], "op": "lt", "out": ["c2"]},
                                       {"in": ["v3", "x"], "op": "add", "out": ["v13"]}]},
                    {"id": "B6", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                    {"id": "B5", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                ],
                "functions": {}, "subObjects": {},
            },
        }
        probe = {
            "type": "Object",
            "Main": {
                "blocks": [
                    {"id": "A", "exit": {"type": "Jump", "targets": ["B2"]},
                     "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v2"]}]},
                    {"id": "B2", "exit": {"type": "ConditionalJump", "cond": "c2", "targets": ["B6", "B5"]},
                     "instructions": [{"in": ["0x0f", "x"], "op": "lt", "out": ["c2"]},
                                       {"in": ["0x01", "x"], "op": "add", "out": ["v13"]}]},
                    {"id": "B6", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                    {"id": "B5", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                    {"id": "B4", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                ],
                "functions": {}, "subObjects": {},
            },
        }

        facts = extract_seed_facts_for_contract(baseline, probe)

        assert facts == {(("Main",), "B2", 1, "v3"): "0x01"}

    def test_a_symmetric_unreachable_dead_block_produces_no_warning(self, caplog):
        # Mirrors the real TUPProxy c4/c5/T2 pattern _reachable_block_ids was added for:
        # baseline and probe both fold the same branch to provably-true, leaving an identical
        # dead-revert block (B4) with zero effective predecessors on *both* sides -- a shape
        # _match_scope's predecessor-propagation can never resolve regardless of content (only
        # the position-0 entry gets a free anchor). Before the fix this produced a spurious "no
        # unique structural correspondence" warning purely from that structural gap, even though
        # the two sides are byte-identical dead code; now B4 is recognized as unreachable and
        # excluded from the check entirely.
        def make():
            return {
                "type": "Object",
                "Main": {
                    "blocks": [
                        {"id": "A", "exit": {"type": "Jump", "targets": ["B1"]},
                         "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v3"]}]},
                        {"id": "B1", "exit": {"type": "ConditionalJump", "cond": "v3", "targets": ["B4", "B2"]},
                         "instructions": []},
                        {"id": "B4", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                        {"id": "B2", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                    ],
                    "functions": {}, "subObjects": {},
                },
            }

        with caplog.at_level(logging.WARNING):
            extract_seed_facts_for_contract(make(), make())

        assert not any("no unique structural correspondence" in record.message for record in caplog.records)

    def test_a_diamond_merge_with_an_unbalanced_branch_length_produces_no_warning(self, caplog):
        # The real bug this fix is for, reproduced end to end: no folding is involved anywhere
        # (no literal condition, nothing for _merge_trivial_blocks to touch) -- baseline and
        # probe are byte-identical. Merge is reached from a 1-block branch (Short) and a 3-block
        # branch (Long1/Long2/Long3); its immediate dominator is A, not either branch, so the
        # previous dominator-tree-based order could schedule Merge before *either* branch was
        # processed, permanently failing to resolve it even though both real predecessors agree.
        def make():
            return {
                "type": "Object",
                "Main": {
                    "blocks": [
                        {"id": "A", "exit": {"type": "ConditionalJump", "cond": "c", "targets": ["Short", "Long1"]},
                         "instructions": [{"in": ["x"], "op": "iszero", "out": ["c"]}]},
                        {"id": "Short", "exit": {"type": "Jump", "targets": ["Merge"]}, "instructions": []},
                        {"id": "Long1", "exit": {"type": "Jump", "targets": ["Long2"]}, "instructions": []},
                        {"id": "Long2", "exit": {"type": "Jump", "targets": ["Long3"]}, "instructions": []},
                        {"id": "Long3", "exit": {"type": "Jump", "targets": ["Merge"]}, "instructions": []},
                        {"id": "Merge", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                    ],
                    "functions": {}, "subObjects": {},
                },
            }

        with caplog.at_level(logging.WARNING):
            extract_seed_facts_for_contract(make(), make())

        assert not any("no unique structural correspondence" in record.message for record in caplog.records)

    def test_a_rematerialized_movable_op_chain_across_a_block_boundary_produces_no_warning(self, caplog):
        # Mirrors the real T1 case end to end: baseline computes a pure compile-time-constant
        # subexpression once in an ancestor block (A) and reuses it directly in a descendant's
        # (B's) branch condition; probe recomputes the same chain fresh, under new variable
        # names, right at the use site in B instead of carrying it across the block boundary.
        # Without _values_provably_equal, B's own condition-defining "gt" instruction would fail
        # to unify (its second-to-last argument, the carried v6/v8, conflicts with probe's
        # locally-recomputed v11), leaving B (and hence C/D) unresolved.
        baseline = {
            "type": "Object",
            "Main": {
                "blocks": [
                    {"id": "A", "exit": {"type": "Jump", "targets": ["B"]},
                     "instructions": [
                         {"in": ["0x01", "0x40"], "op": "shl", "out": ["v5"]},
                         {"in": ["0x01", "v5"], "op": "sub", "out": ["v6"]},
                     ]},
                    {"id": "B", "exit": {"type": "ConditionalJump", "cond": "v8", "targets": ["C", "D"]},
                     "instructions": [
                         {"in": ["0x00"], "op": "mload", "out": ["v7"]},
                         {"in": ["v6", "v7"], "op": "gt", "out": ["v8"]},
                     ]},
                    {"id": "C", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                    {"id": "D", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                ],
                "functions": {}, "subObjects": {},
            },
        }
        probe = {
            "type": "Object",
            "Main": {
                "blocks": [
                    {"id": "A", "exit": {"type": "Jump", "targets": ["B"]},
                     "instructions": [
                         {"in": ["0x01", "0x40"], "op": "shl", "out": ["v5"]},
                         {"in": ["0x01", "v5"], "op": "sub", "out": ["v6"]},
                     ]},
                    {"id": "B", "exit": {"type": "ConditionalJump", "cond": "v12", "targets": ["C", "D"]},
                     "instructions": [
                         {"in": ["0x00"], "op": "mload", "out": ["v9"]},
                         {"in": ["0x01", "0x40"], "op": "shl", "out": ["v10"]},
                         {"in": ["0x01", "v10"], "op": "sub", "out": ["v11"]},
                         {"in": ["v11", "v9"], "op": "gt", "out": ["v12"]},
                     ]},
                    {"id": "C", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                    {"id": "D", "exit": {"type": "Terminated", "targets": []}, "instructions": []},
                ],
                "functions": {}, "subObjects": {},
            },
        }

        with caplog.at_level(logging.WARNING):
            extract_seed_facts_for_contract(baseline, probe)

        assert not any("no unique structural correspondence" in record.message for record in caplog.records)


class TestProbeSequence:
    def test_isolates_a_colon_less_base_before_appending_steps(self):
        # Without isolation this would be "T" -- solc would then silently run its own default
        # cleanup ("fDnTOcmuO") on top, confounding the comparison (see PROGRESS.md)
        assert probe_sequence("", ["T"]) == ":T"
        assert probe_sequence("dfDv", ["T", "m"]) == "dfDv:Tm"

    def test_appends_to_an_existing_cleanup_unchanged(self):
        # A base that already has a real, deliberate colon (e.g. DEFAULT_OPTIMIZER_SEQUENCE)
        # is untouched -- the extra steps just extend its existing cleanup, as before
        assert probe_sequence("dfDv:fDnTOcmu", ["T"]) == "dfDv:fDnTOcmuT"


class TestScopeDefiningInstructions:
    def test_builds_a_flat_map_across_multiple_blocks(self):
        blocks = [
            {"id": "B0", "instructions": [{"in": ["0x01"], "op": "LiteralAssignment", "out": ["v1"]}]},
            {"id": "B1", "instructions": [{"in": ["v1", "0x02"], "op": "add", "out": ["v2", "v3"]}]},
        ]
        defs = _scope_defining_instructions(blocks)

        assert defs["v1"] == {"in": ["0x01"], "op": "LiteralAssignment", "out": ["v1"]}
        assert defs["v2"] is defs["v3"] is blocks[1]["instructions"][0]


class TestValuesProvablyEqual:
    def test_the_same_name_is_trivially_equal(self):
        assert _values_provably_equal("v1", "v1", {})

    def test_two_literals_that_differ_are_not_equal(self):
        assert not _values_provably_equal("0x01", "0x02", {})

    def test_same_movable_op_same_literal_args_is_equal(self):
        # The T1 pattern: a pure compile-time constant, recomputed under a different name
        defs = {
            "v8": {"op": "sub", "in": ["0x01", "v7"]}, "v7": {"op": "shl", "in": ["0x01", "0x40"]},
            "v15": {"op": "sub", "in": ["0x01", "v14"]}, "v14": {"op": "shl", "in": ["0x01", "0x40"]},
        }
        assert _values_provably_equal("v15", "v8", defs)

    def test_same_movable_op_one_arg_recursively_equal_the_other_already_confirmed(self):
        # The c3 pattern: and(0x01, v15) recomputed, where v15 is already the same name on both
        # sides (an already-confirmed identity, not itself needing further resolution)
        defs = {"v18": {"op": "and", "in": ["0x01", "v15"]}, "v23": {"op": "and", "in": ["0x01", "v15"]}}
        assert _values_provably_equal("v23", "v18", defs)

    def test_same_movable_op_but_a_genuinely_different_argument_is_not_equal(self):
        defs = {"v18": {"op": "and", "in": ["0x01", "v15"]}, "v23": {"op": "and", "in": ["0x01", "v16"]}}
        assert not _values_provably_equal("v23", "v18", defs)

    def test_a_non_movable_op_requires_exact_name_match_and_does_not_recurse(self):
        defs = {"v15": {"op": "sload", "in": ["0x03"]}, "v16": {"op": "sload", "in": ["0x03"]}}
        assert not _values_provably_equal("v16", "v15", defs)

    def test_a_commutative_op_resolves_equal_with_swapped_arguments(self):
        defs = {"v1": {"op": "add", "in": ["v9", "v10"]}, "v2": {"op": "add", "in": ["v10", "v9"]}}
        assert _values_provably_equal("v2", "v1", defs)

    def test_different_ops_are_not_equal(self):
        defs = {"v1": {"op": "add", "in": ["v9", "v10"]}, "v2": {"op": "sub", "in": ["v9", "v10"]}}
        assert not _values_provably_equal("v2", "v1", defs)

    def test_mismatched_argument_counts_are_not_equal(self):
        defs = {"v1": {"op": "and", "in": ["v9", "v10"]}, "v2": {"op": "and", "in": ["v9", "v10", "v11"]}}
        assert not _values_provably_equal("v2", "v1", defs)


class TestMatchBlockInstructions:
    def test_matches_by_output_variable_even_if_another_instruction_vanished(self):
        baseline = [
            {"in": ["0x20"], "op": "LiteralAssignment", "out": ["v0"]},
            {"in": ["v2", "v0"], "op": "add", "out": ["v1"]},
        ]
        # The LiteralAssignment defining v0 is now dead and gone in the probe
        probe = [{"in": ["v2", "0x20"], "op": "add", "out": ["v1"]}]

        facts, var_map = match_block_instructions(baseline, probe)

        assert facts == {1: {"v0": "0x20"}}
        assert var_map["v2"] == "v2"

    def test_matches_no_output_instructions_consistently(self):
        baseline = [
            {"in": ["v1", "0x00"], "op": "mstore", "out": []},
            {"in": ["v2", "0x20"], "op": "mstore", "out": []},
        ]
        probe = [
            {"in": ["v1", "0x00"], "op": "mstore", "out": []},
            {"in": ["0x2a", "0x20"], "op": "mstore", "out": []},
        ]

        facts, _ = match_block_instructions(baseline, probe)

        assert facts == {1: {"v2": "0x2a"}}

    def test_rejects_a_collision_when_a_shared_variable_disagrees_later_in_the_walk(self):
        # Mirrors a real bug found against a real contract (see PROGRESS.md): an earlier
        # instruction (baseline idx0) gets eliminated in the probe, shifting idx2's relative
        # position. Naive by-name matching would coincidentally match baseline's
        # "add(v9, v0) -> v10" against probe's unrelated "add(0x80, v4) -> v10" purely because
        # both produce "v10". Walking backward first confirms v0 <-> v0 from the later (in
        # program order) use at idx3/idx2, so by the time the walk reaches idx2/idx1 the
        # tentative v0 <-> v4 that pairing would need already contradicts it, and the whole
        # instruction is rejected rather than reported as a (wrong) fact
        baseline = [
            {"in": ["0x00", "v0"], "op": "add", "out": ["v5"]},   # idx0: eliminated in probe
            {"in": ["v5"], "op": "use", "out": ["v6"]},            # idx1
            {"in": ["v9", "v0"], "op": "add", "out": ["v10"]},     # idx2: collision-prone
            {"in": ["v10", "v0"], "op": "mstore", "out": []},      # idx3: anchors v0 <-> v0
        ]
        probe = [
            {"in": ["v0"], "op": "use", "out": ["v6"]},            # idx0: matches baseline idx1
            {"in": ["0x80", "v4"], "op": "add", "out": ["v10"]},   # idx1: coincidence with baseline idx2
            {"in": ["v10", "v0"], "op": "mstore", "out": []},      # idx2: matches baseline idx3
        ]

        facts, _ = match_block_instructions(baseline, probe)

        assert facts == {}

    def test_resync_recovers_a_fact_past_an_inserted_instruction(self):
        # An instruction gets inserted partway through the probe (mirroring a real case in
        # PROGRESS.md where probing 'T' at a point that interacts with a cleanup phase added
        # instructions rather than removing any). Everything after the insertion aligns at a
        # constant +1 offset; everything before it aligns at offset 0. The walk must find the
        # unique resync point where that transition happens
        baseline = [
            {"in": ["v20", "v0"], "op": "add", "out": ["v21"]},        # idx0: before the insertion
            {"in": ["0x55"], "op": "LiteralAssignment", "out": ["v22"]},  # idx1: before the insertion
            {"in": ["v9", "v0"], "op": "add", "out": ["v10"]},          # idx2: after the insertion
            {"in": ["v10", "v0"], "op": "mstore", "out": []},           # idx3: after the insertion
        ]
        probe = [
            {"in": ["v20", "v0"], "op": "add", "out": ["v21"]},        # idx0: matches baseline idx0
            {"in": ["0x55"], "op": "LiteralAssignment", "out": ["v22"]},  # idx1: matches baseline idx1
            {"in": ["0x77"], "op": "LiteralAssignment", "out": ["v99"]},  # idx2: INSERTED
            {"in": ["0x2a", "v0"], "op": "add", "out": ["v10"]},        # idx3: matches baseline idx2
            {"in": ["v10", "v0"], "op": "mstore", "out": []},           # idx4: matches baseline idx3
        ]

        facts, _ = match_block_instructions(baseline, probe)

        assert facts == {2: {"v9": "0x2a"}}

    def test_rejects_a_coincidental_pairing_only_caught_by_the_next_instruction(self):
        # Mirrors a real bug found against a real contract (see PROGRESS.md): a struct-zeroing
        # loop where a shared stride variable ("v2" = 0x20) is added repeatedly to a running
        # pointer. ExpressionSimplifier folds the chain into direct literal offsets from the
        # base pointer, so the LAST add's two operands happen to unify in isolation (output
        # matches, and the stride variable looks like it substituted to a literal) -- but the
        # SAME instruction also proposes a coincidental v6<->v0 correspondence purely because
        # both sit at the same argument position, and that correspondence is only proven wrong
        # by the very next (mstore) instruction, one step later. The match must not report the
        # substitution it briefly proposed, since it was never actually confirmed
        baseline = [
            {"in": ["0x20"], "op": "LiteralAssignment", "out": ["v2"]},   # idx0: true value of v2
            {"in": ["v2", "v0"], "op": "add", "out": ["v3"]},              # idx1
            {"in": ["v3", "v1"], "op": "mstore", "out": []},               # idx2
            {"in": ["v2", "v3"], "op": "add", "out": ["v4"]},              # idx3
            {"in": ["v4", "v1"], "op": "mstore", "out": []},               # idx4
            {"in": ["v2", "v4"], "op": "add", "out": ["v5"]},              # idx5
            {"in": ["v5", "v1"], "op": "mstore", "out": []},               # idx6
        ]
        probe = [
            {"in": ["0x20"], "op": "LiteralAssignment", "out": ["v2"]},   # idx0: matches baseline idx0
            {"in": ["0x20", "v0"], "op": "add", "out": ["v3"]},            # idx1: matches baseline idx1
            {"in": ["v3", "v1"], "op": "mstore", "out": []},               # idx2: matches baseline idx2
            {"in": ["0x40", "v0"], "op": "add", "out": ["v4"]},            # idx3: folded, no longer uses v3
            {"in": ["v4", "v1"], "op": "mstore", "out": []},               # idx4: matches baseline idx4
            {"in": ["0x60", "v0"], "op": "add", "out": ["v5"]},            # idx5: folded, coincidentally
                                                                            # pairs baseline's "v4" with "v0"
            {"in": ["v5", "v1"], "op": "mstore", "out": []},               # idx6: proves that pairing wrong
        ]

        facts, _ = match_block_instructions(baseline, probe)

        assert "v4" not in facts.get(5, {})
        assert "v2" not in facts.get(3, {})
        assert "v2" not in facts.get(1, {})

    def test_ambiguous_resync_stops_rather_than_guessing(self):
        # Two candidates are equally plausible with no further context to distinguish them --
        # nothing should be inferred rather than guessing which one is real
        baseline = [{"in": ["v9", "v0"], "op": "sub", "out": ["v10"]}]
        probe = [
            {"in": ["0x11", "v0"], "op": "sub", "out": ["v50"]},   # candidate A
            {"in": ["0x22", "v0"], "op": "sub", "out": ["v51"]},   # candidate B
            {"in": ["0x99", "v2"], "op": "mul", "out": ["v60"]},   # natural start -- wrong op, forces resync
        ]

        facts, _ = match_block_instructions(baseline, probe)

        assert facts == {}

    def test_partial_anchor_alignment_when_counts_differ(self):
        # An extra anchor (sstore) with no probe counterpart doesn't block the rest of the
        # block: the second mstore has a distinctive literal (0x99) that only one probe
        # instruction can match, and committing it narrows the first mstore's candidate range
        # down to the one remaining option -- per the user's guidance, align whatever's
        # unambiguously determinable rather than giving up on the whole block
        baseline = [
            {"in": ["v9", "v0"], "op": "mstore", "out": []},    # anchor 0: pinned via order once anchor 2 resolves
            {"in": ["0x22", "v1"], "op": "sstore", "out": []},  # anchor 1: extra -- no probe counterpart
            {"in": ["0x99", "v0"], "op": "mstore", "out": []},  # anchor 2: distinctive literal resolves first
        ]
        probe = [
            {"in": ["0x11", "v0"], "op": "mstore", "out": []},
            {"in": ["0x99", "v0"], "op": "mstore", "out": []},
        ]

        facts, _ = match_block_instructions(baseline, probe)

        assert facts == {0: {"v9": "0x11"}}

    def test_movable_instructions_disambiguated_by_a_downstream_shared_variable(self):
        # Mirrors a real contract (NFTMarketWrap, occurrence T2, Block11): two structurally-
        # identical shl/sub pairs (an address-mask construction) are individually ambiguous,
        # but the second one feeds an "and" alongside an already-known external variable
        # (v28, live-in, unrenamed) -- that pins it down uniquely, which then resolves the
        # first pair by elimination. Also demonstrates reordering across an anchor: solc moved
        # the first shl/sub pair from before the sload to after it, since neither touches
        # storage -- a fixed "segment strictly between two anchors" model would miss this
        baseline = [
            {"in": ["0x01", "0xa0"], "op": "shl", "out": ["v1"]},
            {"in": ["0x01", "v1"], "op": "sub", "out": ["v2"]},
            {"in": ["0x00"], "op": "sload", "out": ["v3"]},
            {"in": ["0x01", "0xa0"], "op": "shl", "out": ["v4"]},
            {"in": ["0x01", "v4"], "op": "sub", "out": ["v5"]},
            {"in": ["v5", "v28"], "op": "and", "out": ["v6"]},
        ]
        probe = [
            {"in": ["0x00"], "op": "sload", "out": ["v10"]},
            {"in": ["0x01", "0xa0"], "op": "shl", "out": ["v11"]},
            {"in": ["0x01", "v11"], "op": "sub", "out": ["v12"]},
            {"in": ["0x01", "0xa0"], "op": "shl", "out": ["v13"]},
            {"in": ["0x01", "v13"], "op": "sub", "out": ["v14"]},
            {"in": ["v14", "v28"], "op": "and", "out": ["v15"]},
        ]

        _, var_map = match_block_instructions(baseline, probe)

        assert var_map["v5"] == "v14"  # the pinned pair
        assert var_map["v2"] == "v12"  # resolved afterward, by elimination
        assert var_map["v1"] == "v11"
        assert var_map["v4"] == "v13"

    def test_commutative_operand_order_swap(self):
        # solc is free to reorder a commutative op's operands; the natural (positional) order
        # here hard-fails (two different literals at the literal-vs-literal position), so the
        # swap is unambiguously the only viable interpretation, not just a preference
        baseline = [{"in": ["0x05", "v9"], "op": "add", "out": ["v1"]}]
        probe = [{"in": ["0x2a", "0x05"], "op": "add", "out": ["v1"]}]

        facts, _ = match_block_instructions(baseline, probe)

        assert facts == {0: {"v9": "0x2a"}}

    def test_associative_reassociation_is_declined_without_producing_a_wrong_fact(self):
        # Mirrors a real contract (UniversalRouter, occurrence s#1, a 127-instruction calldata-
        # decoding block): solc regrouped a 3-term add chain ((0x20+v9)+v10 -> 0x20+(v10+v9)).
        # The intermediate baseline value (v2) has no counterpart instruction in probe at all,
        # so no per-instruction check can match it structurally -- confirmed this doesn't
        # produce a wrong fact (the real case cost nothing, since the reassociated region had
        # no constant to find either way); a genuinely unrelated fact elsewhere in the same
        # block is still found cleanly
        baseline = [
            {"in": ["0x20", "v9"], "op": "add", "out": ["v2"]},
            {"in": ["v10", "v2"], "op": "add", "out": ["v3"]},
            {"in": ["v3", "v0"], "op": "mstore", "out": []},
            {"in": ["v20", "0x07"], "op": "add", "out": ["v21"]},  # unrelated -- v20 becomes a literal in probe
            {"in": ["v21", "v1"], "op": "mstore", "out": []},
        ]
        probe = [
            {"in": ["v10", "v9"], "op": "add", "out": ["v2b"]},   # reassociated: (v10+v9) computed first
            {"in": ["0x20", "v2b"], "op": "add", "out": ["v3b"]},  # same final value, different grouping
            {"in": ["v3b", "v0"], "op": "mstore", "out": []},
            {"in": ["0x99", "0x07"], "op": "add", "out": ["v21b"]},
            {"in": ["v21b", "v1"], "op": "mstore", "out": []},
        ]

        facts, _ = match_block_instructions(baseline, probe)

        assert facts == {3: {"v20": "0x99"}}

    def test_reassociation_is_still_declined_even_with_probe_defs_supplied(self):
        # Regression lock: probe_defs (_values_provably_equal) must not reopen the reassociation
        # gap above. It doesn't apply here regardless -- its precondition is a baseline argument
        # *already confirmed* in var_map conflicting with a probe argument, and none of the
        # reassociated-region variables are pre-seeded in var_map in this fixture -- but this
        # locks that in directly rather than relying on that reasoning alone.
        baseline = [
            {"in": ["0x20", "v9"], "op": "add", "out": ["v2"]},
            {"in": ["v10", "v2"], "op": "add", "out": ["v3"]},
            {"in": ["v3", "v0"], "op": "mstore", "out": []},
            {"in": ["v20", "0x07"], "op": "add", "out": ["v21"]},
            {"in": ["v21", "v1"], "op": "mstore", "out": []},
        ]
        probe = [
            {"in": ["v10", "v9"], "op": "add", "out": ["v2b"]},
            {"in": ["0x20", "v2b"], "op": "add", "out": ["v3b"]},
            {"in": ["v3b", "v0"], "op": "mstore", "out": []},
            {"in": ["0x99", "0x07"], "op": "add", "out": ["v21b"]},
            {"in": ["v21b", "v1"], "op": "mstore", "out": []},
        ]
        probe_defs = _scope_defining_instructions([{"instructions": probe}])

        facts, _ = match_block_instructions(baseline, probe, probe_defs=probe_defs)

        assert facts == {3: {"v20": "0x99"}}

    def test_a_rematerialized_movable_op_chain_is_recognized_as_the_same_value(self):
        # Mirrors the real c3 case: baseline reuses v18 (carried in via seed_var_map, standing in
        # for a value an ancestor block already computed once) directly; probe recomputes
        # and(0x01, v15) fresh at the use site instead of reusing its own v18. Without probe_defs
        # this positional conflict (var_map already says v18 -> v18, but probe's actual argument
        # here is v23) would reject the whole instruction outright.
        baseline = [{"in": ["v21", "v18"], "op": "eq", "out": ["v22"]}]
        probe = [
            {"in": ["0x01", "v15"], "op": "and", "out": ["v23"]},
            {"in": ["v21", "v23"], "op": "eq", "out": ["v24"]},
        ]
        probe_defs = _scope_defining_instructions([
            {"instructions": [{"in": ["0x01", "v15"], "op": "and", "out": ["v18"]}]},  # ancestor block
            {"instructions": probe},
        ])
        seed_var_map = {"v18": "v18", "v21": "v21"}

        facts, var_map = match_block_instructions(baseline, probe, seed_var_map=seed_var_map, probe_defs=probe_defs)

        assert var_map["v22"] == "v24"

    def test_probe_materializes_a_literal_baseline_inlines_directly(self):
        # Mirrors a real contract (TUPProxy, external_fun_cancelFreeze): CSE hoists what used to
        # be several per-call-site literal copies into one shared, named variable -- so baseline
        # can inline a literal directly (slt(0x00, ...)) while probe references an earlier
        # same-block LiteralAssignment with the identical value at that same argument position.
        baseline = [{"in": ["0x00", "v2"], "op": "slt", "out": ["v3"]}]
        probe = [
            {"in": ["0x00"], "op": "LiteralAssignment", "out": ["v1"]},
            {"in": ["v1", "v4"], "op": "slt", "out": ["v3b"]},
        ]

        facts, var_map = match_block_instructions(baseline, probe)

        assert facts == {}
        assert var_map["v2"] == "v4"

    def test_baseline_materializes_a_literal_probe_inlines_directly(self):
        # The symmetric direction -- already handled by the pre-existing mechanism (a baseline
        # variable whose own LiteralAssignment vanishes once probe inlines its value directly is
        # exactly the "substitution discovered at its use site" case), kept here as a regression
        # lock alongside the new probe-side resolution above.
        baseline = [
            {"in": ["0x00"], "op": "LiteralAssignment", "out": ["v1"]},
            {"in": ["v1", "v2"], "op": "slt", "out": ["v3"]},
        ]
        probe = [{"in": ["0x00", "v4"], "op": "slt", "out": ["v3b"]}]

        facts, _ = match_block_instructions(baseline, probe)

        assert facts == {1: {"v1": "0x00"}}

    def test_a_materialized_literal_that_genuinely_differs_is_not_matched(self):
        baseline = [{"in": ["0x00", "v2"], "op": "slt", "out": ["v3"]}]
        probe = [
            {"in": ["0x01"], "op": "LiteralAssignment", "out": ["v1"]},
            {"in": ["v1", "v4"], "op": "slt", "out": ["v3b"]},
        ]

        facts, var_map = match_block_instructions(baseline, probe)

        assert facts == {}
        assert "v2" not in var_map


class TestExtractSeedFactsForInstructions:
    def test_finds_variable_to_literal_substitution(self):
        baseline = [
            {"in": ["0x20"], "op": "LiteralAssignment", "out": ["v0"]},
            {"in": ["v2", "v0"], "op": "add", "out": ["v1"]},
        ]
        probe = [{"in": ["v2", "0x20"], "op": "add", "out": ["v1"]}]

        facts = extract_seed_facts_for_instructions(baseline, probe)

        assert facts == {1: {"v0": "0x20"}}

    def test_no_facts_when_nothing_changes(self):
        baseline = [{"in": ["v1", "v2"], "op": "add", "out": ["v3"]}]
        probe = [{"in": ["v1", "v2"], "op": "add", "out": ["v3"]}]

        assert extract_seed_facts_for_instructions(baseline, probe) == {}

    def test_argument_count_change_is_ignored(self):
        # Not a pure literal substitution (e.g. an argument was dropped by some other
        # optimization); must not be reported as a fact
        baseline = [{"in": ["v1", "v2"], "op": "add", "out": ["v3"]}]
        probe = [{"in": ["v1"], "op": "add", "out": ["v3"]}]

        assert extract_seed_facts_for_instructions(baseline, probe) == {}


class TestIterBlockScopes:
    def _yul_cfg_json(self):
        return {
            "type": "Object",
            "Main": {
                "blocks": [{"id": "Block0"}],
                "functions": {"fun_f": {"blocks": [{"id": "Block0"}]}},
                "subObjects": {
                    "type": "subObject",
                    "Main_deployed": {"blocks": [{"id": "Block0"}], "functions": {}, "subObjects": {}},
                },
            },
        }

    def test_walks_object_function_and_subobject(self):
        scopes = dict(iter_block_scopes(self._yul_cfg_json()))

        assert set(scopes.keys()) == {("Main",), ("Main", "fun_f"), ("Main", "Main_deployed")}
        assert scopes[("Main",)] == [{"id": "Block0"}]


class TestScopeEntryId:
    def _yul_cfg_json(self):
        return {
            "type": "Object",
            "Main": {
                "blocks": [{"id": "B0"}, {"id": "B1"}],
                "functions": {"fun_f": {"entry": "Block2", "blocks": [{"id": "Block2"}, {"id": "Block5"}]}},
                "subObjects": {
                    "type": "subObject",
                    "Main_deployed": {"blocks": [{"id": "D0"}], "functions": {}, "subObjects": {}},
                },
            },
        }

    def test_resolves_a_function_scope_from_its_own_entry_field(self):
        yul_cfg_json = self._yul_cfg_json()
        blocks = yul_cfg_json["Main"]["functions"]["fun_f"]["blocks"]

        assert _scope_entry_id(yul_cfg_json, ("Main", "fun_f"), blocks) == "Block2"

    def test_falls_back_to_the_first_block_for_an_object_scope_with_no_entry_field(self):
        yul_cfg_json = self._yul_cfg_json()
        blocks = yul_cfg_json["Main"]["blocks"]

        assert _scope_entry_id(yul_cfg_json, ("Main",), blocks) == "B0"

    def test_falls_back_to_the_first_block_for_a_subobject_scope_with_no_entry_field(self):
        yul_cfg_json = self._yul_cfg_json()
        blocks = yul_cfg_json["Main"]["subObjects"]["Main_deployed"]["blocks"]

        assert _scope_entry_id(yul_cfg_json, ("Main", "Main_deployed"), blocks) == "D0"


class TestExtractSeedFactsForContract:
    def test_keys_facts_by_scope_block_and_instruction(self):
        baseline = {
            "type": "Object",
            "Main": {
                "blocks": [{"id": "Block0", "exit": {"type": "Terminated", "targets": []}, "instructions": [
                    {"in": ["0x20"], "op": "LiteralAssignment", "out": ["v0"]},
                    {"in": ["v2", "v0"], "op": "add", "out": ["v1"]},
                ]}],
                "functions": {},
                "subObjects": {},
            },
        }
        probe = {
            "type": "Object",
            "Main": {
                "blocks": [{"id": "Block0", "exit": {"type": "Terminated", "targets": []}, "instructions": [
                    {"in": ["v2", "0x20"], "op": "add", "out": ["v1"]},
                ]}],
                "functions": {},
                "subObjects": {},
            },
        }

        facts = extract_seed_facts_for_contract(baseline, probe)

        assert facts == {(("Main",), "Block0", 1, "v0"): "0x20"}

    def test_predecessor_mapping_resolves_an_otherwise_ambiguous_successor(self):
        baseline = {
            "type": "Object",
            "Main": {
                "blocks": [
                    {"id": "Block0", "exit": {"type": "Jump", "targets": ["Block1"]},
                     "instructions": [{"in": ["v9", "v0"], "op": "sub", "out": ["v10"]}]},
                    {"id": "Block1", "exit": {"type": "Terminated", "targets": []},
                     "instructions": [{"in": ["v9", "v100"], "op": "sub", "out": ["v60"]}]},
                ],
                "functions": {}, "subObjects": {},
            },
        }
        probe = {
            "type": "Object",
            "Main": {
                "blocks": [
                    {"id": "Block0", "exit": {"type": "Jump", "targets": ["Block1"]},
                     "instructions": [{"in": ["v88", "v0"], "op": "sub", "out": ["v10"]}]},
                    {"id": "Block1", "exit": {"type": "Terminated", "targets": []},
                     "instructions": [
                         {"in": ["v77", "0x55"], "op": "sub", "out": ["v70"]},   # wrong candidate
                         {"in": ["v88", "0x66"], "op": "sub", "out": ["v71"]},   # matches Block0's v9<->v88
                         {"in": ["0x99", "v5"], "op": "mul", "out": ["v40"]},    # natural start -- forces resync
                     ]},
                ],
                "functions": {}, "subObjects": {},
            },
        }

        # In isolation, Block1's own instruction is genuinely ambiguous between the two
        # candidates -- nothing should be inferred without the predecessor's context
        isolated_facts, _ = match_block_instructions(
            baseline["Main"]["blocks"][1]["instructions"], probe["Main"]["blocks"][1]["instructions"])
        assert isolated_facts == {}

        # With Block0 processed first (dominance order) and its confirmed v9<->v88 threaded
        # in as a seed, only the matching candidate survives
        facts = extract_seed_facts_for_contract(baseline, probe)
        assert facts[(("Main",), "Block1", 0, "v100")] == "0x66"
