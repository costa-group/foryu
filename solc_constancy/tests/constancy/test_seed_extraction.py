from constancy.seed_extraction import (_match_blocks_structurally, extract_seed_facts_for_contract,
                                       extract_seed_facts_for_instructions, is_literal, isolate_cleanup_sequence,
                                       iter_block_scopes, match_block_instructions, probe_sequence,
                                       with_stack_allocation_disabled)


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


class TestMatchBlocksStructurally:
    def test_a_silently_vanished_block_produces_a_confident_but_wrong_pairing(self):
        # Mirrors a real bug found against a real contract (see PROGRESS.md): solc's
        # StackCompressor can silently drop one block from a chain of otherwise-identically-
        # shaped ConditionalJump checks. Structural matching can't tell "B1" was ever there --
        # it just sees a uniform chain and confidently walks one link too far
        baseline = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "targets": ["B1", "D0"]}},
            {"id": "B1", "exit": {"type": "ConditionalJump", "targets": ["B2", "D1"]}},  # vanishes in probe
            {"id": "B2", "exit": {"type": "ConditionalJump", "targets": ["B3", "D2"]}},
            {"id": "B3", "exit": {"type": "Terminated", "targets": []}},
            {"id": "D0", "exit": {"type": "Terminated", "targets": []}},
            {"id": "D1", "exit": {"type": "Terminated", "targets": []}},
            {"id": "D2", "exit": {"type": "Terminated", "targets": []}},
        ]
        probe = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "targets": ["PB2", "D0"]}},  # skips B1
            {"id": "PB2", "exit": {"type": "ConditionalJump", "targets": ["PB3", "D1"]}},
            {"id": "PB3", "exit": {"type": "Terminated", "targets": []}},
            {"id": "D0", "exit": {"type": "Terminated", "targets": []}},
            {"id": "D1", "exit": {"type": "Terminated", "targets": []}},
        ]

        correspondence = _match_blocks_structurally(baseline, probe)

        # B2 should really correspond to "PB2" (the real, surviving continuation of the check
        # chain) -- but the matcher, seeing only uniform shapes, confidently resolves it one
        # link too far. This is exactly why StackCompressor needed a different fix (disabling
        # it for isolated probes), not a smarter matcher -- see PROGRESS.md
        assert correspondence["B2"] == "PB3"
        # B3 (past the vanished block's shape boundary) is correctly left unresolved rather
        # than guessed, once the shape genuinely stops lining up
        assert "B3" not in correspondence

    def test_predecessors_disagreeing_leaves_a_block_unresolved(self):
        baseline = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "targets": ["B1", "B2"]}},
            {"id": "B1", "exit": {"type": "Jump", "targets": ["B3"]}},
            {"id": "B2", "exit": {"type": "Jump", "targets": ["B3"]}},
            {"id": "B3", "exit": {"type": "Terminated", "targets": []}},
        ]
        probe = [
            {"id": "B0", "exit": {"type": "ConditionalJump", "targets": ["B1", "B2"]}},
            {"id": "B1", "exit": {"type": "Jump", "targets": ["P1"]}},
            {"id": "B2", "exit": {"type": "Jump", "targets": ["P2"]}},
            {"id": "P1", "exit": {"type": "Terminated", "targets": []}},
            {"id": "P2", "exit": {"type": "Terminated", "targets": []}},
        ]

        correspondence = _match_blocks_structurally(baseline, probe)

        assert correspondence["B1"] == "B1"
        assert correspondence["B2"] == "B2"
        # B3's two predecessors propose different probe targets (P1 vs P2) -- unresolved,
        # not guessed
        assert "B3" not in correspondence


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
