import copy
import json
import os
import subprocess

import pytest

from find_unsound_constancy_facts import (
    DEFAULT_STATIC_FORYU,
    _build_probe,
    _flatten_facts,
    _is_invalid,
    _run_static_foryu,
    ddmin,
    find_unsound_facts,
)

_requires_static_foryu = pytest.mark.skipif(not os.path.isfile(DEFAULT_STATIC_FORYU),
                                            reason="static_foryu binary not found at the default path")


class _FakeCompletedProcess:
    def __init__(self, stdout=""):
        self.stdout = stdout
        self.stderr = ""
        self.returncode = 0


def _annotated_with(block_a_constancy, block_b_constancy):
    return {
        "contracts": {
            "a.sol": {
                "A": {
                    "yulCFGJson": {
                        "type": "Object",
                        "A": {
                            "blocks": [
                                {"id": "BlockA", "exit": {"type": "Terminated", "targets": []},
                                 "liveness": {"in": [], "out": []},
                                 "instructions": [{"in": ["v0", "v0"], "op": "sub", "out": ["v1"]}],
                                 "constancy": block_a_constancy},
                                {"id": "BlockB", "exit": {"type": "Terminated", "targets": []},
                                 "liveness": {"in": [], "out": []},
                                 "instructions": [{"in": ["v2", "v2"], "op": "xor", "out": ["v3"]}],
                                 "constancy": block_b_constancy},
                            ],
                            "functions": {}, "subObjects": {},
                        },
                    },
                },
            },
        },
    }


class TestRunStaticForyu:
    def test_parses_a_constancy_only_csv_line(self, monkeypatch):
        line = "some/file.json,JSON_PROCESSING_OK,12,34,1000,2000,3000,CONSTANCY_VALID"
        monkeypatch.setattr(subprocess, "run", lambda *a, **kw: _FakeCompletedProcess(stdout=line + "\n"))

        row = _run_static_foryu({}, "/path/to/static_foryu")

        assert row["json_status"] == "JSON_PROCESSING_OK"
        assert row["constancy_result"] == "CONSTANCY_VALID"

    def test_short_line_is_reported_as_empty_rather_than_raising(self, monkeypatch):
        monkeypatch.setattr(subprocess, "run", lambda *a, **kw: _FakeCompletedProcess(stdout=""))

        row = _run_static_foryu({}, "/path/to/static_foryu")

        assert row == {"json_status": "", "constancy_result": ""}


class TestFlattenAndBuildProbe:
    def test_flattens_every_nonempty_entry_across_both_blocks(self):
        data = _annotated_with(
            block_a_constancy=[{}, {"v1": "0x00"}],
            block_b_constancy=[{}, {"v3": "0x00"}],
        )

        facts = _flatten_facts(data)

        assert len(facts) == 2
        scope_paths = {f[0] for f in facts}
        assert ("A", "BlockA") in scope_paths
        assert ("A", "BlockB") in scope_paths

    def test_build_probe_keeps_only_the_given_facts(self):
        data = _annotated_with(
            block_a_constancy=[{}, {"v1": "0x00"}],
            block_b_constancy=[{}, {"v3": "0x00"}],
        )
        facts = _flatten_facts(data)
        keep_only_a = [f for f in facts if f[0] == ("A", "BlockA")]

        probe = _build_probe(data, keep_only_a)

        blocks = probe["contracts"]["a.sol"]["A"]["yulCFGJson"]["A"]["blocks"]
        block_a = next(b for b in blocks if b["id"] == "BlockA")
        block_b = next(b for b in blocks if b["id"] == "BlockB")
        assert block_a["constancy"] == [{}, {"v1": "0x00"}]
        assert block_b["constancy"] == [{}, {}]

    def test_build_probe_does_not_mutate_the_original(self):
        data = _annotated_with(block_a_constancy=[{}, {"v1": "0x00"}], block_b_constancy=[{}, {}])
        original = copy.deepcopy(data)

        _build_probe(data, [])

        assert data == original


class TestDdmin:
    def test_finds_the_single_necessary_element(self):
        candidates = list(range(10))
        target = lambda subset: 7 in subset

        result = ddmin(candidates, target)

        assert result == [7]

    def test_finds_two_jointly_necessary_elements(self):
        candidates = list(range(10))
        target = lambda subset: 3 in subset and 8 in subset

        result = ddmin(candidates, target)

        assert sorted(result) == [3, 8]

    def test_finds_any_two_of_three_sufficient_elements(self):
        # target holds whenever at least 2 of {2, 5, 9} are present -- ddmin should land on
        # exactly 2 of them (removing any one of the surviving pair breaks the target)
        required = {2, 5, 9}
        target = lambda subset: len(required & set(subset)) >= 2

        result = ddmin(list(range(10)), target)

        assert len(result) == 2
        assert set(result).issubset(required)

    def test_full_input_already_satisfying_target_is_returned_when_already_minimal(self):
        result = ddmin([1], lambda subset: True)

        assert result == [1]


class TestFindUnsoundFacts:
    def test_finds_two_independent_single_fact_causes(self, monkeypatch):
        # Simulates a checker where BlockA's fact and BlockB's fact are each, independently,
        # sufficient on their own to make the file invalid -- both must be removed to fix it
        data = _annotated_with(
            block_a_constancy=[{}, {"v1": "0x00"}],
            block_b_constancy=[{}, {"v3": "0x00"}],
        )
        bad_a = (("A", "BlockA"), 1, "v1", "0x00")
        bad_b = (("A", "BlockB"), 1, "v3", "0x00")

        def fake_run(cmd, **kwargs):
            probe_path = cmd[cmd.index("-i") + 1]
            with open(probe_path) as f:
                probe = json.load(f)
            facts = set(_flatten_facts(probe))
            invalid = bad_a in facts or bad_b in facts
            result = "CONSTANCY_INVALID" if invalid else "CONSTANCY_VALID"
            line = f"{probe_path},JSON_PROCESSING_OK,2,2,1,1,1,{result}"
            return _FakeCompletedProcess(stdout=line + "\n")

        monkeypatch.setattr(subprocess, "run", fake_run)

        unsound = find_unsound_facts(data, "/path/to/static_foryu")

        assert set(unsound) == {bad_a, bad_b}

    def test_a_fact_that_only_looks_bad_when_isolated_from_its_support_is_not_reported(self, monkeypatch):
        # Regression lock for the false-positive bug found during development: a legitimately
        # sound fact (fact_a) can *depend* on another fact (fact_c, e.g. its predecessor's own
        # claim) for its own soundness -- isolating fact_a with fact_c cleared makes it look
        # unsound, but it's genuinely fine whenever tested alongside fact_c. A real, unrelated
        # fact (fact_bad) is what actually makes the full file invalid. The removal-based search
        # must isolate fact_bad only, never fact_a/fact_c -- unlike the old, buggy
        # isolate-everything-else-clear approach, which would have flagged fact_a.
        data = _annotated_with(
            block_a_constancy=[{}, {"v1": "0x00"}],
            block_b_constancy=[{"v3": "0x00"}, {"v3": "0x00"}],
        )
        fact_a = (("A", "BlockA"), 1, "v1", "0x00")  # the dependent claim
        fact_c = (("A", "BlockB"), 0, "v3", "0x00")  # its supporting context (a stand-in for
                                                     # "the predecessor's own claim")
        fact_bad = (("A", "BlockB"), 1, "v3", "0x00")  # genuinely, unrelatedly unsound

        def fake_run(cmd, **kwargs):
            probe_path = cmd[cmd.index("-i") + 1]
            with open(probe_path) as f:
                probe = json.load(f)
            facts = set(_flatten_facts(probe))
            invalid = (fact_bad in facts) or (fact_a in facts and fact_c not in facts)
            result = "CONSTANCY_INVALID" if invalid else "CONSTANCY_VALID"
            line = f"{probe_path},JSON_PROCESSING_OK,2,2,1,1,1,{result}"
            return _FakeCompletedProcess(stdout=line + "\n")

        monkeypatch.setattr(subprocess, "run", fake_run)

        # Sanity check the oracle itself models the bug: isolating fact_a alone (its support
        # fact_c cleared) really does look invalid under this oracle -- the old, buggy approach
        assert _is_invalid(_build_probe(data, [fact_a]), "/path/to/static_foryu")

        unsound = find_unsound_facts(data, "/path/to/static_foryu")

        assert unsound == [fact_bad]


@_requires_static_foryu
def test_end_to_end_against_the_real_binary_finds_the_self_subtraction_fact():
    # v0 - v0 is always 0 regardless of v0's own value, but static_foryu's checker only
    # evaluates an opcode when every input is already concretely known -- it can't verify this
    # identity, so the claim on v1 is genuinely, correctly flagged unsound
    data = {
        "contracts": {
            "a.sol": {
                "A": {
                    "yulCFGJson": {
                        "type": "Object",
                        "A": {
                            "blocks": [{
                                "id": "Block0",
                                "exit": {"type": "Terminated", "targets": []},
                                "liveness": {"in": ["v0"], "out": []},
                                "instructions": [
                                    {"in": ["v0", "v0"], "op": "sub", "out": ["v40"]},
                                    {"in": ["0x20", "v40"], "op": "add", "out": ["v41"]},
                                    {"in": ["v41"], "op": "pop", "out": []},
                                ],
                                "constancy": [{}, {}, {"v41": "0x20"}, {}],
                            }],
                            "functions": {}, "subObjects": {},
                        },
                    },
                },
            },
        },
    }

    unsound = find_unsound_facts(data, DEFAULT_STATIC_FORYU)

    assert len(unsound) == 1
    scope_path, pp_index, var, value = unsound[0]
    assert scope_path == ("A", "Block0")
    assert var == "v41"
    assert value == "0x20"
