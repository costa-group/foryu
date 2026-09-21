import shutil

import pytest

from constancy.annotate import compute_constancy
from constancy.occurrence_trace import (
    PROPAGATION_STEPS_TO_TRACE,
    enumerate_occurrences,
    find_occurrences,
    trace_all_occurrences,
    truncate_sequence,
)
from constancy.seed_extraction import iter_block_scopes
from execution.sol_compilation import DEFAULT_OPTIMIZER_SEQUENCE


# --- solc-free unit tests -----------------------------------------------------------------

def test_find_occurrences_matches_all_positions():
    assert find_occurrences("aTbTcT", "T") == [1, 3, 5]


def test_find_occurrences_none():
    assert find_occurrences("abc", "T") == []


def test_truncate_sequence_no_open_bracket():
    assert truncate_sequence("abcT", 3, include_cut=False) == "abc"
    assert truncate_sequence("abcT", 3, include_cut=True) == "abcT"


def test_truncate_sequence_closes_open_bracket_excluding_cut():
    # "x[yTz]w" cut right before the T: prefix is "x[y", with one bracket still open
    assert truncate_sequence("x[yTz]w", 3, include_cut=False) == "x[y]"


def test_truncate_sequence_closes_open_bracket_including_cut():
    assert truncate_sequence("x[yTz]w", 3, include_cut=True) == "x[yT]"


def test_truncate_sequence_nested_brackets():
    # "x[y[Tz]w]v" cut at the T (index 4): one level of nesting still open either way
    assert truncate_sequence("x[y[Tz]w]v", 4, include_cut=False) == "x[y[]]"
    assert truncate_sequence("x[y[Tz]w]v", 4, include_cut=True) == "x[y[T]]"


def test_enumerate_occurrences_against_real_default_sequence():
    occurrences = enumerate_occurrences()

    expected_count = sum(DEFAULT_OPTIMIZER_SEQUENCE.count(step) for step in PROPAGATION_STEPS_TO_TRACE)
    assert len(occurrences) == expected_count

    positions = [occurrence["position"] for occurrence in occurrences]
    assert positions == sorted(positions)
    assert len(set(positions)) == len(positions)

    for occurrence in occurrences:
        assert occurrence["seq_after"][occurrence["position"]] == occurrence["step"]
        for seq in (occurrence["seq_before"], occurrence["seq_after"]):
            assert seq.count("[") == seq.count("]")
            # isolate_cleanup_sequence guarantees an explicit cleanup delimiter everywhere,
            # whether it was already there (an occurrence past the real colon) or just added
            assert seq.count(":") == 1

    for step in PROPAGATION_STEPS_TO_TRACE:
        step_indices = [occurrence["step_index"] for occurrence in occurrences if occurrence["step"] == step]
        assert step_indices == list(range(len(step_indices)))

    indices = [occurrence["index"] for occurrence in occurrences]
    assert indices == list(range(len(occurrences)))


def test_occurrences_within_the_real_cleanup_are_traced_without_a_double_colon():
    # DEFAULT_OPTIMIZER_SEQUENCE's own real, deliberate cleanup tail (after its one genuine
    # colon) already contains "T", "c", and "m" -- find_occurrences/enumerate_occurrences scan
    # the whole sequence regardless of where the colon falls, so these are traced exactly like
    # any pre-colon occurrence, and isolate_cleanup_sequence must leave their already-present
    # colon alone rather than adding a second one
    real_colon_position = DEFAULT_OPTIMIZER_SEQUENCE.index(":")
    occurrences = enumerate_occurrences()

    post_colon = [occurrence for occurrence in occurrences if occurrence["position"] > real_colon_position]
    assert {occurrence["step"] for occurrence in post_colon} == {"T", "c", "m"}
    assert len(post_colon) == 3  # exactly one post-colon occurrence each of T, c, m today

    for occurrence in post_colon:
        for seq in (occurrence["seq_before"], occurrence["seq_after"]):
            assert seq.count(":") == 1
            assert seq.index(":") == real_colon_position


# --- solc-skipped integration tests --------------------------------------------------------
# (applied per-test, not as a module-level pytestmark, since the unit tests above must always
# run even without solc on PATH)

_requires_solc = pytest.mark.skipif(shutil.which("solc") is None, reason="solc is not available on PATH")


def _all_constancy_values(snapshot):
    for yul_cfg_json in snapshot["contracts"].values():
        for _, blocks in iter_block_scopes(yul_cfg_json):
            for block in blocks:
                for entry in block["constancy"]:
                    yield from entry.values()


@_requires_solc
@pytest.mark.parametrize("fixture_name,expected_literal", [
    ("loop_carried_contract_input", "0x07"),
    ("heavy_inlining_contract_input", "0x2a"),
    ("multi_use_contract_input", "0x3039"),
])
def test_trace_recovers_the_expected_constant(request, fixture_name, expected_literal):
    json_input = request.getfixturevalue(fixture_name)

    snapshots = trace_all_occurrences(json_input, solc_executable="solc")

    recovered_values = {value for snapshot in snapshots for value in _all_constancy_values(snapshot)}
    assert expected_literal in recovered_values


@_requires_solc
@pytest.mark.parametrize("fixture_name", [
    "loop_carried_contract_input", "heavy_inlining_contract_input", "multi_use_contract_input",
])
def test_trace_runs_cleanly_and_produces_well_formed_snapshots(request, fixture_name):
    json_input = request.getfixturevalue(fixture_name)

    snapshots = trace_all_occurrences(json_input, solc_executable="solc")

    assert snapshots  # at least one occurrence changed something

    for snapshot in snapshots:
        assert snapshot["contracts"]  # trace_occurrence never returns an empty-contracts snapshot
        assert snapshot["restructuring_warning_count"] >= 0
        assert snapshot["seed_fact_count"] >= 0
        # No blanket "T"/"m"/"c" always report 0" assumption here: once sequences are properly
        # isolated (isolate_cleanup_sequence), any of the four steps can restructure block/scope
        # numbering -- this count exists precisely to surface that per-occurrence, not to
        # enforce a rule per step type (see PROGRESS.md)

        for yul_cfg_json in snapshot["contracts"].values():
            for _, blocks in iter_block_scopes(yul_cfg_json):
                for block in blocks:
                    assert "constancy" in block
                    assert len(block["constancy"]) == len(block["instructions"])


@_requires_solc
@pytest.mark.parametrize("fixture_name,expected_literal", [
    ("heavy_inlining_contract_input", "0x2a"),
    ("multi_use_contract_input", "0x3039"),
])
def test_production_path_misses_what_the_trace_finds(request, fixture_name, expected_literal):
    json_input = request.getfixturevalue(fixture_name)

    result, _ = compute_constancy(json_input, solc_executable="solc")
    assert result is not None

    production_values = {
        value
        for yul_cfg_json in result.values()
        for _, blocks in iter_block_scopes(yul_cfg_json)
        for block in blocks
        for entry in block["constancy"]
        for value in entry.values()
    }
    assert expected_literal not in production_values
