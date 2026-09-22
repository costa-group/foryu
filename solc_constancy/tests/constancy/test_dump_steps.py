from constancy.dump_steps import (
    PROPAGATION_STEPS_TO_TRACE,
    enumerate_occurrences,
    find_occurrences,
    truncate_sequence,
)
from execution.sol_compilation import DEFAULT_OPTIMIZER_SEQUENCE


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
