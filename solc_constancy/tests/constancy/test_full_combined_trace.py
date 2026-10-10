import shutil

import pytest

from constancy.dump_steps import enumerate_occurrences, truncate_sequence, PROPAGATION_STEPS_TO_TRACE
from constancy.seed_extraction import isolate_cleanup_sequence
from execution.sol_compilation import DEFAULT_OPTIMIZER_SEQUENCE
from full_combined_trace import trace_combined_for_input
from full_liveness_trace import _step_positions

_requires_solc = pytest.mark.skipif(shutil.which("solc") is None, reason="solc is not available on PATH")


class TestReuseCorrectness:
    def test_every_occurrences_seq_before_matches_the_preceding_sweep_position(self):
        # The whole point of this script: an occurrence's baseline is read off the sweep's own
        # already-computed compile at the immediately preceding alphabetic position, instead of
        # being recompiled -- this only holds if that position's own truncation is exactly the
        # same sequence dump_steps.enumerate_occurrences would otherwise compile fresh as
        # "seq_before" (a cosmetic whitespace difference is fine: solc ignores it, confirmed by
        # compiling both and diffing the real output -- see PROGRESS.md/TASKS.md).
        positions = _step_positions(DEFAULT_OPTIMIZER_SEQUENCE)
        position_to_index = {p: i for i, p in enumerate(positions)}

        for occurrence in enumerate_occurrences(DEFAULT_OPTIMIZER_SEQUENCE, PROPAGATION_STEPS_TO_TRACE):
            index = position_to_index[occurrence["position"]]
            if index == 0:
                continue  # no preceding position to reuse; handled as a dedicated fresh compile
            previous_position = positions[index - 1]
            reused = isolate_cleanup_sequence(
                truncate_sequence(DEFAULT_OPTIMIZER_SEQUENCE, previous_position, include_cut=True))
            # Equal up to whitespace: a space is never itself an alphabetic "position", so it can
            # fall between previous_position and this occurrence's own position without being
            # reflected in the reused string -- solc's own step-sequence parser ignores spaces.
            assert reused.replace(" ", "") == occurrence["seq_before"].replace(" ", "")


@_requires_solc
class TestTraceCombinedForInput:
    def test_sweeps_every_position_and_checks_liveness_for_each(self, tmp_path, constant_local_contract_input):
        stats = trace_combined_for_input(constant_local_contract_input, str(tmp_path), solc_executable="solc")

        expected_positions = len(_step_positions(DEFAULT_OPTIMIZER_SEQUENCE))
        assert stats["position_count"] == expected_positions

        import csv
        with open(tmp_path / "liveness.csv") as f:
            rows = list(csv.DictReader(f))
        # one row per position, plus one extra for the last position's "enabled" variant
        assert len(rows) == expected_positions + 1
        assert sum(1 for r in rows if r["variant"] == "enabled") == 1
        assert sum(1 for r in rows if r["variant"] == "disabled") == expected_positions
        # the "enabled" row must be for the very last (highest-position) sweep entry
        enabled_row = next(r for r in rows if r["variant"] == "enabled")
        disabled_positions = [int(r["position"]) for r in rows if r["variant"] == "disabled"]
        assert int(enabled_row["position"]) == max(disabled_positions)

    def test_writes_a_compiled_json_file_per_position(self, tmp_path, constant_local_contract_input):
        trace_combined_for_input(constant_local_contract_input, str(tmp_path), solc_executable="solc")

        positions_dir = tmp_path / "positions"
        expected_positions = len(_step_positions(DEFAULT_OPTIMIZER_SEQUENCE))
        disabled_files = list(positions_dir.glob("*_disabled.json"))
        enabled_files = list(positions_dir.glob("*_enabled.json"))
        assert len(disabled_files) == expected_positions
        assert len(enabled_files) == 1

    def test_only_t_m_c_s_occurrences_get_constancy_results(self, tmp_path, constant_local_contract_input):
        stats = trace_combined_for_input(constant_local_contract_input, str(tmp_path), solc_executable="solc")

        assert stats["occurrence_count"] == len(enumerate_occurrences(DEFAULT_OPTIMIZER_SEQUENCE,
                                                                       PROPAGATION_STEPS_TO_TRACE))
        # every annotated result on disk must correspond to a real T/m/c/s occurrence filename
        results_dir = tmp_path / "results"
        for annotated_file in results_dir.glob("*_annotated.json"):
            assert any(letter in annotated_file.name for letter in PROPAGATION_STEPS_TO_TRACE)

    def test_a_too_short_compile_timeout_is_treated_as_a_compile_failure_not_a_hang(
            self, tmp_path, constant_local_contract_input):
        stats = trace_combined_for_input(constant_local_contract_input, str(tmp_path),
                                         solc_executable="solc", compile_timeout=0.0001)

        assert stats["manifest_entry_count"] == 0
        import csv
        with open(tmp_path / "liveness.csv") as f:
            rows = list(csv.DictReader(f))
        assert all(r["error"] for r in rows)
