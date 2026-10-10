import json
import os
import shutil
import subprocess

import pytest

from full_liveness_trace import (
    DEFAULT_STATIC_FORYU,
    LIVENESS_CSV_FIELDS,
    _step_positions,
    trace_liveness_for_input,
)

_requires_solc = pytest.mark.skipif(shutil.which("solc") is None, reason="solc is not available on PATH")


class _FakeCompletedProcess:
    def __init__(self, stdout=""):
        self.stdout = stdout
        self.stderr = ""
        self.returncode = 0


class TestStepPositions:
    def test_covers_every_alphabetic_position_not_just_occurrences(self):
        # Unlike dump_steps.find_occurrences (gated to a few chosen letters), every alphabetic
        # character is a candidate position here -- that's the whole point of this script
        positions = _step_positions("dfT[r]c:m")

        # indices: d=0 f=1 T=2 [=3 r=4 ]=5 c=6 :=7 m=8 -- brackets and the colon are skipped
        assert positions == [0, 1, 2, 4, 6, 8]

    def test_skips_spaces_too(self):
        assert _step_positions("d m") == [0, 2]


@_requires_solc
class TestTraceLivenessForInput:
    def test_writes_one_row_per_step_position(self, tmp_path, constant_local_contract_input, monkeypatch):
        # Stub static_foryu itself (not solc) so this test doesn't depend on the real binary
        # existing, while still exercising a real compilation per position
        def fake_run(cmd, **kwargs):
            return _FakeCompletedProcess(
                stdout="file,JSON_PROCESSING_OK,3,10,1000,500,700,LIVENESS_VALID\n")
        monkeypatch.setattr(subprocess, "run", fake_run)

        sequence = "dTm"
        rows = trace_liveness_for_input(constant_local_contract_input, str(tmp_path),
                                        base_sequence=sequence, solc_executable="solc",
                                        static_foryu="/fake/static_foryu", input_label="c.sol")

        assert len(rows) == 3  # one per alphabetic position in "dTm"
        assert [r["position"] for r in rows] == [0, 1, 2]
        assert [r["step"] for r in rows] == ["d", "T", "m"]
        for row in rows:
            assert set(row.keys()) == set(LIVENESS_CSV_FIELDS)
            assert row["compile_seconds"] > 0
            assert row["liveness_result"] == "LIVENESS_VALID"
            assert row["error"] == ""

    def test_does_not_leave_any_intermediate_json_files_behind(self, tmp_path, constant_local_contract_input,
                                                                monkeypatch):
        monkeypatch.setattr(subprocess, "run",
                            lambda cmd, **kw: _FakeCompletedProcess(
                                stdout="file,JSON_PROCESSING_OK,1,1,1,1,1,LIVENESS_VALID\n"))

        trace_liveness_for_input(constant_local_contract_input, str(tmp_path), base_sequence="dT",
                                 solc_executable="solc", static_foryu="/fake/static_foryu")

        on_disk = {p.name for p in tmp_path.iterdir()}
        assert on_disk == {"liveness.csv", "manifest.json"}

    def test_manifest_is_rewritten_with_one_entry_per_position(self, tmp_path, constant_local_contract_input,
                                                               monkeypatch):
        monkeypatch.setattr(subprocess, "run",
                            lambda cmd, **kw: _FakeCompletedProcess(
                                stdout="file,JSON_PROCESSING_OK,1,1,1,1,1,LIVENESS_VALID\n"))

        trace_liveness_for_input(constant_local_contract_input, str(tmp_path), base_sequence="dTm",
                                 solc_executable="solc", static_foryu="/fake/static_foryu",
                                 input_label="c.sol")

        with open(tmp_path / "manifest.json") as f:
            manifest = json.load(f)
        assert len(manifest) == 3
        assert [entry["position"] for entry in manifest] == [0, 1, 2]
        assert all(entry["status"] == "done" for entry in manifest)
        assert all(entry["input_file"] == "c.sol" for entry in manifest)

    def test_a_compile_failure_is_recorded_as_an_error_row_not_raised(self, tmp_path,
                                                                      constant_local_contract_input):
        # An unusable solc binary -- every position should fail to compile and record an error
        # row rather than raising
        rows = trace_liveness_for_input(constant_local_contract_input, str(tmp_path), base_sequence="dT",
                                        solc_executable="/nonexistent/solc",
                                        static_foryu="/fake/static_foryu")

        assert len(rows) == 2
        assert all(row["error"] != "" for row in rows)
        assert all(row["liveness_result"] == "" for row in rows)


@_requires_solc
def test_end_to_end_against_the_real_static_foryu_binary(tmp_path, constant_local_contract_input):
    if not os.path.isfile(DEFAULT_STATIC_FORYU):
        pytest.skip("static_foryu binary not found at the default path")

    rows = trace_liveness_for_input(constant_local_contract_input, str(tmp_path), base_sequence="dT",
                                    solc_executable="solc", input_label="c.sol")

    assert len(rows) == 2
    assert any(row["liveness_result"] == "LIVENESS_VALID" for row in rows)
