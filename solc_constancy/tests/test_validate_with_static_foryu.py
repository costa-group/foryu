import os
import subprocess

import pytest

import json

from validate_with_static_foryu import DEFAULT_STATIC_FORYU, _find_annotated_files, _run_static_foryu, \
    _strip_unverified

_requires_static_foryu = pytest.mark.skipif(not os.path.isfile(DEFAULT_STATIC_FORYU),
                                            reason="static_foryu binary not found at the default path")


class _FakeCompletedProcess:
    def __init__(self, stdout="", stderr="", returncode=0):
        self.stdout = stdout
        self.stderr = stderr
        self.returncode = returncode


def _annotated(constancy, unverified):
    block = {"id": "Block0", "instructions": [], "constancy": constancy, "constancy_unverified": unverified}
    return {"contracts": {"a.sol": {"A": {"yulCFGJson": {"A_1": {"blocks": [block], "functions": {},
                                                               "subObjects": {}}}}}}}


class TestStripUnverified:
    def test_removes_only_the_unverified_facts_and_the_field_itself(self):
        data = _annotated([{"v0": "0x80"}, {"v0": "0x80", "v17": "0x64"}], [{}, {"v17": "0x64"}])

        removed = _strip_unverified(data)

        block = data["contracts"]["a.sol"]["A"]["yulCFGJson"]["A_1"]["blocks"][0]
        assert removed == 1
        assert block["constancy"] == [{"v0": "0x80"}, {"v0": "0x80"}]
        assert "constancy_unverified" not in block


class TestRunStaticForyu:
    def test_checks_the_verified_subset_separately(self, monkeypatch, tmp_path):
        path = tmp_path / "f.json"
        path.write_text(json.dumps(_annotated([{"v17": "0x64"}], [{"v17": "0x64"}])))
        verdicts = iter(["CONSTANCY_INVALID", "CONSTANCY_VALID"])
        seen_inputs = []

        def fake_run(cmd, **kw):
            seen_inputs.append(json.load(open(cmd[-1])))
            return _FakeCompletedProcess(stdout=f"{cmd[-1]},JSON_PROCESSING_OK,1,0,0,0,0,{next(verdicts)}\n")
        monkeypatch.setattr(subprocess, "run", fake_run)

        row = _run_static_foryu(str(path), "/path/to/static_foryu")

        assert row["constancy_result"] == "CONSTANCY_INVALID"
        assert row["constancy_result_verified"] == "CONSTANCY_VALID"
        assert row["unverified_fact_count"] == 1
        stripped_block = seen_inputs[1]["contracts"]["a.sol"]["A"]["yulCFGJson"]["A_1"]["blocks"][0]
        assert stripped_block["constancy"] == [{}]

    def test_parses_a_full_csv_line(self, monkeypatch):
        line = ("some/file.json,JSON_PROCESSING_OK,293,948,15320063,"
               "8288860,17141819,CONSTANCY_VALID")
        monkeypatch.setattr(subprocess, "run", lambda *a, **kw: _FakeCompletedProcess(stdout=line + "\n"))

        row = _run_static_foryu("some/file.json", "/path/to/static_foryu")

        assert row["annotated_file"] == "some/file.json"
        assert row["wall_seconds"] > 0
        assert row["returncode"] == 0
        assert row["json_status"] == "JSON_PROCESSING_OK"
        assert row["nblocks"] == "293"
        assert row["ninstrs"] == "948"
        assert row["constancy_result"] == "CONSTANCY_VALID"
        assert row["constancy_extract_ns"] == "8288860"
        assert row["constancy_check_ns"] == "17141819"
        assert row["error"] == ""

    def test_a_json_processing_error_is_recorded_even_though_exit_code_is_0(self, monkeypatch):
        # Confirmed directly against the real binary: JSON_PROCESSING_ERROR still exits 0 --
        # pass/fail must come from the parsed verdict field, never the exit code
        line = "bad/file.json,JSON_PROCESSING_ERROR,,,,,,"
        monkeypatch.setattr(subprocess, "run", lambda *a, **kw: _FakeCompletedProcess(stdout=line + "\n", returncode=0))

        row = _run_static_foryu("bad/file.json", "/path/to/static_foryu")

        assert row["returncode"] == 0
        assert row["json_status"] == "JSON_PROCESSING_ERROR"
        assert row["constancy_result"] != "CONSTANCY_VALID"

    def test_empty_stdout_is_recorded_as_a_crash(self, monkeypatch):
        # Matches run_experiments.sh's own convention: empty stdout means static_foryu crashed
        monkeypatch.setattr(subprocess, "run", lambda *a, **kw: _FakeCompletedProcess(stdout="", stderr="Fatal error"))

        row = _run_static_foryu("some/file.json", "/path/to/static_foryu")

        assert "CRASH" in row["error"]
        assert row["json_status"] == ""

    def test_a_subprocess_launch_failure_is_recorded_not_raised(self, monkeypatch):
        def _raise(*args, **kwargs):
            raise FileNotFoundError("no such file")
        monkeypatch.setattr(subprocess, "run", _raise)

        row = _run_static_foryu("some/file.json", "/path/to/nonexistent")

        assert "no such file" in row["error"]


class TestFindAnnotatedFiles:
    def test_flat_layout_directly_under_output_dir(self, tmp_path):
        results_dir = tmp_path / "results"
        results_dir.mkdir()
        (results_dir / "occ_000_T0_annotated.json").write_text("{}")
        (results_dir / "occ_001_s0_annotated.json").write_text("{}")
        (tmp_path / "intermediate").mkdir()
        (tmp_path / "intermediate" / "manifest.json").write_text("[]")

        found = _find_annotated_files(str(tmp_path))

        assert len(found) == 2
        assert all(f.endswith("_annotated.json") for f in found)

    def test_nested_folder_batch_layout(self, tmp_path):
        for contract in ("contractA", "contractB"):
            results_dir = tmp_path / contract / "results"
            results_dir.mkdir(parents=True)
            (results_dir / "occ_000_T0_annotated.json").write_text("{}")

        found = _find_annotated_files(str(tmp_path))

        assert len(found) == 2

    def test_no_results_directories_found(self, tmp_path):
        assert _find_annotated_files(str(tmp_path)) == []


@_requires_static_foryu
def test_end_to_end_against_the_real_binary(tmp_path):
    # A minimal, validly-shaped annotated file -- real static_foryu output for this exact shape
    # isn't asserted here (that's the whole point of the external checker), just that invoking
    # it produces a well-formed row
    annotated = {
        "contracts": {
            "a.sol": {
                "A": {
                    "yulCFGJson": {
                        "type": "Object",
                        "A": {
                            "blocks": [{"id": "Block0", "exit": {"type": "Terminated", "targets": []},
                                       "liveness": {"in": [], "out": []}, "instructions": [],
                                       "constancy": [{}]}],
                            "functions": {}, "subObjects": {},
                        },
                    },
                },
            },
        },
    }
    annotated_file = tmp_path / "occ_000_T0_annotated.json"
    import json
    annotated_file.write_text(json.dumps(annotated))

    row = _run_static_foryu(str(annotated_file), DEFAULT_STATIC_FORYU)

    assert row["wall_seconds"] > 0
    assert row["json_status"] in ("JSON_PROCESSING_OK", "JSON_PROCESSING_ERROR")
