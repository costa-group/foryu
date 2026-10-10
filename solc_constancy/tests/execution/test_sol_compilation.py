import subprocess

import pytest

from execution.sol_compilation import SolidityCompilation, run_command


def _compilation():
    return SolidityCompilation(None, "solc")


class TestRunCommand:
    def test_passes_timeout_through_to_communicate(self, monkeypatch):
        calls = {}

        class _FakePopen:
            def __init__(self, *args, **kwargs):
                pass

            def communicate(self, timeout=None):
                calls["timeout"] = timeout
                return b"out", b""

        monkeypatch.setattr(subprocess, "Popen", _FakePopen)

        outs, err = run_command("solc --version", timeout=300)

        assert calls["timeout"] == 300
        assert outs == "out"

    def test_kills_and_reaps_the_process_on_timeout_then_reraises(self, monkeypatch):
        killed = []

        class _FakePopen:
            def __init__(self, *args, **kwargs):
                self._calls = 0

            def communicate(self, timeout=None):
                self._calls += 1
                if self._calls == 1:
                    raise subprocess.TimeoutExpired(cmd="solc", timeout=timeout)
                return b"", b""

            def kill(self):
                killed.append(True)

        monkeypatch.setattr(subprocess, "Popen", _FakePopen)

        with pytest.raises(subprocess.TimeoutExpired):
            run_command("solc --standard-json slow.json", timeout=5)

        assert killed == [True]


class TestProcessJsonOutput:
    def test_builds_the_file_contract_structure_alongside_the_flattened_dict(self):
        output_dict = {
            "contracts": {
                "a.sol": {"A": {"yulCFGJson": {"type": "Object", "A": {}}}},
                "b.sol": {"B": {"yulCFGJson": {"type": "Object", "B": {}}}},
            },
        }
        compilation = _compilation()

        correct, json_dict = compilation._process_json_output(output_dict, "", None)

        assert correct is True
        assert json_dict == {"A": {"type": "Object", "A": {}}, "B": {"type": "Object", "B": {}}}
        assert compilation.last_contract_structure == {"a.sol": ["A"], "b.sol": ["B"]}

    def test_excludes_a_contract_with_a_null_yulcfgjson_from_both_the_dict_and_the_structure(self):
        output_dict = {
            "contracts": {
                "a.sol": {"A": {"yulCFGJson": None}, "Interface": {"yulCFGJson": {"type": "Object"}}},
            },
        }
        compilation = _compilation()

        _, json_dict = compilation._process_json_output(output_dict, "", None)

        assert "A" not in json_dict
        assert compilation.last_contract_structure == {"a.sol": ["Interface"]}

    def test_resets_the_structure_on_a_compile_error(self):
        compilation = _compilation()
        compilation.last_contract_structure = {"stale.sol": ["Stale"]}
        output_dict = {"errors": [{"severity": "error", "message": "boom"}], "contracts": {}}

        correct, json_dict = compilation._process_json_output(output_dict, "", None)

        assert correct is False
        assert compilation.last_contract_structure == {}
