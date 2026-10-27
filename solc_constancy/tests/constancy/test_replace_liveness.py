import copy
import csv
import json
import sys

import full_liveness_recheck
from replace_liveness import replace_liveness, replace_liveness_in_file_data


def _block(block_id, instructions, exit_, entries=None):
    block = {"id": block_id, "type": "BuiltinCall", "instructions": instructions, "exit": exit_,
             "liveness": {"in": [], "out": []}}
    if entries is not None:
        block["entries"] = entries
    return block


def _instr(op, in_, out):
    return {"op": op, "in": in_, "out": out}


def _yul_cfg(blocks, functions=None, sub_objects=None):
    obj = {"blocks": blocks, "functions": functions or {}}
    if sub_objects is not None:
        obj["subObjects"] = sub_objects
    return {"obj": obj, "type": "Object"}


def _liveness(yul_cfg, block_id, path=("obj",)):
    node = yul_cfg
    for key in path:
        node = node[key]
    return next(b["liveness"] for b in node["blocks"] if b["id"] == block_id)


TERMINATED = {"type": "Terminated"}


def _cond_in_predecessor_cfg():
    return _yul_cfg([
        _block("Block0", [_instr("calldataload", ["0x00"], ["v0"])], {"type": "Jump", "targets": ["Block1"]}),
        _block("Block1", [], {"type": "ConditionalJump", "cond": "v0", "targets": ["Block2", "Block3"]}),
        _block("Block2", [_instr("revert", ["0x00", "0x00"], [])], TERMINATED),
        _block("Block3", [_instr("stop", [], [])], TERMINATED),
    ])


class TestReplaceLiveness:
    def test_straight_line_only_later_uses_are_live(self):
        cfg = _yul_cfg([
            _block("Block0", [_instr("calldataload", ["0x00"], ["v0"]),
                              _instr("calldataload", ["0x20"], ["v1"]),
                              _instr("mstore", ["v1", "0x00"], [])],
                   {"type": "Jump", "targets": ["Block1"]}),
            _block("Block1", [_instr("sstore", ["v0", "0x00"], [])], {"type": "MainExit"}),
        ])
        replace_liveness(cfg)
        assert _liveness(cfg, "Block0") == {"in": [], "out": ["v0"]}
        assert _liveness(cfg, "Block1") == {"in": ["v0"], "out": []}

    def test_condition_defined_in_predecessor_is_live(self):
        # The condition is only an exit field: it becomes a use once the JUMPI is inserted
        cfg = _cond_in_predecessor_cfg()
        replace_liveness(cfg)
        assert _liveness(cfg, "Block0") == {"in": [], "out": ["v0"]}
        assert _liveness(cfg, "Block1") == {"in": ["v0"], "out": []}

    def test_phi_output_live_in_and_inputs_live_out_of_their_predecessor(self):
        cfg = _yul_cfg([
            _block("Block0", [_instr("calldataload", ["0x00"], ["v0"])],
                   {"type": "ConditionalJump", "cond": "v0", "targets": ["Block1", "Block2"]}),
            _block("Block1", [_instr("calldataload", ["0x20"], ["v1"])], {"type": "Jump", "targets": ["Block3"]}),
            _block("Block2", [_instr("calldataload", ["0x40"], ["v2"])], {"type": "Jump", "targets": ["Block3"]}),
            _block("Block3", [_instr("PhiFunction", ["v1", "v2"], ["phi3"]),
                              _instr("mstore", ["phi3", "0x00"], [])],
                   {"type": "MainExit"}, entries=["Block1", "Block2"]),
        ])
        replace_liveness(cfg)
        assert _liveness(cfg, "Block1") == {"in": [], "out": ["v1"]}
        assert _liveness(cfg, "Block2") == {"in": [], "out": ["v2"]}
        assert _liveness(cfg, "Block3") == {"in": ["phi3"], "out": []}

    def test_function_return_values_live_out_and_no_return_address(self):
        functions = {"f": {"arguments": ["v0"], "returns": ["v1"], "entry": "Block0", "blocks": [
            _block("Block0", [_instr("add", ["0x01", "v0"], ["v1"])],
                   {"type": "FunctionReturn", "returnValues": ["v1"]}),
        ]}}
        cfg = _yul_cfg([
            _block("Block0", [_instr("calldataload", ["0x00"], ["v0"]),
                              _instr("f", ["v0"], ["v1"]),
                              _instr("mstore", ["v1", "0x00"], [])],
                   {"type": "MainExit"}),
        ], functions=functions)
        replace_liveness(cfg)
        # solc's convention: the exit happens after the block, so returned variables are live-out
        assert _liveness(cfg, "Block0", ("obj", "functions", "f")) == {"in": ["v0"], "out": ["v1"]}
        assert _liveness(cfg, "Block0") == {"in": [], "out": []}

    def test_sub_object_blocks_are_replaced(self):
        sub = _cond_in_predecessor_cfg()["obj"]
        cfg = _yul_cfg([_block("Block0", [_instr("stop", [], [])], TERMINATED)],
                       sub_objects={"obj_deployed": sub, "type": "Object"})
        stats = replace_liveness(cfg)
        assert _liveness(cfg, "Block1", ("obj", "subObjects", "obj_deployed")) == {"in": ["v0"], "out": []}
        assert stats["blocks"] == 5

    def test_only_liveness_changes_and_stats(self):
        cfg = _cond_in_predecessor_cfg()
        original = copy.deepcopy(cfg)
        stats = replace_liveness(cfg)
        for block, original_block in zip(cfg["obj"]["blocks"], original["obj"]["blocks"]):
            # The parser rewrites exit targets in place: it must only see a copy
            assert {k: v for k, v in block.items() if k != "liveness"} == \
                   {k: v for k, v in original_block.items() if k != "liveness"}
        assert stats == {"blocks": 4, "blocks_changed": 2, "blocks_unreached": 0}

    def test_block_not_reaching_an_exit_gets_empty_sets(self):
        cfg = _yul_cfg([
            _block("Block0", [_instr("calldataload", ["0x00"], ["v0"])],
                   {"type": "ConditionalJump", "cond": "v0", "targets": ["Block1", "Block2"]}),
            _block("Block1", [_instr("stop", [], [])], TERMINATED),
            _block("Block2", [_instr("sstore", ["v0", "0x00"], [])], {"type": "Jump", "targets": ["Block2"]}),
        ])
        cfg["obj"]["blocks"][2]["liveness"] = {"in": ["v0"], "out": ["v0"]}
        stats = replace_liveness(cfg)
        assert _liveness(cfg, "Block2") == {"in": [], "out": []}
        assert stats["blocks_unreached"] == 1

    def test_standard_json_output_shape(self):
        data = {"contracts": {"c.sol": {"I": {"yulCFGJson": None},
                                        "C": {"yulCFGJson": _cond_in_predecessor_cfg()}}}}
        stats = replace_liveness_in_file_data(data)
        assert stats["blocks"] == 4
        assert _liveness(data["contracts"]["c.sol"]["C"]["yulCFGJson"], "Block1") == {"in": ["v0"], "out": []}


class TestFullLivenessRecheck:
    def _prior_run(self, tmp_path):
        positions = tmp_path / "prior" / "c1" / "positions"
        positions.mkdir(parents=True)
        for name in ["pos_000_disabled.json", "pos_002_disabled.json"]:
            (positions / name).write_text(json.dumps(
                {"contracts": {"c.sol": {"C": {"yulCFGJson": _cond_in_predecessor_cfg()}}}}))
        return tmp_path / "prior"

    def test_writes_liveness_csv_per_contract(self, tmp_path, monkeypatch):
        def fake_check(data, static_foryu):
            return {"json_status": "JSON_PROCESSING_OK", "liveness_result": "LIVENESS_VALID"}

        monkeypatch.setattr(full_liveness_recheck, "_run_static_foryu_liveness", fake_check)
        prior, out = self._prior_run(tmp_path), tmp_path / "out"
        monkeypatch.setattr(sys, "argv", ["full_liveness_recheck.py", str(prior), "--output-dir", str(out),
                                          "-cpus", "1", "--keep-json"])
        full_liveness_recheck.main()

        rows = list(csv.DictReader(open(out / "c1" / "liveness.csv")))
        assert [(r["position"], r["variant"], r["step"]) for r in rows] == [("0", "disabled", "d"),
                                                                            ("2", "disabled", "D")]
        assert all(r["liveness_result"] == "LIVENESS_VALID" and r["blocks_changed"] == "2" for r in rows)
        kept = json.loads((out / "c1" / "positions" / "pos_002_disabled.json").read_text())
        assert _liveness(kept["contracts"]["c.sol"]["C"]["yulCFGJson"], "Block1") == {"in": ["v0"], "out": []}
        summary = list(csv.DictReader(open(out / "results.csv")))
        assert summary[0]["contract"] == "c1" and summary[0]["position_count"] == "2"

    def test_error_is_recorded_not_raised(self, tmp_path):
        bad = tmp_path / "c1" / "positions" / "pos_000_disabled.json"
        bad.parent.mkdir(parents=True)
        bad.write_text("not json")
        row = full_liveness_recheck.recheck_position((str(bad), "c1", str(tmp_path / "out"), "unused", False, "repo"))
        assert row["error"].startswith("JSONDecodeError")
