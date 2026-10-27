import csv
import json
import sys

import yul_cfg_stats
from test_replace_liveness import _block, _cond_in_predecessor_cfg, _instr, _yul_cfg


def test_counts_blocks_functions_and_sub_objects():
    functions = {"f": {"arguments": ["v0"], "returns": [], "entry": "Block0", "blocks": [
        _block("Block0", [_instr("PhiFunction", ["v0", "v1"], ["phi0"]), _instr("pop", ["phi0"], [])],
               {"type": "FunctionReturn", "returnValues": []}, entries=["Block1", "Block2"]),
    ]}}
    sub = _cond_in_predecessor_cfg()["obj"]
    cfg = _yul_cfg([_block("Block0", [_instr("stop", [], [])], {"type": "Terminated"})],
                   functions=functions, sub_objects={"obj_deployed": sub, "type": "Object"})
    counts = yul_cfg_stats.Counter()
    yul_cfg_stats.count_yul_cfg(cfg, counts)
    assert counts == {"nblocks": 6, "ninstrs": 6, "nphis": 1}


def test_main_writes_one_row_per_position_with_compile_time(tmp_path, monkeypatch):
    contract = tmp_path / "run" / "c1"
    (contract / "positions").mkdir(parents=True)
    for name in ["pos_000_disabled.json", "pos_138_enabled.json"]:
        (contract / "positions" / name).write_text(json.dumps(
            {"contracts": {"c.sol": {"I": {"yulCFGJson": None}, "C": {"yulCFGJson": _cond_in_predecessor_cfg()}}}}))
    (contract / "positions" / "pos_001_disabled.json").write_text("not json")
    (contract / "liveness.csv").write_text("position,variant,compile_seconds\n0,disabled,1.5\n138,enabled,2.5\n")
    out = tmp_path / "stats.csv"
    monkeypatch.setattr(sys, "argv", ["yul_cfg_stats.py", str(tmp_path / "run"), "-o", str(out), "-cpus", "1"])
    yul_cfg_stats.main()

    rows = list(csv.DictReader(open(out)))
    assert [(r["position"], r["variant"], r["step"], r["nblocks"], r["ninstrs"], r["compile_seconds"])
            for r in rows] == [("0", "disabled", "d", "4", "3", "1.5"),
                               ("1", "disabled", "f", "", "", ""),
                               ("138", "enabled", "u", "4", "3", "2.5")]
    assert rows[1]["error"].startswith("JSONDecodeError")
