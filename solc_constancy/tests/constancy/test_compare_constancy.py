from constancy.compare_constancy import annotate_constancy_between


def _baseline_and_probe():
    # Mirrors test_seed_extraction.py's TestExtractSeedFactsForContract fixtures, extended with
    # the "liveness"/"type"/contract-name wrapping annotate_constancy_between's full pipeline
    # (parse_CFG_from_json_dict, compute_constancy_for_cfg) needs: baseline inlines a literal
    # directly (v0's LiteralAssignment vanishes), probe references it at the same argument
    # position -- a genuine substitution, exercising both fact analysis and annotation for real.
    baseline = {
        "ContractA": {
            "type": "Object",
            "Main": {
                "blocks": [{"id": "Block0", "exit": {"type": "Terminated", "targets": []},
                            "liveness": {"in": [], "out": []},
                            "instructions": [
                                {"in": ["0x20"], "op": "LiteralAssignment", "out": ["v0"]},
                                {"in": ["v2", "v0"], "op": "add", "out": ["v1"]},
                            ]}],
                "functions": {}, "subObjects": {},
            },
        },
    }
    probe = {
        "ContractA": {
            "type": "Object",
            "Main": {
                "blocks": [{"id": "Block0", "exit": {"type": "Terminated", "targets": []},
                            "liveness": {"in": [], "out": []},
                            "instructions": [
                                {"in": ["v2", "0x20"], "op": "add", "out": ["v1"]},
                            ]}],
                "functions": {}, "subObjects": {},
            },
        },
    }
    return baseline, probe


def test_stats_out_accumulates_fact_analysis_and_annotation_seconds():
    baseline, probe = _baseline_and_probe()
    stats = {}

    annotated, _ = annotate_constancy_between(baseline, probe, stats_out=stats)

    assert stats["fact_analysis_seconds"] > 0
    assert stats["annotation_seconds"] > 0
    # the actual substitution is still found -- timing instrumentation changes nothing else
    assert annotated["ContractA"]["Main"]["blocks"][0]["constancy"][1] == {"v0": "0x20"}


def test_stats_out_accumulates_across_multiple_contracts():
    baseline, probe = _baseline_and_probe()
    baseline["ContractB"] = baseline["ContractA"]
    probe["ContractB"] = probe["ContractA"]
    stats = {}

    annotate_constancy_between(baseline, probe, stats_out=stats)

    # two contracts processed with the same stats dict -- accumulated, not overwritten
    assert stats["fact_analysis_seconds"] > 0
    assert stats["annotation_seconds"] > 0


def test_byte_identical_contract_still_records_annotation_seconds():
    # The _annotate_with_no_facts shortcut path (baseline == probe) substitutes for both fact
    # analysis and annotation together -- charged to annotation_seconds, never fact_analysis
    baseline, _ = _baseline_and_probe()
    probe = baseline
    stats = {}

    annotate_constancy_between(baseline, probe, stats_out=stats)

    assert stats["annotation_seconds"] > 0
    assert "fact_analysis_seconds" not in stats


def test_without_stats_out_is_unaffected():
    # Omitting stats_out (the default) must change nothing about the existing return value
    baseline, probe = _baseline_and_probe()

    annotated, warning_count = annotate_constancy_between(baseline, probe)

    assert warning_count == 0
    assert annotated["ContractA"]["Main"]["blocks"][0]["constancy"][1] == {"v0": "0x20"}


def test_a_verified_fact_is_not_marked_unverified():
    baseline, probe = _baseline_and_probe()

    annotated, _ = annotate_constancy_between(baseline, probe)

    block = annotated["ContractA"]["Main"]["blocks"][0]
    assert block["constancy"][1] == {"v0": "0x20"}
    assert block["constancy_unverified"] == [{} for _ in block["constancy"]]


def test_an_unverified_fact_stays_in_constancy_and_is_marked_wherever_it_propagates():
    # v17 = add(v98, v99) can't be re-derived locally, but the probe shows it as 0x64: it is kept
    # in "constancy" (sound, from the correspondence), and every propagated copy -- including
    # Block1's live-in copy -- is listed in "constancy_unverified" too, not just the seed.
    def scope(block0_instrs, block1_instrs):
        return {"ContractA": {"type": "Object", "Main": {
            "blocks": [
                {"id": "Block0", "exit": {"type": "Jump", "targets": ["Block1"]},
                 "liveness": {"in": ["v98", "v99"], "out": ["v17"]}, "instructions": block0_instrs},
                {"id": "Block1", "exit": {"type": "Terminated", "targets": []},
                 "liveness": {"in": ["v17"], "out": []}, "instructions": block1_instrs},
            ],
            "functions": {}, "subObjects": {}}}}
    baseline = scope([{"in": ["v98", "v99"], "op": "add", "out": ["v17"]},
                      {"in": ["v17", "0x00"], "op": "mstore", "out": []}],
                     [{"in": ["v17", "0x20"], "op": "mstore", "out": []}])
    probe = scope([{"in": ["0x64", "0x00"], "op": "mstore", "out": []}],
                  [{"in": ["0x64", "0x20"], "op": "mstore", "out": []}])

    annotated, _ = annotate_constancy_between(baseline, probe)

    blocks = {b["id"]: b for b in annotated["ContractA"]["Main"]["blocks"]}
    for block_id in ("Block0", "Block1"):
        constancy, unverified = blocks[block_id]["constancy"], blocks[block_id]["constancy_unverified"]
        assert any(entry.get("v17") == "0x64" for entry in constancy)
        assert [{var: val for var, val in entry.items() if var == "v17"} for entry in constancy] == unverified
