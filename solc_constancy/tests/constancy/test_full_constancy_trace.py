import shutil

import pytest

from constancy.seed_extraction import iter_block_scopes
from full_constancy_trace import process_standard_json

_requires_solc = pytest.mark.skipif(shutil.which("solc") is None, reason="solc is not available on PATH")


def _all_constancy_values(entry):
    for yul_cfg_json in entry["annotated"].values():
        for _, blocks in iter_block_scopes(yul_cfg_json):
            for block in blocks:
                for constancy_entry in block.get("constancy", []):
                    yield from constancy_entry.values()


@_requires_solc
@pytest.mark.parametrize("fixture_name,expected_literal", [
    ("loop_carried_contract_input", "0x07"),
    ("heavy_inlining_contract_input", "0x2a"),
    ("multi_use_contract_input", "0x3039"),
])
def test_trace_recovers_the_expected_constant(request, fixture_name, expected_literal, tmp_path):
    json_input = request.getfixturevalue(fixture_name)

    manifest = process_standard_json(json_input, str(tmp_path), solc_executable="solc")

    recovered_values = {value for entry in manifest for value in _all_constancy_values(entry)}
    assert expected_literal in recovered_values


@_requires_solc
@pytest.mark.parametrize("fixture_name", [
    "loop_carried_contract_input", "heavy_inlining_contract_input", "multi_use_contract_input",
])
def test_trace_runs_cleanly_and_produces_well_formed_entries(request, fixture_name, tmp_path):
    json_input = request.getfixturevalue(fixture_name)

    manifest = process_standard_json(json_input, str(tmp_path), solc_executable="solc")

    assert manifest  # at least one occurrence revealed something

    for entry in manifest:
        assert entry["annotated"]  # never an empty-contracts entry
        assert entry["restructuring_warning_count"] >= 0
        assert entry["fact_count"] >= 0

        for yul_cfg_json in entry["annotated"].values():
            for _, blocks in iter_block_scopes(yul_cfg_json):
                for block in blocks:
                    # A contract whose baseline/probe compiled byte-identical is still
                    # included (see compare_constancy.annotate_constancy_between) but skips
                    # annotation entirely -- only blocks that were actually annotated are
                    # required to have the field, and correctly shaped where they do
                    if "constancy" in block:
                        assert len(block["constancy"]) == len(block["instructions"])


@_requires_solc
@pytest.mark.parametrize("fixture_name,expected_literal", [
    ("heavy_inlining_contract_input", "0x2a"),
    ("multi_use_contract_input", "0x3039"),
])
def test_production_path_misses_what_the_trace_finds(request, fixture_name, expected_literal):
    from next_step_constancy import compute_constancy_for_next_step

    json_input = request.getfixturevalue(fixture_name)

    annotated, _ = compute_constancy_for_next_step(json_input, solc_executable="solc")
    assert annotated is not None

    production_values = {
        value
        for yul_cfg_json in annotated.values()
        for _, blocks in iter_block_scopes(yul_cfg_json)
        for block in blocks
        for entry in block["constancy"]
        for value in entry.values()
    }
    assert expected_literal not in production_values


@_requires_solc
def test_annotated_output_targets_match_block_ids_in_the_same_scope(tmp_path, heavy_inlining_contract_input):
    # Regression test for the block-name corruption bug: parser.parser.parse_block used to
    # mutate its input's block "exit.targets" in place (prefixing each with the containing
    # scope's name for its own internal representation), which -- since compare_constancy
    # parses the very CFG it's about to annotate and return -- leaked that prefix into the
    # final output, decoupling every block's own "id" from the "targets" naming used to refer
    # to it. Fixed by parsing a deep copy instead of the object being kept as output.
    manifest = process_standard_json(heavy_inlining_contract_input, str(tmp_path), solc_executable="solc")
    assert manifest

    for entry in manifest:
        for yul_cfg_json in entry["annotated"].values():
            for _, blocks in iter_block_scopes(yul_cfg_json):
                block_ids = {block["id"] for block in blocks}
                for block in blocks:
                    for target in block.get("exit", {}).get("targets", []):
                        assert target in block_ids, (
                            f"target {target!r} does not match any block id in its own scope "
                            f"({sorted(block_ids)}) -- the scope-name prefix leaked into targets")
