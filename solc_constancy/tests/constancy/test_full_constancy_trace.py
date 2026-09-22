import json
import os
import shutil

import pytest

from constancy.seed_extraction import count_leading_phis, iter_block_scopes
from full_constancy_trace import _wrap_in_original_structure, process_standard_json

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
                        # one entry per real (non-leading-phi) instruction, plus the leading
                        # live-in slot that also absorbs every leading PhiFunction
                        instructions = block["instructions"]
                        assert len(block["constancy"]) == len(instructions) - count_leading_phis(instructions) + 1


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


class TestWrapInOriginalStructure:
    def test_reshapes_the_flattened_dict_into_solc_own_contracts_nesting(self):
        yul_cfg_dict = {"A": {"type": "Object", "marker": "a"}, "B": {"type": "Object", "marker": "b"}}
        structure = {"a.sol": ["A"], "b.sol": ["B"]}

        wrapped = _wrap_in_original_structure(yul_cfg_dict, structure)

        assert wrapped == {
            "contracts": {
                "a.sol": {"A": {"yulCFGJson": {"type": "Object", "marker": "a"}}},
                "b.sol": {"B": {"yulCFGJson": {"type": "Object", "marker": "b"}}},
            },
        }

    def test_omits_a_structure_entry_with_no_matching_yul_cfg_dict_key(self):
        # e.g. a contract that compiled to a null yulCFGJson -- excluded from the flattened dict
        # already (see sol_compilation._process_json_output), so it's simply skipped here too
        wrapped = _wrap_in_original_structure({}, {"a.sol": ["Interface"]})

        assert wrapped == {"contracts": {}}


@_requires_solc
def test_output_directory_splits_results_from_intermediate_files(tmp_path, heavy_inlining_contract_input):
    manifest = process_standard_json(heavy_inlining_contract_input, str(tmp_path), solc_executable="solc")
    assert manifest

    results_dir = tmp_path / "results"
    intermediate_dir = tmp_path / "intermediate"

    results_files = {p.name for p in results_dir.iterdir()}
    intermediate_files = {p.name for p in intermediate_dir.iterdir()}

    assert results_files, "no annotated files were written"
    assert all(name.endswith("_annotated.json") for name in results_files)
    assert "manifest.json" in intermediate_files
    assert any(name.endswith("_before.json") for name in intermediate_files)
    assert any(name.endswith("_after.json") for name in intermediate_files)
    assert not any(name.endswith("_annotated.json") for name in intermediate_files)

    with open(intermediate_dir / "manifest.json") as f:
        disk_manifest = json.load(f)
    for entry in disk_manifest:
        assert os.path.isfile(results_dir / entry["annotated_file"])
        assert os.path.isfile(intermediate_dir / entry["before_file"])
        assert os.path.isfile(intermediate_dir / entry["after_file"])


@_requires_solc
def test_annotated_file_on_disk_has_the_original_solc_output_nesting(tmp_path, heavy_inlining_contract_input):
    manifest = process_standard_json(heavy_inlining_contract_input, str(tmp_path), solc_executable="solc")
    assert manifest

    entry = manifest[0]
    with open(tmp_path / "results" / entry["annotated_file"]) as f:
        on_disk = json.load(f)

    assert set(on_disk.keys()) == {"contracts"}
    for contract_name, in_memory_yul_cfg in entry["annotated"].items():
        found = None
        for contracts_in_file in on_disk["contracts"].values():
            if contract_name in contracts_in_file:
                found = contracts_in_file[contract_name]["yulCFGJson"]
        assert found is not None, f"{contract_name} missing from the on-disk contracts nesting"
        assert found == in_memory_yul_cfg
