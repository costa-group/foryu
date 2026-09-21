import shutil

import pytest

from constancy.annotate import compute_constancy
from constancy.seed_extraction import DEFAULT_OPTIMIZER_SEQUENCE, iter_block_scopes

pytestmark = pytest.mark.skipif(shutil.which("solc") is None, reason="solc is not available on PATH")


def _all_blocks(yul_cfg_json):
    for _, blocks in iter_block_scopes(yul_cfg_json):
        yield from blocks


def test_constancy_field_present_and_correctly_shaped_on_every_block(constant_local_contract_input):
    result, _ = compute_constancy(constant_local_contract_input, solc_executable="solc")

    assert result is not None
    assert result  # at least one contract compiled

    for yul_cfg_json in result.values():
        for block in _all_blocks(yul_cfg_json):
            assert "constancy" in block
            assert len(block["constancy"]) == len(block["instructions"])


def test_more_aggressive_baseline_recovers_the_local_constant(constant_local_contract_input):
    # Stripping T/m out of the baseline (an artificial, more aggressive variant than the
    # real default -- see PROGRESS.md) forces the analysis to actually recover facts, so
    # this checks the full seed-extraction -> propagation -> annotation round trip end to
    # end against real solc output, not just the JSON shape
    no_prop_sequence = DEFAULT_OPTIMIZER_SEQUENCE.replace("T", "").replace("m", "")

    result, _ = compute_constancy(constant_local_contract_input, solc_executable="solc",
                               base_sequence=no_prop_sequence)

    assert result is not None

    recovered_values = {value
                        for yul_cfg_json in result.values()
                        for block in _all_blocks(yul_cfg_json)
                        for entry in block["constancy"]
                        for value in entry.values()}

    # 32 == 0x20, the local `uint a = 32;`
    assert "0x20" in recovered_values
