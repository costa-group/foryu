import pytest


@pytest.fixture
def constant_local_contract_input():
    """
    Standard-json input for a tiny contract with a local constant (`uint a = 32;`) that
    feeds an arithmetic op -- used across the constancy integration tests
    """
    source = """
pragma solidity ^0.8.17;
contract C {
    function f(uint x) public pure returns (uint) {
        uint a = 32;
        return x + a;
    }
}
"""
    return {
        "language": "Solidity",
        "sources": {"c.sol": {"content": source}},
        "settings": {
            "viaIR": True,
            "optimizer": {"enabled": True},
            "outputSelection": {"*": {"*": ["yulCFGJson"]}},
        },
    }


@pytest.fixture
def heavy_inlining_contract_input():
    """
    Standard-json input for a contract where a constant (`42`) is returned by an internal
    function inlined at two different call sites. Used by dump_steps.py/full_constancy_trace.py's
    tests: under the real DEFAULT_OPTIMIZER_SEQUENCE, this constant is folded away before any
    "T"/"m" occurrence ever runs (production annotate.py's {T, m}-only mechanism never finds
    it), but the "s" (ExpressionSimplifier) occurrences do surface it -- see PROGRESS.md's
    2026-09-18 entry.
    """
    source = """
pragma solidity ^0.8.17;
contract C {
    function k() internal pure returns (uint) { return 42; }
    function f1(uint x) public pure returns (uint) { return x + k(); }
    function f2(uint x) public pure returns (uint) { return x * k(); }
}
"""
    return {
        "language": "Solidity",
        "sources": {"c.sol": {"content": source}},
        "settings": {
            "viaIR": True,
            "optimizer": {"enabled": True},
            "outputSelection": {"*": {"*": ["yulCFGJson"]}},
        },
    }


@pytest.fixture
def multi_use_contract_input():
    """
    Standard-json input for a contract where a local constant (`12345`) is reused with six
    different operators. Used by dump_steps.py/full_constancy_trace.py's tests: same story as
    heavy_inlining_contract_input -- invisible to the production {T, m}-only mechanism, but
    surfaced by the "s" occurrences in the trace -- see PROGRESS.md's 2026-09-18 entry.
    """
    source = """
pragma solidity ^0.8.17;
contract C {
    function f(uint x) public pure returns (uint) {
        uint a = 12345;
        uint r = x;
        r = r + a;
        r = r * a;
        r = r - a;
        r = r / a;
        r = r + a;
        r = r * a;
        return r;
    }
}
"""
    return {
        "language": "Solidity",
        "sources": {"c.sol": {"content": source}},
        "settings": {
            "viaIR": True,
            "optimizer": {"enabled": True},
            "outputSelection": {"*": {"*": ["yulCFGJson"]}},
        },
    }


@pytest.fixture
def loop_carried_contract_input():
    """
    Standard-json input for a contract where a local constant (`7`) is accumulated inside a
    `for` loop, never mutated. Used by dump_steps.py/full_constancy_trace.py's tests: the 3rd "m"
    occurrence in the real DEFAULT_OPTIMIZER_SEQUENCE recovers it as a genuine mid-pipeline
    propagation event that's invisible by the end of the pipeline (its SSA name doesn't
    survive) -- see PROGRESS.md's 2026-09-18 entry.
    """
    source = """
pragma solidity ^0.8.17;
contract C {
    function f(uint x) public pure returns (uint) {
        uint a = 7;
        uint r = 0;
        for (uint i = 0; i < x; i++) {
            r += a;
        }
        return r;
    }
}
"""
    return {
        "language": "Solidity",
        "sources": {"c.sol": {"content": source}},
        "settings": {
            "viaIR": True,
            "optimizer": {"enabled": True},
            "outputSelection": {"*": {"*": ["yulCFGJson"]}},
        },
    }
