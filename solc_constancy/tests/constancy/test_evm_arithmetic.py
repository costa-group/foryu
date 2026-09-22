from constancy.evm_arithmetic import evaluate


def test_reversed_argument_order_matches_the_real_panic_error_0x11_shape():
    # The load-bearing regression test for the whole module: raw yulCFGJson "in" lists are
    # reversed relative to natural Yul syntax (selector first, shift second, here) -- see the
    # module docstring for the two independent real-contract confirmations. Textually this is
    # `shl(224, selector)`, i.e. `selector << 224`.
    assert evaluate("shl", ["0x4e487b71", "0xe0"]) == \
        "0x4e487b7100000000000000000000000000000000000000000000000000000000"


def test_sub_with_asymmetric_operands_reads_in_reversed_order():
    # Textually `sub(a, b) = a - b`; in reversed-"in"-order this is in_args = [b, a].
    assert evaluate("sub", ["0x01", "0x10"]) == "0x0f"


def test_gt_with_asymmetric_operands_reads_in_reversed_order():
    # Textually `gt(a, b) = a > b`; in_args = [b, a] reversed -- 0x27 > 0x0f is true.
    assert evaluate("gt", ["0x0f", "0x27"]) == "0x01"


def test_array_allocation_size_bytes_2988_chain():
    # The real TUPProxy scope this feature was built to resolve: a whole shl/sub/gt chain over
    # literals, chained through evaluate() the same way _literal_value_table chains them.
    v0 = evaluate("shl", ["0x01", "0x40"])
    assert v0 == "0x010000000000000000"
    v1 = evaluate("sub", ["0x01", v0])
    assert v1 == "0xffffffffffffffff"
    v2 = evaluate("gt", [v1, "0x27"])
    assert v2 == "0x00"


def test_unfoldable_op_returns_none():
    assert evaluate("mload", ["0x00"]) is None


def test_arity_mismatch_returns_none():
    assert evaluate("add", ["0x01"]) is None
