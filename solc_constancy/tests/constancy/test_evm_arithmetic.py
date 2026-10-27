from constancy.evm_arithmetic import evaluate, SELF_CANCELING_OPS


def test_textual_argument_order_matches_the_real_panic_error_0x11_shape():
    # The load-bearing regression test for the whole module: since solc 0.8.36, raw yulCFGJson
    # "in" lists are in textual Yul order (shift first, selector second, here). Textually this is
    # `shl(224, selector)`, i.e. `selector << 224`.
    assert evaluate("shl", ["0xe0", "0x4e487b71"]) == \
        "0x4e487b7100000000000000000000000000000000000000000000000000000000"


def test_sub_with_asymmetric_operands_reads_in_textual_order():
    # `sub(a, b) = a - b`, in_args = [a, b].
    assert evaluate("sub", ["0x10", "0x01"]) == "0x0f"


def test_gt_with_asymmetric_operands_reads_in_textual_order():
    # `gt(a, b) = a > b`, in_args = [a, b] -- 0x27 > 0x0f is true.
    assert evaluate("gt", ["0x27", "0x0f"]) == "0x01"


def test_array_allocation_size_bytes_2988_chain():
    # The real TUPProxy scope this feature was built to resolve: a whole shl/sub/gt chain over
    # literals, chained through evaluate() the same way _literal_value_table chains them.
    v0 = evaluate("shl", ["0x40", "0x01"])
    assert v0 == "0x010000000000000000"
    v1 = evaluate("sub", [v0, "0x01"])
    assert v1 == "0xffffffffffffffff"
    v2 = evaluate("gt", ["0x27", v1])
    assert v2 == "0x00"


def test_unfoldable_op_returns_none():
    assert evaluate("mload", ["0x00"]) is None


def test_arity_mismatch_returns_none():
    assert evaluate("add", ["0x01"]) is None


def test_self_canceling_ops_is_exactly_sub_and_xor():
    assert SELF_CANCELING_OPS == {"sub", "xor"}
