"""
U256 arithmetic for the 25 EVM opcodes affecting pure arithmetic/bitwise/comparison
"""
from typing import List, Optional

MODULUS = 1 << 256


def _to_t(z: int) -> int:
    return z % MODULUS


def _signed(v: int) -> int:
    return ((v + (1 << 255)) % MODULUS) - (1 << 255)


def _op_add(a, b): return _to_t(a + b)
def _op_sub(a, b): return _to_t(a - b)
def _op_mul(a, b): return _to_t(a * b)


def _op_div(a, b):
    return 0 if b == 0 else _to_t(a // b)


def _op_sdiv(a, b):
    if b == 0:
        return 0
    return _to_t(_signed(a) // _signed(b))


def _op_mod(a, b):
    return 0 if b == 0 else _to_t(a % b)


def _op_smod(a, b):
    if b == 0:
        return 0
    return _to_t(_signed(a) % _signed(b))


def _op_exp(a, b): return pow(a, b, MODULUS)
def _op_not(a): return _to_t(MODULUS - a - 1)
def _op_lt(a, b): return 1 if a < b else 0
def _op_gt(a, b): return 1 if a > b else 0
def _op_slt(a, b): return 1 if _signed(a) < _signed(b) else 0
def _op_sgt(a, b): return 1 if _signed(a) > _signed(b) else 0
def _op_eq(a, b): return 1 if a == b else 0
def _op_iszero(a): return 1 if a == 0 else 0
def _op_and(a, b): return a & b
def _op_or(a, b): return a | b
def _op_xor(a, b): return a ^ b


def _op_byte(n, x):
    if n >= 32:
        return 0
    return (x // (256 ** (31 - n))) % 256


def _op_shl(shift, value):
    if shift >= 256:
        return 0
    return _to_t(value * (1 << shift))


def _op_shr(shift, value):
    if shift >= 256:
        return 0
    return _to_t(value // (1 << shift))


def _op_sar(shift, value):
    sv = _signed(value)
    if shift >= 256:
        return MODULUS - 1 if sv < 0 else 0
    return _to_t(sv // (1 << shift))


def _op_addmod(a, b, m):
    return 0 if m == 0 else (a + b) % m


def _op_mulmod(a, b, m):
    return 0 if m == 0 else (a * b) % m


def _op_signextend(i, x):
    if i >= 31:
        return x
    size = 8 * (i + 1)
    byte = (x // (1 << (8 * i))) % 256
    sign_bit = byte // 128
    extend = (MODULUS - (1 << size)) if sign_bit == 1 else 0
    return _to_t((x % (1 << size)) + extend)


FOLDABLE_OPS = {
    "add": _op_add, "sub": _op_sub, "mul": _op_mul, "div": _op_div,
    "sdiv": _op_sdiv, "mod": _op_mod, "smod": _op_smod, "exp": _op_exp,
    "not": _op_not, "lt": _op_lt, "gt": _op_gt, "slt": _op_slt,
    "sgt": _op_sgt, "eq": _op_eq, "iszero": _op_iszero, "and": _op_and,
    "or": _op_or, "xor": _op_xor, "byte": _op_byte, "shl": _op_shl,
    "shr": _op_shr, "sar": _op_sar, "addmod": _op_addmod,
    "mulmod": _op_mulmod, "signextend": _op_signextend,
}


def evaluate(op: str, in_args: List[str]) -> Optional[str]:
    """
    The result of applying op to in_args -- an instruction's raw "in" list, exactly as read
    (this function owns the reversal, see the module docstring) -- as a lowercase hex string, or
    None if op isn't one of FOLDABLE_OPS or in_args doesn't match its arity.
    """
    func = FOLDABLE_OPS.get(op)
    if func is None:
        return None
    try:
        operands = [int(v, 16) for v in reversed(in_args)]
        return _to_hex(func(*operands))
    except (TypeError, ValueError):
        return None


def _to_hex(value: int) -> str:
    """
    value as a byte-aligned hex string (even number of digits, minimum one byte) -- solc's own
    convention throughout every real yulCFGJson literal seen this session ("0x00", "0x0f",
    "0x0100", never "0x0" or "0xf"). Plain hex(value) doesn't zero-pad, which silently breaks
    every exact-string check elsewhere in this module that compares against "0x00" (confirmed by
    a real regression: hex(0) == "0x0" made a genuinely-zero condition fail to match "0x00" and
    fold onto the wrong branch target).
    """
    digits = format(value, "x")
    if len(digits) % 2 != 0:
        digits = "0" + digits
    return "0x" + digits
