"""Exact supporting halfplanes for each unchanged original physical corner."""
from fractions import Fraction as F
from math import isqrt

Q = F(1105, 256)
PREFIX = 'physical_corner_disk_'


def sqrt_upper(value, bits=40):
    value = F(value)
    assert value >= 0 and type(bits) is int and bits >= 0
    numerator = value.numerator << (2 * bits)
    denominator = value.denominator
    root = isqrt(numerator // denominator)
    if root * root * denominator < numerator:
        root += 1
    return F(root, 1 << bits)


def row(original, epsilon, tau, a, b):
    assert type(original) is int and 0 <= original < 9
    assert epsilon in (-1, 1) and tau in (-1, 1)
    a, b = F(a), F(b)
    assert a or b
    upper = sqrt_upper(Q * (a * a + b * b))
    coefficients = {2 * original: a, 2 * original + 1: b,
                    18 + original: (epsilon * a + tau * b) / 2,
                    27 + original: (epsilon * b - tau * a) / 2}
    name = f'{PREFIX}{original}_{epsilon}_{tau}_{a}_{b}_{upper}'
    return tuple((k, v) for k, v in sorted(coefficients.items()) if v), upper, name
