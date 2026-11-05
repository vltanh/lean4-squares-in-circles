"""Universal support rows for the center of each physical original square.

All four corners must lie in the closed disk with squared radius1105/256.
No mask, branch, interval box or other original is a premise.
"""
from fractions import Fraction as F
from math import isqrt

RADIUS = F(91, 60)
PREFIX = 'physical_center_disk_'


def sqrt_upper(value, bits=40):
    """Round an exact nonnegative square root upward on a dyadic grid."""
    value = F(value)
    assert value >= 0 and type(bits) is int and bits >= 0
    numerator = value.numerator << (2 * bits)
    denominator = value.denominator
    root = isqrt(numerator // denominator)
    if root * root * denominator < numerator:
        root += 1
    return F(root, 1 << bits)


def row(original, a, b):
    """Return a*x_original+b*y_original <= s; zero directions are allowed."""
    assert type(original) is int and 0 <= original < 9
    a, b = F(a), F(b)
    upper = sqrt_upper(RADIUS * RADIUS * (a * a + b * b))
    co = tuple((index, value) for index, value in
               ((2 * original, a), (2 * original + 1, b)) if value)
    name = f'{PREFIX}{original}_{a}_{b}_{upper}'
    return co, upper, name
