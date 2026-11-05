"""Independent center-row decoding and squared-support check.

Imports no producer, optimizer, legacy geometry or propagated-state code.
The hand proof supplies the universal norm bound for the physical center.
"""
from fractions import Fraction as F

PREFIX = 'physical_center_disk_'


def verify_literal(literal):
    coefficients, rhs, name = literal
    assert isinstance(name, str) and name.startswith(PREFIX)
    fields = name[len(PREFIX):].split('_')
    assert len(fields) == 4
    original = int(fields[0])
    assert fields[0] == str(original) and 0 <= original < 9
    horizontal, vertical, support = map(F, fields[1:])
    assert support >= 0 and F(rhs) == support
    assert 3600 * support * support >= 8281 * (horizontal * horizontal + vertical * vertical)
    # Reconstruct the two original center coordinates literally. No frame
    # column, product auxiliary or child-specific interval may enter this row.
    expected = []
    if horizontal:
        expected.append((2 * original, horizontal))
    if vertical:
        expected.append((2 * original + 1, vertical))
    assert tuple(coefficients) == tuple(expected)
    return literal
