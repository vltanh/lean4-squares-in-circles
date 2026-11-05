"""Untrusted radial suggestions for the universal physical center rows."""
from fractions import Fraction as F
from math import hypot, isfinite

RADIUS = 91 / 60


def violated_parameters(point, denominator=4096, tolerance=1e-7):
    """Suggest (original,a,b) parameters; exact replay decides validity.

Only the existing first18 center coordinates are read. The rational grid
and floating tolerance affect discovery alone, and impose no proof premise.
"""
    assert len(point) >= 18 and type(denominator) is int and denominator > 0
    assert tolerance >= 0
    result = []
    for original in range(9):
        x, y = float(point[2 * original]), float(point[2 * original + 1])
        if not isfinite(x) or not isfinite(y):
            continue
        radius = hypot(x, y)
        if radius <= RADIUS + tolerance:
            continue
        ia, ib = round(denominator * x / radius), round(denominator * y / radius)
        a, b = ia / denominator, ib / denominator
        violation = a * x + b * y - RADIUS * hypot(a, b)
        if violation > tolerance:
            result.append(((original, F(ia, denominator), F(ib, denominator)), violation))
    result.sort(key=lambda item: item[1], reverse=True)
    return result
