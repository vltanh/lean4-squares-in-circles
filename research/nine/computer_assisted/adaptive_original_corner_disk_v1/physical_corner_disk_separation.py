"""Numerical direction suggestions only; every row is reconstructed exactly."""
from fractions import Fraction as F
from itertools import product
from math import isfinite
import physical_corner_disk_rows as EXACT


def violated_parameters(point, tolerance=1e-9, denominator=65536):
    assert type(denominator) is int and denominator > 0
    candidates = []
    for original, epsilon, tau in product(range(9), (-1, 1), (-1, 1)):
        x = point[2 * original] + (epsilon * point[18 + original] - tau * point[27 + original]) / 2
        y = point[2 * original + 1] + (epsilon * point[27 + original] + tau * point[18 + original]) / 2
        if not isfinite(x) or not isfinite(y) or x * x + y * y <= float(EXACT.Q) + tolerance:
            continue
        a, b = F(round(x * denominator), denominator), F(round(y * denominator), denominator)
        if not a and not b:
            continue
        parameters = (original, epsilon, tau, a, b)
        coefficients, rhs, name = EXACT.row(*parameters)
        violation = sum(float(value) * point[index] for index, value in coefficients) - float(rhs)
        if violation > tolerance:
            candidates.append((parameters, violation))
    return sorted(candidates, key=lambda item: item[1], reverse=True)
