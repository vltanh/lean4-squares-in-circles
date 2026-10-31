#!/usr/bin/env python3
"""Exact rational verifier for the 24-row loaded-ray angular lemma.

No floating point or numerical optimization is used. Every radical is
enclosed between rational numbers whose squares are checked explicitly.
The Markdown table is the certificate checked by default; --print-table
prints the reproducible table for review.
"""

from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import argparse
import re


SCALE = 10**8
TABLE_SCALE = 10**4


def sqrt_bounds(value):
    assert value >= 0
    scaled = value * SCALE**2
    k = isqrt(scaled.numerator // scaled.denominator)
    lo, hi = F(k, SCALE), F(k + 1, SCALE)
    assert lo * lo <= value < hi * hi
    return lo, hi


def ceil_scaled(value):
    value *= TABLE_SCALE
    return -((-value.numerator) // value.denominator)


def div_upper(numerator_upper, denominator_bounds):
    lo, hi = denominator_bounds
    assert lo > 0
    return numerator_upper / (lo if numerator_upper >= 0 else hi)


def a0_upper(t):
    _, root17_hi = sqrt_bounds(F(17))
    numerator_hi = (root17_hi - 2) * t - 1
    den = sqrt_bounds(1 + t*t)
    return div_upper(numerator_hi, (2*den[0], 2*den[1]))


def a45_upper(t):
    return div_upper(2*t - 1, sqrt_bounds(2 + 2*t*t))


def b_upper(z):
    assert z >= 0
    _, radical_hi = sqrt_bounds(17*z*z + 2*z + 17)
    return z * (radical_hi - 1 - z) / (2 * (1 + z*z)) - F(1, 2)


def certificate_rows():
    result = []
    for i in range(24):
        lo, hi = F(3*i, 80), F(3*(i+1), 80)
        z = (9 - 10*lo) / (10 + 9*lo)
        u0, u45, ub = [ceil_scaled(x) for x in
                       (a0_upper(hi), a45_upper(hi), b_upper(z))]
        total = max(u0, u45) + ub
        assert total < 0
        result.append((i, u0, u45, ub, total))
    assert F(3*24, 80) == F(9, 10)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--print-table', action='store_true')
    args = parser.parse_args()
    rows = certificate_rows()
    if args.print_table:
        print('| i | U_0 | U_45 | U_B | max(U_0,U_45)+U_B |')
        print('| --- | ---: | ---: | ---: | ---: |')
        for row in rows:
            print('| ' + ' | '.join(map(str, row)) + ' |')
        return
    manuscript = Path(__file__).with_name('LOADED_THREE_RAY_ANGLE_BOUND.md')
    table_rows = []
    pattern = re.compile(r'^\| (\d+) \| (-?\d+) \| (-?\d+) \| (-?\d+) \| (-?\d+) \|$')
    for line in manuscript.read_text().splitlines():
        match = pattern.fullmatch(line)
        if match:
            table_rows.append(tuple(map(int, match.groups())))
    assert table_rows == rows, 'The printed certificate differs from exact recomputation'

    x, y = F(15, 104), F(17, 27)
    tan3 = (3*x - x**3)/(1 - 3*x*x)
    tan2 = 2*y/(1 - y*y)
    assert tan3 * tan2 == F(44371071, 46405216) < 1
    assert F(14) > F(133, 36)**2
    print('PASS: 24 rational intervals, all endpoint bounds, and printed rows.')
    print('Largest certified upper bound:', F(max(row[-1] for row in rows), TABLE_SCALE))
    print('Seven-loaded/one-D angle product:', tan3*tan2, '< 1')


if __name__ == '__main__':
    main()
