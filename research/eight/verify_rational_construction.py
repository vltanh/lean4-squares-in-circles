#!/usr/bin/env python3
"""Exact construction certificate: eight unit squares fit below R=1.978771.

Python 3 standard library only. No floating point, numerical optimization,
external package, or Lean is used in verification. This proves an UPPER bound,
not optimality. Run: python research/eight/verify_rational_construction.py

The coordinate discovery is documented in CANDIDATE_RECONSTRUCTION.md.
"""
from fractions import Fraction as F
from itertools import combinations, product

R = F(1978771, 1000000)
TAN_HALF = F(967147047, 15625000000)
CENTERS = [
    (F(1001239567, 800000000), F(-21032834321, 50000000000)),
    (F(115847888369, 100000000000), F(28967166679, 50000000000)),
    (F(15847886369, 100000000000), F(350000007, 1000000000)),
    (F(15847886369, 100000000000), F(1350000027, 1000000000)),
    (F(-140212271901, 100000000000), F(-908041199, 20000000000)),
    (F(-84152115631, 100000000000), F(19091959201, 20000000000)),
    (F(24595354161, 100000000000), F(-45328779497, 50000000000)),
    (F(-74641314477, 100000000000), F(-25747448271, 25000000000)),
]


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1]


def perpendicular(e):
    return -e[1], e[0]


def verify():
    h = TAN_HALF
    tilted = ((1-h*h)/(1+h*h), 2*h/(1+h*h))
    axes = [(F(1), F(0))] * 6 + [tilted, tilted]
    circle_margins, pair_margins = [], []
    for i, (center, e) in enumerate(zip(CENTERS, axes)):
        f = perpendicular(e)
        if dot(e, e) != 1 or dot(f, f) != 1 or dot(e, f) != 0:
            raise AssertionError(f"Non-orthonormal square frame {i+1}")
        for a, b in product((-1, 1), repeat=2):
            p = tuple(center[k] + (a*e[k]+b*f[k])/2 for k in range(2))
            margin = R*R-dot(p, p)
            if margin <= 0:
                raise AssertionError(f"Circle containment fails: square {i+1}")
            circle_margins.append(margin)
    for i, j in combinations(range(8), 2):
        ei, ej = axes[i], axes[j]
        fi, fj = perpendicular(ei), perpendicular(ej)
        delta = tuple(CENTERS[j][k]-CENTERS[i][k] for k in range(2))
        margins = []
        for n in (ei, fi, ej, fj):
            half_width_sum = (abs(dot(n, ei))+abs(dot(n, fi))
                              +abs(dot(n, ej))+abs(dot(n, fj)))/2
            margins.append(abs(dot(n, delta))-half_width_sum)
        margin = max(margins)
        if margin <= 0:
            raise AssertionError(f"No certified separator for pair {i+1},{j+1}")
        pair_margins.append(margin)
    # Coarse reserves, checked exactly, make the claim easy to reproduce.
    if min(circle_margins) <= F(4, 10**7):
        raise AssertionError("Circle reserve smaller than the reported bound")
    if min(pair_margins) < F(1, 50000000):
        raise AssertionError("Pair reserve smaller than the reported bound")
    print("Verified: 8 orthonormal unit-square frames, 32 vertices, 28 pairs.")
    print("Every vertex has squared-radius reserve > 4/10000000.")
    print("Every pair has a separating-axis reserve >= 1/50000000.")
    print("Therefore eight unit squares fit strictly inside R=1978771/1000000.")
    print("This is a construction certificate; no lower-bound claim is made.")


if __name__ == '__main__':
    verify()
