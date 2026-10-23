#!/usr/bin/env python3
"""Exact arithmetic check of SIX_CENTRAL_SQUARES.md; no dependencies."""
from fractions import Fraction as F
from itertools import combinations

CENTRES = [
    (F(1167, 1000), F(-19, 100)),
    (F(587, 1000), F(801, 1000)),
    (F(-103, 250), F(111, 100)),
    (F(-293, 250), F(91, 500)),
    (F(-763, 1000), F(-463, 500)),
    (F(51, 125), F(-223, 200)),
]
HALF_ANGLE_TANGENTS = [F(2, 5), F(11, 20), F(11, 20),
                       F(13, 50), F(1, 20), F(29, 40)]
U = [((1-t*t)/(1+t*t), 2*t/(1+t*t)) for t in HALF_ANGLE_TANGENTS]
V = [(-u[1], u[0]) for u in U]

def dot(a, b):
    return sum(x*y for x, y in zip(a, b))

for p, u, v in zip(CENTRES, U, V):
    assert dot(u, u) == dot(v, v) == 1 and dot(u, v) == 0
    a, b = abs(dot(p, u)), abs(dot(p, v))
    closest_squared = max(a-F(1, 2), 0)**2 + max(b-F(1, 2), 0)**2
    farthest_squared = (a+F(1, 2))**2 + (b+F(1, 2))**2
    assert closest_squared < F(49, 200) < F(1, 4)
    assert farthest_squared < F(15, 4) < F(9, 2)

for i, j in combinations(range(6), 2):
    delta = tuple(y-x for x, y in zip(CENTRES[i], CENTRES[j]))
    required_gap = (1 + abs(dot(U[i], U[j])) + abs(dot(U[i], V[j]))) / 2
    actual_gap = max(abs(dot(delta, axis)) for axis in [U[i], V[i], U[j], V[j]])
    assert actual_gap - required_gap > F(9, 1000)

print('Verified: six separated unit squares, each meets open B(0, 1/2), all in D_(15/4).')
