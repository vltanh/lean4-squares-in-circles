#!/usr/bin/env python3
"""Exact rational audit of 2026-10-12 hand cap threshold improvements.

Not a numerical search, a certificate for a continuous theorem, or a Lean proof.
Each inequality audits a strict rational margin in the Markdown hand arguments.
"""
from fractions import Fraction as Q

R2 = Q(9789, 2500)
RHI = Q(9894, 5000)
RT2LO = Q(7071, 5000)

assert RHI**2 > R2
assert RT2LO**2 < 2
assert Q(141, 100)**2 < 2
assert Q(191, 100) == Q(141, 100) + Q(1, 2)


def b2_upper(h):
    return (3 * RHI**2 - 2 * RHI * h - h**2) / 4


# HUMAN_PERPENDICULAR_TRIPLE_IMPROVED.md
H = Q(1, 11)
HMAX = Q(5813, 20000)
assert (1 + HMAX)**2 + Q(9, 4) - R2 == Q(70969, 400000000)
assert (Q(191, 100) + H) / 2 == Q(2201, 2200) > 1
assert (RHI + HMAX) / 2 == Q(45389, 40000)
assert (RHI - H) / 2 < 1
assert Q(16867, 10000)**2 - b2_upper(H) == Q(2799701, 12100000000)
assert 2 * RT2LO - RHI + H == Q(6466, 6875)
assert Q(6466, 6875) - Q(9405, 10000) == Q(1, 110000)
assert 3 * Q(9405, 10000) - Q(16867, 10000) - Q(45389, 40000) == Q(3, 40000)
assert Q(16867, 10000) - Q(9405, 10000) < 1
assert Q(25, 48)**2 - (R2 - Q(21, 11)**2) == Q(51481, 174240000)

# HUMAN_TRIPLE_CAP_TWO_OUTER_IMPROVED.md
H = Q(13, 100)
BHI = Q(3349, 2000)
ELLO = Q(9796, 10000)
assert (RHI - H) / 2 == Q(2311, 2500)
assert BHI**2 - b2_upper(H) == Q(6017, 100000000)
assert 2 * RT2LO - RHI + H == ELLO
assert 2 * (1 - Q(2311, 2500)) - (Q(69, 50) - 1)**2 == Q(17, 2500)
S = H - BHI + 2 * ELLO + 1
assert S == Q(14147, 10000) and S**2 - 2 == Q(137609, 100000000)
K = 3 * ELLO - BHI
assert K == Q(12643, 10000)
assert K - Q(3, 4) > 0
assert H + Q(69, 50) - K > 0
F = (H + Q(69, 100))**2 + (K - Q(69, 100))**2
assert F == Q(100222049, 100000000) > 1

# HUMAN_TRIPLE_CAP_QUADRANT_IMPROVED.md
H = Q(17, 80)
BHI = Q(164779, 100000)
assert BHI**2 - b2_upper(H) == Q(56833, 5000000000)
assert 2 * RT2LO - RHI + H == Q(10621, 10000) > 1
assert H - Q(1, 2) < -Q(1, 4)  # plateau-frame comparison
assert 2 + RT2LO - RHI + H - BHI == Q(11, 100000) > 0

print("All exact rational cap-improvement margins checked.")
