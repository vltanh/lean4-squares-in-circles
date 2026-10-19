#!/usr/bin/env python3
"""Exact endpoint audit of the forbidden seven-outer C-rooted m=7 stress path.

The geometric implications are proved in HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md
and HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md. This verifies the strict
rational contradiction only, not a numerical packing search.
"""
from fractions import Fraction as F

# Opposite central neighbor center-ray gap > pi/2+1/13.
# Outer-center pair gap > pi/4-1/500 implies missing seventh
# circular gap < pi/2+6/500 = pi/2+3/250.
assert F(6,500)==F(3,250)
assert F(1,13)-F(3,250)==F(211,3250)>0

# Original weaker m=7 angular budget is now superseded.
assert F(1,13)>F(1,800)
assert F(4,25)/F(283,200)**2==F(6400,80089)>F(1,13)

# Original 35 labeled C-degree-2 paths comprise 7 per m=3..7.
# Excluding the m=7 support removes 7 of them, leaving 28.
assert 5*7-7==28
print("PASS: m=7 full seven-outer stressed path angular bounds incompatible")
