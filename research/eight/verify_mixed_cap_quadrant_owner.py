#!/usr/bin/env python3
"""Exact rational endpoint audit of the forced mixed-cap quadrant owner.

Only checks stated rational comparisons; the hand theorem proves
the frame-uniform geometric statements.
"""
from fractions import Fraction as F

x=F(3,4)
tangent_lower=x+x**3/3+2*x**5/15
assert tangent_lower==F(2361,2560)
assert F(19,24)*tangent_lower==F(14953,20480)
assert F(71,100)**2>F(1,2)
clearance=F(14953,20480)-F(71,100)
assert clearance==F(2061,102400)
assert clearance-F(1,50)==F(13,102400)>0
print("PASS: arbitrary-frame mixed-cap outer whole-quadrant rational margin")
