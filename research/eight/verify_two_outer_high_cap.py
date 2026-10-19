#!/usr/bin/env python3
"""Exact arithmetic audit for HUMAN_TWO_OUTER_HIGH_CAP.md.

Not a numerical packing search, interval cover, or Lean proof:
only the displayed rational comparisons of the hand argument.
"""
from fractions import Fraction as F

q=F(9789,2500)
r0=F(283,200)
a0=F(197,200)
assert F(173,1000)**2-(1-a0*a0)==F(77,500000)>0
assert r0*r0+r0+F(1,2)-q==F(65,40000)>0
assert F(131,100)**2-(q-F(297,200)**2)==F(229,40000)>0
assert r0*r0-F(81,100)**2-F(29,25)**2==F(21,40000)>0
upper=r0*r0+1-2*a0*F(29,25)+2*F(81,100)*F(173,1000)
assert upper==F(199457,200000)<1
print("PASS: full-frame high-cap two-outer center margin", 1-upper)
