#!/usr/bin/env python3
"""Exact rational audit of HUMAN_MIXED_HIGH_CAP_37_100.md.

The genuine arbitrary-frame continuum proof is in the cited hand theorem.
This checks its rational rectangle margins, not a numerical case cover.
"""
from fractions import Fraction as F

q=F(9789,2500)
H=F(37,100)
assert H>F(7,24)
assert F(143,100)**2-(q-(1+H)**2)==F(31,5000)>0
assert F(123,100)**2-(F(283,200)**2-F(7,10)**2)==F(27,40000)>0
assert (H+F(1,2))==F(87,100)
assert F(123,100)-F(87,100)==F(9,25)
assert F(93,100)**2+F(9,25)**2==F(1989,2000)
assert 1-F(1989,2000)==F(11,2000)>0
print("PASS: mixed-cap same-sign exclusion for h>=37/100")
