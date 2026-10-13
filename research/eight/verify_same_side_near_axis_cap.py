#!/usr/bin/env python3
"""Exact rational audit for HUMAN_SAME_SIDE_NEAR_AXIS_CAP.md.

Does not verify square containment analytically or the global n=8 theorem.
The hand proof supplies the geometric reduction.
"""
from fractions import Fraction as F
t=F(3000,3001)
h=F(7,24)
q=F(9789,2500)
lb=(h+t)**2+F(9,4)*t*t
assert lb-q==F(1435675009,3242160360000)>0
assert F(2257,576)-q==F(1009,360000)>0
assert (h+2*t)**2+t*t/4-(lb)==2*h*t+t*t>0
print("PASS: exact same-side near-axis two-cap radius margin")
