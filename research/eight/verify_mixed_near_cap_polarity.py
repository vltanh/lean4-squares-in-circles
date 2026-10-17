#!/usr/bin/env python3
"""Exact fraction audit for HUMAN_MIXED_NEAR_CAP_POLARITY.md.

Only verifies displayed rational endpoint inequalities, not the
continuous trigonometric/convexity reasoning or full n=8 proof.
"""
from fractions import Fraction as F
x=F(17,20)
sin_upper=x-x**3/6+x**5/120
assert F(19,24)-sin_upper==F(5161381,128000000)>0
x=F(29,50)
sin_upper=x-x**3/6+x**5/120
assert F(475,849)-sin_upper==F(121549694833,10612500000000)>0
x=F(3,4)
cos_lower=1-x*x/2+x**4/24-x**6/720
assert cos_lower==F(239759,327680)
assert cos_lower-F(73,100)==F(2763,1638400)>0
corners=[
 r*r+s*s-F(73,50)*r*s
 for r in [F(19,24),F(1)]
 for s in [F(1),F(283,200)]
]
assert corners==[
 F(6781,14400),F(715289,720000),
 F(27,50),F(37453,40000)]
assert max(corners)==1-F(4711,720000)<1
assert F(3,4)-(F(11,7)-F(17,20))==F(1,35)>0
x=F(133,100)
cos_upper=1-x*x/2+x**4/24
assert cos_upper==F(590220721,2400000000)
assert F(1,4)-cos_upper==F(9779279,2400000000)>0
x=F(3,4)
tan_lower=x+x**3/3+2*x**5/15
assert tan_lower==F(2361,2560)
assert tan_lower-F(9,10)==F(57,2560)>0
assert F(19,24)*F(9,10)==F(171,240)>F(7,10)
print("PASS: near-cap mixed inner/outer exact arithmetic")
