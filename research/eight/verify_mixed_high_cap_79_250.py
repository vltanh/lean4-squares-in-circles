#!/usr/bin/env python3
"""Exact rational audit of HUMAN_MIXED_HIGH_CAP_79_250.md.

The preceding hand proofs establish true-square geometry and
the sharp cap envelope. This script certifies the tight exact
coupled-center-distance endpoints only.
"""
from fractions import Fraction as F
H=F(79,250);Q=F(9789,2500);r=F(283,200)
a=H+F(1,2);X=F(489,500);C=F(409,400)
assert a==F(102,125)
assert (1+H)**2+(X+F(1,2))**2-Q==F(37,50000)>0
assert r*r-X*X-C*C==F(939,4000000)>0
high=r*r+a*a-2*a*C
low=X*X+(1-a)**2
assert high==F(999361,1000000)<1
assert low==F(49517,50000)<1
assert 1-high==F(639,1000000)>0
assert 1-low==F(483,50000)>0
assert H-F(7,24)==F(73,3000)>0
print('PASS: full-frame mixed same-sign cap excluded at h>=79/250')
