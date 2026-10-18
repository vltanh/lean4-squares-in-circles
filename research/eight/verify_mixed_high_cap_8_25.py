#!/usr/bin/env python3
"""Exact rational audit of HUMAN_MIXED_HIGH_CAP_8_25.md.

The all-frame cap envelope and mixed angular center-sign lemmas
are proved in Markdown hand notes. This verifies all new strict
rational margins in the coupled radial two-case argument.
"""
from fractions import Fraction as F
h=F(8,25);q=F(9789,2500);r=F(283,200)
a=h+F(1,2);X=F(39,40);C=F(41,40)
assert a==F(41,50)
assert (1+h)**2+(X+F(1,2))**2-q==F(97,40000)>0
assert r*r-X*X-C*C==F(39,40000)>0
high=r*r+a*a-2*a*C
low=X*X+(1-a)**2
assert high==F(7949,8000)<1
assert low==F(39321,40000)<1
assert 1-high==F(51,8000)>0
assert 1-low==F(679,40000)>0
print('PASS: full-frame mixed cap same-sign exclusion at h>=8/25')
