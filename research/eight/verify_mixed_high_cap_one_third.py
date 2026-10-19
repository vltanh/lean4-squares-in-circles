#!/usr/bin/env python3
"""Exact rational audit of HUMAN_MIXED_HIGH_CAP_ONE_THIRD.md.

The all-frame center-angle, cap-envelope and geometric implications
are written in the accompanying hand proofs. This checks the strict
coupled-distance endpoint inequalities with exact fractions.
"""
from fractions import Fraction as F
q=F(9789,2500);h=F(1,3);a=h+F(1,2);r0=F(283,200)
X=F(97,100);C=F(103,100)
assert h>F(7,24)
assert (1+h)**2+(X+F(1,2))**2-q==F(2077,90000)>0
assert r0**2-X**2-C**2==F(17,40000)>0
assert a==F(5,6)
high=r0*r0+a*a-2*a*C
low=X*X+(1-a)**2
assert high==F(352801,360000)<1
assert low==F(87181,90000)<1
assert 1-high==F(7199,360000)>0
assert 1-low==F(2819,90000)>0
print('PASS: mixed whole-cap inner/outer opposite signs for h>=1/3')
