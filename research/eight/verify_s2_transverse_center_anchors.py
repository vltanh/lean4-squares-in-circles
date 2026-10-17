#!/usr/bin/env python3
"""Exact rational endpoint checks for S2/k4 transverse center anchors.

The squared inequalities here only audit margins in a written proof.
"""
from fractions import Fraction as F
assert 551*2500-1173**2 == 1571 > 0
assert F(44,3)**2-215 == F(1,9)>0
assert F(1319,3600)-F(9,25)==F(23,3600)>0
assert F(1733,1000)**2>3>F(17,10)**2
assert F(267,1000)==2-F(1733,1000)
tan_lower=(F(267,1000)-F(1,250))/(1+F(3,10)*F(1,250))
assert tan_lower==F(1315,5006)
assert F(9,8)*tan_lower-F(29,100)==F(5527,1001200)>0
print('PASS: strict U and D transverse rational margins')
