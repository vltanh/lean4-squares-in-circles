#!/usr/bin/env python3
"""Exact rational audit for HUMAN_FIVE_SQUARE_RU_ONE_SIXTEENTH.md.

Checks the new 1/16 angular threshold, all new radial rectangle
corners and strict Taylor signs. The analytic five-square argument
is in the Markdown note; no interval classifier or Lean proof.
"""
from fractions import Fraction as F

# At hU>=1/16, alpha=asin(hU+1/2)>297/500.
A=F(297,500)
assert F(9,16)-(A-A**3/6+A**5/120)==F(3518153059581,1250000000000000)>0

# R- inner radius >7/10 from R cap x>117/200 and alpha>=asin(9/16).
assert F(117,140)**2-F(175,256)==F(4649,313600)>0

def cosine_lower(x):
    return 1-x*x/2+x**4/24-x**6/720

def cosine_upper(x):
    return 1-x*x/2+x**4/24

def corners(rmin,c):
    return [r*r+s*s-2*c*r*s
            for r in (rmin,F(1)) for s in (F(1),F(283,200))]

# New mixed inner U+ (radius >9/16) / outer center angular gap >.59.
M=F(59,100)
assert cosine_lower(M)-F(83,100)==F(677027766359,720000000000000)>0
assert corners(F(9,16),F(83,100)) == [
    F(2449,6400),F(7979,8000),F(17,50),F(26133,40000)]
assert max(corners(F(9,16),F(83,100)))==F(7979,8000)<1

# Ray bounds using pi<22/7, pi>157/50.
neg_upper=F(22,21)-A-F(311,500)
assert neg_upper==-F(442,2625)
pos_upper=F(44,21)-A-M
assert pos_upper==F(2392,2625)<F(157,150)
assert F(22,7)/8 * F(3) - A < F(2,9)*F(157,50)

# Negative-ray amplification: first inner radius exceeds 9/10.
theta1=F(442,2625)+F(2,9)*F(157,50)
assert theta1==F(6821,7875)>F(433,500)
assert theta1-F(433,500)==F(1,6300)
assert F(13,20)-cosine_upper(F(433,500)) == F(2314874879,1500000000000)>0

# New >.779 gap between inner radius >9/10 and an outer radius.
T=F(779,1000)
assert cosine_lower(T)-F(1779,2500) == F(9447139570318679,720000000000000000000)>0
v=corners(F(9,10),F(1779,2500))
assert max(v)==F(4998899,5000000)<1

theta2=F(442,2625)+T
assert theta2==F(3979,4200)
assert F(117,200)-cosine_upper(theta2) == F(1495706861519,7468070400000000)>0

# Final positive ray and center pair inequality.
assert F(311,500)>F(11,21)
assert F(2392,2625)<F(157,150)
assert F(1) - (F(113079,200000)**2+F(81,100)**2) == F(969139759,40000000000)>0
print("PASS: sharpened five-square RU obstruction to hU>=1/16")
