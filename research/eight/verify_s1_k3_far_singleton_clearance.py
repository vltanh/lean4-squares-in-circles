#!/usr/bin/env python3
"""Exact rational margins for S1/k3 far L clearance y_L<-1/75.

The hand proof establishes angular ordering for every square frame.
This audits the arithmetic only; no interval cover or Lean certificate.
"""
from fractions import Fraction as F

assert F(1,75)/F(137,100)==F(4,411)
assert F(1,100)-F(4,411)==F(11,41100)>0
assert F(2,9)*F(22,7)<F(5,7)
assert F(2,9)*F(157,50)-F(1,100)-F(2,3)==F(19,900)>0

def cos_upper(x):
    return 1-x*x/2+x**4/24

assert cos_upper(F(2,3))==F(191,243)
assert F(117,140)-F(191,243)==F(1691,34020)>0

# The inherited two strict mixed angular gaps have room even with +.01.
assert F(2,9) -(F(11,72)+F(1,100)/F(157,50))>0
assert F(157,450)+F(311,500)-F(1,100)-F(24,25)==F(1,1125)>0
assert F(12,25)-F(22,63)-F(1,100)>0
assert F(117,200)-cos_upper(F(24,25))==F(32533,3125000)>0

# The last two actual center projections conflict with unit separation.
assert F(13,100)+F(177,250)<F(227,250)
assert 1-(F(113079,200000)**2+F(81,100)**2)==F(969139759,40000000000)>0
print("PASS: all new S1/k3 strict far singleton transverse margins")
