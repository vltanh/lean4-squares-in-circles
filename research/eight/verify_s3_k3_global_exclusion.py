#!/usr/bin/env python3
"""Exact rational audit of HUMAN_S3_K3_FULL_EXCLUSION.md.

These are only the displayed strict arithmetic checks. The human
document proves the all-orientation geometric implications; this
script is not a sampled classifier or Lean proof.
"""
from fractions import Fraction as Q

assert 33111*100-1819**2==2339>0
assert 1623**2-26311*100==3029>0
assert Q(1819-1623,2000)==Q(49,500)
z=Q(311,500)
cosupper=1-z*z/2+z**4/24
assert Q(813,1000)-cosupper==Q(308048159,1500000000000)>0
assert Q(177,250)**2>Q(1,2)
X=Q(283,200)*Q(813,1000)
assert X==Q(230079,200000)
A=X-Q(117,200)
assert A==Q(113079,200000)>Q(1,2)
Y=Q(1,5)+Q(177,250)-Q(49,500)
assert Y==Q(81,100)
assert 1-A*A-Y*Y==Q(969139759,40000000000)>0
print("PASS: exact S3/k3 complete-exclusion rational margins")
