#!/usr/bin/env python3
"""Exact rational audit for HUMAN_MIXED_HIGH_CAP_SIGN_SPLIT.md.

This checks the few stated squared and rectangle inequalities.
The continuous mixed-angle and cap-envelope arguments are
proved in the hand note, not replaced by the script.
"""
from fractions import Fraction as F

q=F(9789,2500)
r0=F(283,200)
assert q-F(7,5)**2==F(4889,2500)<F(7,5)**2
assert r0*r0-F(7,10)**2==F(60489,40000)
assert F(123,100)**2-F(60489,40000)==F(27,40000)>0
assert F(9,10)**2+F(33,100)**2==F(9189,10000)<1
assert 1-F(9189,10000)==F(811,10000)>0
assert F(19,24)*F(9,10)==F(171,240)>F(7,10)
print("PASS: mixed inner/outer high-cap opposite-sign margins")
