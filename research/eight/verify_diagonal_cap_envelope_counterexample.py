#!/usr/bin/env python3
"""Exact radical-bound verification of a rotated single unit square.

The actual frame uses c=s=sqrt(2)/2; the rational bound
sqrt(2)<99/70 bounds ALL four actual vertex norms.
This is a valid local counterexample to the proposed cap envelope
at h=293/1000, not an eight-square packing.
"""
from fractions import Fraction as F
h=F(293,1000)
q=F(9789,2500)
S2upper=F(99,70)
assert S2upper*S2upper>2
assert h-F(7,24)==F(1,750)>0
# With center (h+sqrt2/2,1) and diagonal frame,
# true vertices are (h,1), (h+sqrt2,1), and
# (h+sqrt2/2, 1 +/- sqrt2/2).
right_upper=h*h+3+2*h*S2upper
top_upper=h*h+2+(h+1)*S2upper
assert q-right_upper==F(6857,7000000)>0
assert q-top_upper==F(7557,7000000)>0
left=h*h+1
assert left<q
axis_envelope=(h+1)**2+F(9,4)
assert axis_envelope==F(3921849,1000000)
assert axis_envelope-q==F(6249,1000000)>0
print('PASS: diagonal square below q+ contradicts cap envelope at h=293/1000')
