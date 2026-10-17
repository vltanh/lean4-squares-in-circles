#!/usr/bin/env python3
"""Exact rational endpoint audit for S1/k3 far singleton transverse sign.

Checks new rational angle/normal comparisons and the inherited final
center-distance margin. The full all-frame proof is the Markdown
hand argument, not a generated case classification or Lean proof.
"""
from fractions import Fraction as F

# A U- inner center at theta>=7pi/9 would have r>7/10.
assert F(2,9)*F(22,7)<F(5,7)

# R- inner has radius>7/10 when its angle magnitude exceeds 2pi/9.
z=F(157,225)   # pi>157/50 => 2pi/9 >157/225
cos_upper=1-z*z/2+z**4/24
assert F(4,5)-cos_upper==F(2064819299,61509375000)>0
assert (F(117,200)/F(4,5))>F(7,10)

# R- would exceed its x projection in the negative R-outer ray.
assert F(157,450)+F(311,500)-F(24,25)==F(49,4500)>0
z=F(24,25)
assert F(117,200)-(1-z*z/2+z**4/24)==F(32533,3125000)>0

# Positive-R outer upper ray remains <pi/3.
assert F(12,25)-F(22,63)==F(206,1575)>0
assert F(311,500)>F(11,21)

# In the remaining positive-R sector, the sole R outer and R+
# inner center cannot be separated by one unit.
assert F(1)-(F(113079,200000)**2+F(81,100)**2)==F(969139759,40000000000)>0
assert F(13,100)+F(177,250)<F(227,250)

print("PASS: S1/k3 strict far-L opposite transverse center-sign margins")
