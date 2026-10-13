#!/usr/bin/env python3
"""Exact rational angular certificate for k7/B2/m3 semicircle impossibility.

The hand proof uses:
  * the true unit-square vertex distance sqrt(2)/2,
  * the lower eight-square radius R>sqrt(2)+1/2,
  * five complementary center-ray gaps > pi/4-1/500,
  * support of normalized physical circle multipliers
    only on the three consecutive outer stressed square labels,
  * global positive circle-force balance sum mu*x = 0.

This script verifies the strict rational shadow/semicircle margins,
NOT the graph reduction or the continuous geometric force proof.
"""
from fractions import Fraction as F
a_upper=F(99,140)            # sqrt(2)/2 < 99/140
R_lower=F(191,100)          # R>sqrt(2)+1/2>191/100
shadow_ratio=a_upper/R_lower
assert F(141,100)**2<2
assert F(99,70)**2>2
assert shadow_ratio==F(495,1337)

x=F(31,80)
sine_lower=x-x*x*x/6
assert sine_lower==F(1160609,3072000)
assert sine_lower-shadow_ratio==F(31094233,4107264000)>0
# Hence angular deviation of any square's circle vertex from
# its true center ray is < 31/80 (with R>191/100).

# 5 complementary gaps each > pi/4-1/500:
# 2 pi - 5(pi/4-1/500) = 3pi/4 + 1/100.
assert 5*F(1,500)==F(1,100)

# Both angular vertex shadows add 2*(31/80)=31/40.
# Together with 1/100 their additive width is exactly 157/200.
assert F(1,100)+2*x==F(157,200)
# pi>157/50 gives pi/4>157/200:
assert F(157,50)/4==F(157,200)
# Strictness comes from true pi>157/50 and all previous strict inequalities.
print("PASS: true circle-vertex rays of three consecutive stressed")
print("      outer squares lie within one STRICT open semicircle")
print("      under k7 outer-ray separation and R>sqrt(2)+1/2")
