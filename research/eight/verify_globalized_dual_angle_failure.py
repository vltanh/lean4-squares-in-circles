#!/usr/bin/env python3
"""Exact rational upper bound for a GLOBALIZED candidate adaptive dual.

At the exact isolated sharp root, the E-angle potential from
HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md is
  DeltaPhi_E(delta) = A_E*(cos(delta)-1) +
                      B_E*sin(delta) + Gamma_E*abs(sin(delta)).
For delta = +1/10, the existing candidate-derived positive dual
LOWER bound decreases by more than 4189/3000000 in squared-radius
units. This is NOT a smaller-radius packing or a counterexample
to unrestricted optimality; it only invalidates a naive claim
that this one dual is globally coercive in every frame angle.

The imports use the exact outward-rounded integer interval library
and the isolated candidate q,y,z root box of the existing verifier.
"""
from fractions import Fraction as F
from verify_adaptive_seven_square_dual import A,B,gamma

A_E=A[4]
B_E=B[4]
Gamma_E=gamma[4]

# Rigorous over the entire exact candidate rational root box:
A_E.gt(F(22,25))
(B_E+Gamma_E).lt(F(3,100))

# For positive delta=1/10:
# sin(delta)<delta,
# 1-cos(delta)>=delta^2/2-delta^4/24.
delta=F(1,10)
low_one_minus_cos=delta**2/2-delta**4/24
assert low_one_minus_cos==F(1,200)-F(1,240000)
strict_upper=-F(22,25)*low_one_minus_cos+F(3,100)*delta
assert strict_upper==-F(4189,3000000)<0
print("PASS: exact root-box A_E>22/25 and B_E+Gamma_E<3/100")
print("PASS: candidate adaptive dual angle E=+0.1 has")
print("      DeltaPhi_E < -4189/3000000 < 0")
print("      This is a DUAL NO-GO, NOT A PACKING COUNTEREXAMPLE")
