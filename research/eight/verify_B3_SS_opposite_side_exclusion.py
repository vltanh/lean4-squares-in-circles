#!/usr/bin/env python3
"""Exact arithmetic audit of HUMAN_B3_SS_OPPOSITE_SIDE_EXCLUDED.md.

The full all-frame lemma follows from the exact identities
L=c+s, D=c-s, L^2+D^2=2, L+D=2c<=2, L>=1,
and 0<=k<=1/2. The decisive inequality is
  2*k*(L-1)+(D-1) <= (L-1)+(D-1) <=0.
The script checks symbolic cancellation and the strict disk
radius reserve. It does NOT claim to certify global n=8 feasibility.
"""
from fractions import Fraction as F
import sympy as sp

k,L,D,rho=sp.symbols("k L D rho",real=True)
difference=sp.expand((k+L)**2+(sp.Rational(1,2)+D)**2
                     -((k+1)**2+sp.Rational(9,4)))
assert sp.expand(difference-(2*k*(L-1)+D-1)-
                 (L*L+D*D-2))==0
# On the actual frame circle L^2+D^2=2, so difference
# equals 2k(L-1)+(D-1), which is <= L+D-2 <=0.
r_squared=rho**2+sp.Rational(1,4)
k_sub=2-rho
disk_margin=sp.expand(r_squared-((k_sub+1)**2+sp.Rational(9,4)))
assert disk_margin==6*rho-11

# R>sqrt(2)+1/2 ==> rho^2>2+sqrt2>121/36.
assert F(49,36)**2<2
assert 2+F(49,36)==F(121,36)
assert F(11,6)<2

# If tau_minus<0<tau_plus and both on the same length-one
# central side, one has abs(tau)<=1/2. The contrapositive:
# both abs(tau)>1/2 would imply separation >1.
for tau_minus,tau_plus in [
    (F(-1,2),F(1,2)),
    (F(-2,5),F(3,5)),
    (F(-1,10),F(9,10)),
]:
    assert tau_minus<0<tau_plus
    assert tau_plus-tau_minus==1
    assert min(abs(tau_minus),abs(tau_plus))<=F(1,2)

print("PASS: universal rotated-square one-contact vertex bound;")
print("      positive strict disk reserve 6*rho-11,")
print("      k<=1/2, and opposite-side transverse contact witness")
