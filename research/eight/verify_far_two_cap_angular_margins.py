#!/usr/bin/env python3
"""Exact arithmetic audit of HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md.

This checks the hand proof's rational comparisons only; it is NOT an
interval classifier, proof oracle, Lean formalization, or full n=8 proof.
The angular and geometric deductions must be verified from the written note.
"""
from fractions import Fraction as F

# The universal center radius r0<283/200.
r0=F(283,200)
qplus=F(9789,2500)
assert r0*r0+r0+F(1,2)-qplus == F(65,40000)>0

# Four-inner polar ray witness R_-: cos alpha <5/8
# cos alpha =sqrt(215)/24, hence sqrt(215)<15.
assert 215<15*15
assert F(1,2)/F(5,8)==F(4,5)

# Far-side outer polar elevation beta: sin|theta_D|>4/5
# since sqrt(3)<217/125, 2-sqrt(3)/2>283/250.
assert 3*125**2<217**2
assert 2-F(217,250)==F(283,250)
assert F(283,250)/r0==F(4,5)

# A mixed center radius >4/5 and an outer radius <283/200
# cannot be unit-separated at an angle <=pi/6+1/100.
assert 3*250**2>433**2
trig_lower=F(433,500)*(1-F(1,20000))-F(1,200)
assert trig_lower-F(43,50)==F(9567,10000000)>0
mixed_upper=(F(123,200))**2+F(283,100)*F(7,50)
assert mixed_upper==F(30977,40000)<1

# alpha+beta>7*pi/12 by exact arctangent comparisons.
# tan(alpha)=19/sqrt(215) >9/7.
assert 133**2>81*215
# tan(pi/12)=2-sqrt(3)<3/11 iff sqrt(3)>19/11.
assert 3*11**2>19**2
# tan(atan(9/7)+atan(4/3)-pi/2)==3/11
aa=F(9,7); bb=F(4,3)
assert aa*bb>1
assert (aa*bb-1)/(aa+bb)==F(3,11)
# interval width bound is pi/4 -1/100, stronger than
# the outer-pair theorem's pi/4 -1/500
assert F(1,100)>F(1,500)

print("PASS: exact outer/inner angular-crowding margins (no numerical search)")
