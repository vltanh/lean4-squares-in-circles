#!/usr/bin/env python3
"""Exact rational endpoint audit for HUMAN_CAP_ENVELOPE_37_100.md.

Does not check continuous geometry by sampling. Polynomial positivity,
concavity and vertex reductions are proved in the hand note.
"""
from fractions import Fraction as F

H=F(37,100); Q=F(9789,2500)
assert H > F(7,24)
assert (1+H)**2 + F(9,4) - Q == F(2113,10000)
assert H**2+2+(H+1)*F(7,5)-Q == F(1393,10000)
assert H**2+3+2*H*F(7,5)-Q == F(2573,10000)
assert (2*F(7,5)-1)*H-F(13,20)==F(2,125)>0

def add(a,b):
    return [x+y for x,y in zip(a+[F(0)]*(max(len(a),len(b))-len(a)),b+[F(0)]*(max(len(a),len(b))-len(b))]
def mul(a,k): return [x*k for x in a]
def poly(h,y):
    PH=[0,-4,12,0,16,4,4]
    PY=[2,-8,-2,-8,-2,0,2]
    P0=[1,-3,6,14,5,1,0]
    return add(add(mul(PH,h),mul(PY,y)),[F(x) for x in P0])
def evalpoly(a,z): return sum(c*z**i for i,c in enumerate(a))
def deriv(a): return [a[i]*i for i in range(1,len(a))]

A=poly(H,0); B=poly(F(7,5),0)
C=poly(H,1); D=poly(F(2,5),1)
assert A == [F(1),-F(112,25),F(261,25),F(14),F(273,25),F(62,25),F(37,25)]
assert B == [F(1),-F(43,5),F(114,5),F(14),F(137,5),F(33,5),F(28,5)]
assert C == [F(3),-F(312,25),F(211,25),F(6),F(223,25),F(62,25),F(87,25)]
assert D == [F(3),-F(63,5),F(44,5),F(6),F(47,5),F(13,5),F(18,5)]
assert A[1]**2-4*A[0]*A[2]==-F(13556,625)
assert B[1]**2-4*B[0]*B[2]==-F(431,25)
for a in (C,D):
    assert all(v>0 for v in deriv(deriv(a)))  # P'' coefficients positive
AC=F(2,5); AD=F(79,200)
assert evalpoly(deriv(C),AC)==-F(2596,78125)
assert evalpoly(C,AC)-AC*evalpoly(deriv(C),AC)==F(1851,78125)
assert F(1851,78125)-F(2596,78125)*F(1,2)==F(553,78125)>0
assert evalpoly(deriv(D),AD)==F(761606023,400000000000)
assert evalpoly(D,AD)-AD*evalpoly(deriv(D),AD)==F(1041716561351,32000000000000)>0
print('PASS: exact 37/100 cap envelope endpoint and polynomial margins')
