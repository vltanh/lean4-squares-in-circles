#!/usr/bin/env python3
"""Exact rational Bernstein audit of HUMAN_CAP_ENVELOPE_ONE_THIRD.md.

Checks the true-square vertex endpoints and every coefficient of all
eight Bernstein interval certificates. Geometric reductions, concavity,
and the Bernstein-basis positivity principle are in the hand proof.
"""
from fractions import Fraction as F
from math import comb
H=F(1,3);Y=F(49,50);Q=F(9789,2500)
assert (1+H)**2+(Y+F(1,2))**2-Q==F(1183,22500)>0
assert (H+F(7,5))**2+Y**2-Q==F(277,5625)>0
assert H**2+Y**2+1+(H+Y)*F(141,100)-Q==F(347,45000)>0
assert F(141,100)**2<2
assert 2*H*F(2,5)+F(3,4)-Y==F(11,300)>0
PH=[F(i) for i in (0,-4,12,0,16,4,4)]
PY=[F(i) for i in (2,-8,-2,-8,-2,0,2)]
P0=[F(i) for i in (1,-3,6,14,5,1,0)]
def poly(h,y):return [P0[i]+h*PH[i]+y*PY[i] for i in range(7)]
def bernstein(p,a,b):
    ct=[sum(p[j]*comb(j,i)*a**(j-i)*(b-a)**i for j in range(i,7)) for i in range(7)]
    return [sum(ct[i]*F(comb(k,i),comb(6,i)) for i in range(k+1)) for k in range(7)]
V=[
 (H,F(0),[(F(0),F(1,2),F(4,9))]),
 (F(7,5),F(0),[(F(0),F(1,4),F(3601,19200)),(F(1,4),F(1,2),F(779,1280))]),
 (H,Y,[(F(0),F(1,4),F(169331,307200)),(F(1,4),F(3,8),F(278637,6553600)),(F(3,8),F(1,2),F(173087,18432000))]),
 (F(21,50),Y,[(F(0),F(1,4),F(54823,102400)),(F(1,4),F(1,2),F(29,4000))])
]
for h,y,intervals in V:
    assert intervals[0][0]==0 and intervals[-1][1]==F(1,2)
    for i in range(1,len(intervals)):
        assert intervals[i][0]==intervals[i-1][1]
    p=poly(h,y)
    for a,b,m in intervals:
        bs=bernstein(p,a,b)
        assert len(bs)==7 and min(bs)==m>0,(h,y,a,b,min(bs),m)
assert V[3][0]+Y==F(7,5)
print("PASS: exact 1/3 cap envelope four-vertex Bernstein certificate")
