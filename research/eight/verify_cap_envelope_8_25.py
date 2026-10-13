#!/usr/bin/env python3
"""Exact rational audit for HUMAN_CAP_ENVELOPE_8_25.md.

The hand proof uses top-edge Bernstein positivity to prove y<39/40
before concluding full quadrilateral positivity. Here ALL eight
intervals' 56 Bernstein coefficients and true-vertex endpoint
comparisons are checked as exact fractions, not numerical samples.
"""
from fractions import Fraction as F
from math import comb
H=F(8,25);Y=F(39,40);q=F(9789,2500)
assert (1+H)**2+(Y+F(1,2))**2-q==F(97,40000)>0
assert (H+F(141,100))**2+Y**2-q==F(1117,40000)>0
assert F(141,100)**2<2
assert 2*H*F(2,5)+F(3,4)-Y==F(31,1000)>0
PH=[F(v) for v in (0,-4,12,0,16,4,4)]
PY=[F(v) for v in (2,-8,-2,-8,-2,0,2)]
P0=[F(v) for v in (1,-3,6,14,5,1,0)]
def poly(h,y):return [P0[i]+h*PH[i]+y*PY[i] for i in range(7)]
def bernstein(p,a,b):
    ct=[sum(p[j]*comb(j,i)*a**(j-i)*(b-a)**i for j in range(i,7)) for i in range(7)]
    return [sum(ct[i]*F(comb(k,i),comb(6,i)) for i in range(k+1)) for k in range(7)]
V=[
 (H,F(0),[(F(0),F(1,2),F(169,375))]),
 (F(7,5),F(0),[(F(0),F(1,4),F(3601,19200)),(F(1,4),F(1,2),F(779,1280))]),
 (H,Y,[(F(0),F(1,4),F(227299,409600)),(F(1,4),F(3,8),F(1151851,26214400)),(F(3,8),F(1,2),F(202921,24576000))]),
 (F(17,40),Y,[(F(0),F(1,4),F(43889,81920)),(F(1,4),F(1,2),F(923,51200))])
]
for h,y,intervals in V:
    assert intervals[0][0]==0 and intervals[-1][1]==F(1,2)
    for i in range(1,len(intervals)):
        assert intervals[i][0]==intervals[i-1][1]
    p=poly(h,y)
    for a,b,m in intervals:
        values=bernstein(p,a,b)
        assert len(values)==7 and min(values)==m>0,(h,y,a,b,min(values),m)
assert V[3][0]+Y==F(7,5)
print('PASS: exact 8/25 one-square cap envelope and noncircular height certificate')
