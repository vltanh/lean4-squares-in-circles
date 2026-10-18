#!/usr/bin/env python3
"""Exact 63-coefficient Bernstein certificate for h>=79/250 cap envelope.

Hand proof uses top-edge polynomial positivity noncircularly to establish
y<49/50. This script checks all rational true-vertex margins and the exact
Bernstein minimum over every listed interval, never a numerical grid.
"""
from fractions import Fraction as F
from math import comb
H=F(79,250);Y=F(49,50);q=F(9789,2500)
assert (1+H)**2+(Y+F(1,2))**2-q==F(104,15625)>0
assert (H+F(141,100))**2+Y*Y-q==F(5969,250000)>0
assert F(141,100)**2<2
assert 2*H*F(2,5)+F(3,4)-Y==F(57,2500)>0
PH=[F(i) for i in (0,-4,12,0,16,4,4)]
PY=[F(i) for i in (2,-8,-2,-8,-2,0,2)]
P0=[F(i) for i in (1,-3,6,14,5,1,0)]
def poly(h,y):return [P0[i]+h*PH[i]+y*PY[i] for i in range(7)]
def bernstein(p,a,b):
    ct=[sum(p[j]*comb(j,i)*a**(j-i)*(b-a)**i for j in range(i,7)) for i in range(7)]
    return [sum(ct[i]*F(comb(k,i),comb(6,i)) for i in range(k+1)) for k in range(7)]
V=[
(H,F(0),[(F(0),F(1,2),F(1697,3750))]),
(F(7,5),F(0),[(F(0),F(1,4),F(3601,19200)),(F(1,4),F(1,2),F(779,1280))]),
(H,Y,[(F(0),F(1,4),F(283839,512000)),(F(1,4),F(3,8),F(1083811,32768000)),(F(3,8),F(7,16),F(4322111,1310720000)),(F(7,16),F(1,2),F(14654007,419430400))]),
(F(21,50),Y,[(F(0),F(1,4),F(54823,102400)),(F(1,4),F(1,2),F(29,4000))])
]
for h,y,parts in V:
    assert parts[0][0]==0 and parts[-1][1]==F(1,2)
    for i in range(1,len(parts)):
        assert parts[i][0]==parts[i-1][1]
    for a,b,m in parts:
        vals=bernstein(poly(h,y),a,b)
        assert len(vals)==7 and min(vals)==m>0,(h,y,a,b,min(vals),m)
print('PASS: exact h>=79/250 one-square envelope 63-coefficient certificate')
