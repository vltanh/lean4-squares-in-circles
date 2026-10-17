#!/usr/bin/env python3
"""Exact finite audit of the local sharpness dual over both full slider ranges.

The candidate root box and interval arithmetic are those of the existing
adaptive-dual audit. For each actual SAT owner assignment, the smooth
angular coefficients are affine in the two sliders. Unsigned wrong-axis
gaps are convex in those sliders. Consequently the four rectangle corners
prove the stated uniform bounds throughout the whole rectangle.

This verifies the explicit strict arithmetic premises of
HUMAN_UNIFORM_SLIDER_LOCAL_SHARPNESS.md, not the missing global capture.
"""
from fractions import Fraction as F
from itertools import product
from contextlib import redirect_stdout
import io

with redirect_stdout(io.StringIO()):
    import verify_adaptive_seven_square_dual as d

I=d.I
half=I(F(1,2))
zero=I(0)
one=I(1)
two=I(2)
T_RANGE=(F(7,12),F(11,8))
ETA_RANGE=(F(-9,20),F(7,20))

pA=(d.x1-half,d.y+half)
pB=(d.x2-half,d.y+I(F(3,2)))
pD=(d.x3+half,d.y3-half)
pE=(d.x4+half,d.y4+half)
pH=((d.h1+half)*d.c-(d.h2+half)*d.s,
    (d.h1+half)*d.s+(d.h2+half)*d.c)
inner=lambda a,b:a[0]*b[0]+a[1]*b[1]
sub=lambda a,b:(a[0]-b[0],a[1]-b[1])
normals={'a':(one,zero),'b':(zero,one),'e':(d.c,d.s),'f':(-d.s,d.c)}
standard={'A','B','T','D','E'}
def halfwidth(label,axis):
    return half if (label in standard)==(axis in ('a','b')) else half*(d.c+d.s)

wrong={('A','B'):('a',),('T','B'):('b',),('D','T'):('b',),
       ('E','D'):('a',),('G','A'):('f','a','b'),('H','G'):('f',),
       ('H','E'):('e','a','b')}
assert sum(map(len,wrong.values()))==11
names=('A','B','T','D','E','H','G')
where={name:k for k,name in enumerate(names)}
edges=[('A','B',d.ab),('T','B',d.tb),('D','T',d.dt),
       ('E','D',d.ed),('H','G',d.wHG)]

# Exact admissible endpoint bounds for the candidate-compatible component.
xT=d.x2-I(F(3,2))
aG=d.h1+I(F(3,2))
bG=d.h2+half
xT.gt(0);xT.lt(F(1,2));aG.gt(0);aG.lt(F(1,2));bG.lt(0)
topT=(d.q-(xT+half)*(xT+half)).sqrt()-half
etaOuter=-(d.q-(aG+half)*(aG+half)).sqrt()+half-bG
etaCore=-I(F(7,12))-bG
topT.lt(T_RANGE[1]);topT.gt(T_RANGE[0])
etaOuter.gt(ETA_RANGE[0]);etaCore.lt(ETA_RANGE[1])
(etaCore-etaOuter).gt(0)

lowest=None
largest_wrong=None
wrong_count=0
coefficient_count=0
for height,eta in product(T_RANGE,ETA_RANGE):
    z=I(height);eta=I(eta)
    pT=(xT,z)
    pG=(pH[0]+d.c-eta*d.s,pH[1]+d.s+eta*d.c)
    poses=dict(A=pA,B=pB,T=pT,D=pD,E=pE,H=pH,G=pG)
    for (a,b),axes in wrong.items():
        delta=sub(poses[b],poses[a])
        for axis in axes:
            gap=abs(inner(normals[axis],delta))-halfwidth(a,axis)-halfwidth(b,axis)
            gap.lt(-F(1,125))
            largest_wrong=gap if largest_wrong is None or gap.hi>largest_wrong.hi else largest_wrong
            wrong_count+=1

    transverse=[d.x1-d.x2,pB[1]-z,z-pD[1],d.x4-d.x3,eta]
    Y_GA=inner(normals['f'],sub(pA,pG))
    Y_HE=-inner(normals['e'],sub(pE,pH))
    smooth=[d.B[0],d.B[1],zero,d.B[3],d.B[4],
            d.mH*(d.h1-d.h2)+d.he*((d.c-d.s)/two-Y_HE),
            d.W*((d.c-d.s)/two-Y_GA)]

    for assignment in product((0,1),repeat=5):
        v=[I(x) for x in smooth]
        for k,choice in enumerate(assignment):
            a,b,weight=edges[k]
            owner=(a,b)[choice]
            v[where[owner]]=v[where[owner]]-weight*transverse[k]
        cED=v[where['E']]
        cDT=v[where['D']]+cED
        cTB=v[where['T']]+cDT
        cAB=-v[where['B']]-cTB
        cHG=v[where['H']]
        for coeff,(_,_,weight) in zip((cAB,cTB,cDT,cED,cHG),edges):
            reserve=weight/two-abs(coeff)
            reserve.gt(F(1,40))
            lowest=reserve if lowest is None or reserve.lo<lowest.lo else lowest
            coefficient_count+=1

assert wrong_count==44 and coefficient_count==640
print('PASS: both full candidate-compatible slider intervals lie in the rational rectangle')
print('PASS: 44 wrong-axis corner bounds < -1/125 imply all 11 uniform axis bounds')
print('PASS: all 32 owner assignments, 4 slider corners, 5 angular reserves >1/40')
print('minimum reserve enclosure',lowest.show())
print('largest wrong-axis gap enclosure',largest_wrong.show())
print('T upper endpoint enclosure',topT.show())
print('G outer eta endpoint enclosure',etaOuter.show())
print('G core eta endpoint enclosure',etaCore.show())
