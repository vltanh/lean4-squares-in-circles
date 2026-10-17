#!/usr/bin/env python3
"""Exact finite audit of the quantitative full-slider local sharpness tube.

The candidate root box and interval arithmetic are those of the existing
adaptive-dual audit. For each actual SAT owner assignment, the smooth
angular coefficients are affine in the two sliders. Unsigned wrong-axis
gaps are convex in those sliders. Consequently the four rectangle corners
prove the stated uniform bounds throughout the whole rectangle.

This verifies the explicit strict arithmetic premises of
HUMAN_QUANTITATIVE_SLIDER_TUBE.md, not the missing global capture.
"""
from fractions import Fraction as F
from itertools import product
from contextlib import redirect_stdout
import io

with redirect_stdout(io.StringIO()):
    import verify_adaptive_seven_square_dual as d

I=d.I
ROOT=d
from types import SimpleNamespace
YRAD=F(1,500)
ZRAD=F(1,2000)
YBOX=I(ROOT.y0-YRAD,ROOT.y0+YRAD)
ZBOX=I(ROOT.z0-ZRAD,ROOT.z0+ZRAD)

def calc(q,y,z):
 one,two,half=I(1),I(2),I(F(1,2))
 c=(one-z*z)/(one+z*z);s=two*z/(one+z*z)
 x1=(q-y*y).sqrt();x2=(q-(y+two)*(y+two)).sqrt();x3=x2-3
 y3=(q-x3*x3).sqrt();y4=y3-two;x4=-(q-y4*y4).sqrt()
 h1=c*x1+s*y-two-c;h2=-s*x4+c*y4-one-s
 dx1=-y/x1;ddx1=-q/(x1*x1*x1)
 dx2=-(y+two)/x2;ddx2=-q/(x2*x2*x2)
 dy4=-x3*dx2/y3;ddy4=-q*dx2*dx2/(y3*y3*y3)-x3*ddx2/y3
 dx4=-y4*dy4/x4;ddx4=-q*dy4*dy4/(x4*x4*x4)-y4*ddy4/x4
 h1y=c*dx1+s;h2y=-s*dx4+c*dy4
 h1yy=c*ddx1;h2yy=-s*ddx4+c*ddy4
 Fy=two*(h1*h1y+h2*h2y)
 Fyy=two*(h1y*h1y+h1*h1yy+h2y*h2y+h2*h2yy)
 h1t=-s*(x1-one)+c*y;h2t=-c*(x4+one)-s*y4
 Fyt=two*(h1t*h1y+h1*(-s*dx1+c)+h2t*h2y+h2*(-c*dx4-s*dy4))
 mA0=c/(two*x1);ab0=s-c*y/x1;mB0=ab0/(two*(y+two));tb0=ab0*x2/(y+two);mD0=-tb0/(two*x3);ed0=two*mD0*y3;mH0=-one/(two*h1);he0=h2/h1;mE0=-s*he0/(two*x4)
 factor=one/(mA0+mB0+mD0+mE0+mH0)
 mA,mB,mD,mE,mH=[v*factor for v in [mA0,mB0,mD0,mE0,mH0]]
 ab,tb,dt,ed,W,wHG,he=[v*factor for v in [ab0,tb0,tb0,ed0,one,one,he0]]
 B=[mA*(x1+y)-W*(c-s)/two,mB*(y+two-x2),I(0),-mD*(x3+y3),mE*(x4-y4)-he*(c-s)/two,mH*(h1-h2),I(0)]
 vals=locals();return vals


values=calc(ROOT.q,YBOX,ZBOX)
d=SimpleNamespace(**values)
d.I=I
calc(ROOT.q,I(ROOT.y0-YRAD),ZBOX)['Fy'].lt(-F(3,500))
calc(ROOT.q,I(ROOT.y0+YRAD),ZBOX)['Fy'].gt(F(3,500))
d.Fyy.gt(7)
abs(d.Fyt).lt(5)
(2*(ZBOX-ZBOX*ZBOX*ZBOX/3)).gt(F(1,10))
(2*ZBOX).lt(F(1,5))
(d.s/d.c).lt(F(1,5))

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

# The root-level endpoint inclusion is proved by the separate uniform-slider audit.
# Here every pseudo reference in the full rational slider rectangle is covered.
xT=d.x2-I(F(3,2))
lowest=None
largest_wrong=None
wrong_count=0
coefficient_count=0
for height,eta in product(T_RANGE,ETA_RANGE):
    z=I(height);eta=I(eta)
    pT=(xT,z)
    pG=(pH[0]+d.c-eta*d.s,pH[1]+d.s+eta*d.c)
    poses=dict(A=pA,B=pB,T=pT,D=pD,E=pE,H=pH,G=pG)
    for a0,b0 in [('A','B'),('T','B'),('D','T'),('E','D'),('G','A'),('H','G'),('H','E')]:
        v0=sub(poses[b0],poses[a0])
        (abs(v0[0])*abs(v0[0])+abs(v0[1])*abs(v0[1])).lt(4)
    for (a,b),axes in wrong.items():
        delta=sub(poses[b],poses[a])
        for axis in axes:
            gap=abs(inner(normals[axis],delta))-halfwidth(a,axis)-halfwidth(b,axis)
            gap.lt(-F(1,400))
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
            reserve.gt(F(9,500))
            lowest=reserve if lowest is None or reserve.lo<lowest.lo else lowest
            coefficient_count+=1

assert wrong_count==44 and coefficient_count==640
# Uniform constants in the explicit nonlinear estimate.
mu=[d.mA,d.mB,d.mD,d.mE,d.mH]
weights=[d.ab,d.tb,d.dt,d.ed,d.W,d.wHG,d.he]
for x in mu:
    x.gt(F(1,50));x.lt(1)
for x in weights:
    x.gt(0);x.lt(1)
sum(weights,I(0)).lt(6)
ROOT.q.lt(4)
(d.h1*d.h1+d.h2*d.h2).lt(4)
incidence=[d.ab+d.W,d.ab+d.tb,d.dt+d.ed,d.ed+d.he,d.W+d.he]
bcoef=[2*m+v for m,v in zip(mu,incidence)]
young=sum((b*b/(2*m) for b,m in zip(bcoef,mu)),I(0))
young.lt(100)

def norm_squared(v):return abs(v[0])*abs(v[0])+abs(v[1])*abs(v[1])
ydot=-d.Fyt/d.Fyy
Hdot=(d.h1t+d.h1y*ydot-(d.h2+half),d.h2t+d.h2y*ydot+(d.h1+half))
ETA=I(F(-9,20),F(7,20))
derivatives=[(d.dx1*ydot,ydot),(d.dx2*ydot,ydot),
             (d.dx2*ydot,d.dy4*ydot),(d.dx4*ydot,d.dy4*ydot),Hdot,
             (d.dx2*ydot,I(0)),(Hdot[0]-ETA,Hdot[1]+1)]
for v in derivatives:norm_squared(v).lt(64)
PERR=F(1,1000)
SMAX=F(1,10000)
assert 2*PERR+3*SMAX<F(1,400)
assert F(9,500)-112*SMAX-4*PERR==F(7,2500)>0
print('PASS: full common-tilt chart has opposite Fy endpoint signs, Fyy>7, |Fyt|<5')
print('PASS: 44 wrong-axis corner bounds<-1/400 and 640 owner coefficient bounds>9/500')
print('PASS: all circle weights>1/50, contact weights in(0,1), total contact weight<6')
print('PASS: Young coefficient sum<100, every reference neighbor distance<2')
print('PASS: all seven pseudo-center derivatives have norm<8')
print('PASS: center error<=1/1000 and total mismatch S<=1/10000 leave 7S/2500')
print('minimum angular reserve enclosure',lowest.show())
print('largest wrong-axis gap enclosure',largest_wrong.show())
print('Young coefficient enclosure',young.show())
