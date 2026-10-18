#!/usr/bin/env python3
"""Exact rational interval audit for HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md.

Input: the rigorously isolated sharp candidate root box in
FIVE_CORNER_REDUCTION.md, q,y,z (z=tan(t/2)), decimal centers
as *exact rationals*, each coordinate within 10^-16.

Checks over the ENTIRE rational box:
  - the seven directed positive support multipliers;
  - five positive normalized disk-vertex weights;
  - every strict angle cusp margin Gamma_i-|B_i| > 1/40;
  - every absolute cosine coefficient |A_i| < 2;
  - normalization and the numerical enclosures of the
    two exact algebraic force-stationarity identities.

The continuum proof of force balance uses F_y=0, not a small
numerical residual. The implicit-function theorem and the
adaptive completed-square inequality are proven analytically
in the companion Markdown, not inferred from this audit.
"""
from fractions import Fraction as F
from math import isqrt

SCALE=10**48
def ceildiv(a,b):return -((-a)//b)
class I:
    def __init__(self,a,b=None):
        if isinstance(a,I):
            self.lo,self.hi=a.lo,a.hi
            return
        a=F(a)
        self.lo=(a.numerator*SCALE)//a.denominator
        if b is None:
            self.hi=ceildiv(a.numerator*SCALE,a.denominator)
        else:
            b=F(b)
            self.hi=ceildiv(b.numerator*SCALE,b.denominator)
    @staticmethod
    def exact(a,b):
        obj=object.__new__(I)
        obj.lo,obj.hi=a,b
        return obj
    def __neg__(self):return I.exact(-self.hi,-self.lo)
    def __add__(self,x):
        x=I(x)
        return I.exact(self.lo+x.lo,self.hi+x.hi)
    __radd__=__add__
    def __sub__(self,x):return self+-I(x)
    def __rsub__(self,x):return I(x)+-self
    def __mul__(self,x):
        x=I(x)
        products=[p*q for p in (self.lo,self.hi)
                  for q in (x.lo,x.hi)]
        return I.exact(min(products)//SCALE,
                       ceildiv(max(products),SCALE))
    __rmul__=__mul__
    def __truediv__(self,x):
        x=I(x)
        if x.lo<=0<=x.hi:
            raise ZeroDivisionError("interval crosses zero")
        if x.hi<0:return -self/(-x)
        return self*I.exact((SCALE*SCALE)//x.hi,
                            ceildiv(SCALE*SCALE,x.lo))
    def __rtruediv__(self,x):return I(x)/self
    def sqrt(self):
        assert self.lo>=0
        l=isqrt(self.lo*SCALE)
        h=isqrt(self.hi*SCALE)
        return I.exact(l,h+(h*h<self.hi*SCALE))
    def __abs__(self):
        if self.lo>=0:return self
        if self.hi<=0:return -self
        return I.exact(0,max(-self.lo,self.hi))
    def gt(self,x):
        x=F(x)
        assert self.lo*SCALE*0+self.lo*x.denominator>x.numerator*SCALE,(self,x)
    def lt(self,x):
        x=F(x)
        assert self.hi*x.denominator<x.numerator*SCALE,(self,x)
    def includes_zero(self,tolerance):
        tol=F(tolerance)
        assert self.lo<=0<=self.hi
        assert abs(self.lo)*tol.denominator<tol.numerator*SCALE
        assert abs(self.hi)*tol.denominator<tol.numerator*SCALE
    def show(self):
        return ("%.12f"% (self.lo/SCALE),
                "%.12f"% (self.hi/SCALE))

radius=F(1,10**16)
q0=F("3.91553413751747532652")
y0=F("-0.92065667800760613175")
z0=F("0.06189741100766035970")
q=I(q0-radius,q0+radius)
y=I(y0-radius,y0+radius)
z=I(z0-radius,z0+radius)
one,two=I(1),I(2)
c=(one-z*z)/(one+z*z)
s=two*z/(one+z*z)
x1=(q-y*y).sqrt()
x2=(q-(y+two)*(y+two)).sqrt()
x3=x2-3
y3=(q-x3*x3).sqrt()
y4=y3-two
x4=-(q-y4*y4).sqrt()
h1=c*x1+s*y-two-c
h2=-s*x4+c*y4-one-s

# Exact unnormalized positive force multipliers at the
# stationary five-corner pseudo-chain, W0=1.
mA0=c/(two*x1)
ab0=s-c*y/x1
mB0=ab0/(two*(y+two))
tb0=ab0*x2/(y+two)
mD0=-tb0/(two*x3)
ed0=two*mD0*y3
mH0=-one/(two*h1)
he0=h2/h1
mE0=-s*he0/(two*x4)

factor=one/(mA0+mB0+mD0+mE0+mH0)
mA,mB,mD,mE,mH=[
    x*factor for x in (mA0,mB0,mD0,mE0,mH0)]
ab,tb,dt,ed,W,wHG,he=[
    x*factor for x in (ab0,tb0,tb0,ed0,one,one,he0)]
for label,value in zip(
        ("mA","mB","mD","mE","mH",
         "ab","tb","dt","ed","W","wHG","he"),
        (mA,mB,mD,mE,mH,
         ab,tb,dt,ed,W,wHG,he)):
    value.gt(0)
    print(label, value.show())
(mA+mB+mD+mE+mH-one).includes_zero(F(1,10**12))

gamma=[
    ab/two,
    (ab+tb)/two,
    tb,
    (dt+ed)/two,
    ed/two,
    (W+he)/two,
    W,
]
B=[
    mA*(x1+y)-W*(c-s)/two,
    mB*(y+two-x2),
    I(0),
    -mD*(x3+y3),
    mE*(x4-y4)-he*(c-s)/two,
    mH*(h1-h2),
    I(0),
]
A=[
    gamma[0]+mA*(x1-y)+W*(c+s)/two,
    gamma[1]+mB*(x2+y+two),
    gamma[2],
    gamma[3]+mD*(-x3+y3),
    gamma[4]+mE*(-x4-y4)+he*(c+s)/two,
    gamma[5]-mH*(h1+h2),
    gamma[6],
]
names=("A","B","T","D","E","H","G")
for name,gg,bb,aa in zip(names,gamma,B,A):
    margin=gg-abs(bb)
    margin.gt(F(1,40))
    abs(aa).lt(2)
    print(name,"angle cusp reserve",margin.show(),
          "|cos coefficient|",abs(aa).show())

# Verify the small stationarity enclosure (not an axiom).
# The companion hand proof derives this equality exactly
# from F_y(q*,y*,t*)=0 and the chain differentiation.
residE=two*mE*y4+ed-c*he
residE.includes_zero(F(1,10**12))

# The F_t condition is NOT required for adaptive weights:
# their reference tilt t varies and h1,h2 adapt to it.
# However the old frozen dual has negative curvature.
Kc=W+ed*he/(two*mE)
Ks=he+ab*W/(two*mA)
Kc.gt(0);Ks.gt(0)
K=Kc*c+Ks*s
K.gt(13)
K.lt(F(133,10))
print("frozen positive dual tilt curvature = -K, K",K.show())
print("PASS: all 7 strict adaptive angular margins Gamma-|B|>1/40")
print("PASS: all 7 |A|<2 and all 12 force multipliers positive")
print("PASS: exact candidate-box angular coefficient bounds")
