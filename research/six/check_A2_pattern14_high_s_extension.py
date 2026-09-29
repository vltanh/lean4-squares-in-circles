#!/usr/bin/env python3
"""Exact scalar check for the missing Pattern-14 positive-s range.

On the nonnegative-W candidate strip

    0 <= w <= 2/25,
    1/6 <= s <= 2/5,
   -1/4 <= eps <= 0,

the reduced Pattern-12 cardinal/cardinal envelope is
    F = a(w)+b(s)+D(w,s,eps)
with b(s)=B_Es(0,s).

The old proof invoked MON7/MON10 outside their stated s<1/6 domain.
This checker instead verifies the combined derivative directly through the
exact cap/vertex support switch:

    d/ds [b(s)+D(w,s,eps)] > 1/20.

Therefore s moves monotonically to 1/6, where the previously proved
small-strip reduction takes over.
"""
from fractions import Fraction as F
import n6_a2_scalar as X

I,J=X.I,X.J
jj,jcos,jsin=X.jj,X.jcos,X.jsin
R,rho=X.R,X.rho

h=X.h
ss=X.ss
tt=(-F(20)+F(30)*h)*ss+F(7,2)-F(9,2)*h
r=(ss+F(1,2))/(ss+F(3,2))
k=(tt+F(1,2))/(F(3,2)-ss)
m=(1+r)*k
rt2=X.sqrt_bounds(F(2),150)
SQRT2=I(rt2.lo,rt2.hi)

def bpos(s):
    s=jj(s)
    sn,cs=jsin(s),jcos(s)
    H=F(1,2)+(cs+sn)/2
    GEx=J(1); GEy=J(r)
    GSx=cs*(1+r); GSy=J(m)-sn*(1+r)
    return J(1)+H*(1+r)+J(m)/2-X.support_any(GEx,GEy)-X.support_any(GSx,GSy)

def Dcap(beta,delta):
    beta,delta=jj(beta),jj(delta)
    return J(SQRT2)*J(m)*(J(1-rho)*jcos(beta)+J(rho)*jsin(beta))*jcos(delta)

def Dvert(beta,delta):
    beta,delta=jj(beta),jj(delta)
    cb,sb=jcos(beta),jsin(beta)
    cd,sd=jcos(delta),jsin(delta)
    return J(SQRT2)*J(m)*(
        ((3*cb-sb)/2)*cd-((cb-sb)/2)*sd-J(R)*(cb-sb))

def D_s(w,s,eps):
    beta=J((w.v-s.v)/2,-F(1,2))
    delta=J(eps.v-(w.v+s.v)/2,-F(1,2))
    cap=Dcap(beta,delta)
    vert=Dvert(beta,delta)
    sd=X.sinR(delta.v)
    assert sd.hi < 0
    switch=2*R*(-sd)-I(1)
    if switch.hi<=0:
        return cap.d
    if switch.lo>=0:
        return vert.d
    return X.hullI(cap.d,vert.d)

W=(F(0),F(2,25))
S=(F(1,6),F(2,5))
E=(-F(1,4),F(0))

best=F(100)
where=None
count=0
for wa,wb in X.parts(*W,F(1,50)):
    for sa,sb in X.parts(*S,F(1,50)):
        bd=bpos(J(I(sa,sb),1)).d
        for ea,eb in X.parts(*E,F(1,50)):
            ds=D_s(J(I(wa,wb)),J(I(sa,sb)),J(I(ea,eb)))
            lo=bd.lo+ds.lo
            if lo<best:
                best=lo
                where=(wa,wb,sa,sb,ea,eb)
            count+=1

assert best>F(1,20),(best,where)
print("Pattern 14 high-s extension: PASS")
print("boxes",count,"combined derivative >",float(best))
