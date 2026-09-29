#!/usr/bin/env python3
"""Exact interval audit for the Pattern-27 w=2/5 high-s face.

Only the formerly uncovered strip 21/50 <= s <= 11/25 is checked here.
This is an arithmetic audit of the scalar hand inequality, not a packing-state
box certificate.
"""
from fractions import Fraction as F
import n6_a2_scalar as X
I,J=X.I,X.J;jj,jcos,jsin=X.jj,X.jcos,X.jsin
h=X.h;ss=X.ss
tt=(-20+30*h)*ss+F(7,2)-F(9,2)*h
r=(ss+F(1,2))/(ss+F(3,2));m=(1+r)*(tt+F(1,2))/(F(3,2)-ss)
SQ2=X.sqrtI(I(2));R,rho=X.R,X.rho
K=F(73,100);W=F(2,5)
S=(F(21,50),F(11,25))
E=(F(1,2)-X.PI.hi/4,F(0))

def hpos(x):
    x=jj(x)
    return F(1,2)+(jcos(x)+jsin(x))/2

def aprof(w):
    w=jj(w);sn,cs=jsin(w),jcos(w);H=hpos(w)
    return (1+(1+jj(r))*H+jj(m)/2
            -X.support_any(1+jj(r)*sn,jj(r)*cs)
            -X.support_any(cs+jj(r),sn+jj(m)))

AD=aprof(J(W)).v-aprof(J(0)).v

def Dcap(beta,delta):
    return J(SQ2)*J(m)*(J(1-rho)*jcos(beta)+J(rho)*jsin(beta))*jcos(delta)

def Dvert(beta,delta):
    cb,sb=jcos(beta),jsin(beta);cd,sd=jcos(delta),jsin(delta)
    return J(SQ2)*J(m)*(
        ((3*cb-sb)/2)*cd-((cb-sb)/2)*sd-J(R)*(cb-sb))

def Dactual(beta,delta):
    cap=Dcap(beta,delta)
    V=X.jabs(jsin(delta))
    sw=2*R*V.v-I(1)
    vert=Dvert(beta,delta)
    if sw.hi<=0:
        return cap
    if sw.lo>=0:
        return vert
    return X.hullJ(cap,vert)

D0=Dcap(J(0),J(0)).v
best=F(100);where=None
for sa,sb in X.parts(*S,F(1,500)):
    for ea,eb in X.parts(*E,F(1,500)):
        sv=J(I(sa,sb));ev=J(I(ea,eb))
        z=(J(AD)+J(K)*sv
           +Dactual((J(W)-sv)/2,ev-(J(W)+sv)/2)-J(D0)).v
        if z.lo<best:
            best=z.lo;where=(sa,sb,ea,eb)

assert best>F(1,20),(best,where)
print("Pattern 27 w=2/5 high-s face: PASS")
print("margin >",float(best))
