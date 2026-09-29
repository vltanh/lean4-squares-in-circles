#!/usr/bin/env python3
"""Exact scalar audit for Pattern 27 on 21/50 <= s <= 11/25.

The hand proof reduces the reflected own-own source comparison to three n
edges.  This checks those scalar edges and replaces the stale w=0 face
citation with an exact cap/vertex calculation.
"""
from fractions import Fraction as F
import n6_a2_scalar as X
I,J=X.I,X.J; jj,jcos,jsin,jsqrt=X.jj,X.jcos,X.jsin,X.jsqrt
R,rho=X.R,X.rho; h=X.h; ss=X.ss
tt=(-20+30*h)*ss+F(7,2)-F(9,2)*h
r=(ss+F(1,2))/(ss+F(3,2)); m=(1+r)*(tt+F(1,2))/(F(3,2)-ss)
SQ2=X.sqrtI(I(2)); K=F(73,100); SLO=F(21,50); SHI=F(11,25)
EPSLO=F(1,2)-X.PI.hi/4

def far_signed(x,y):
    x,y=jj(x),jj(y)
    return jj(R)*jsqrt(x*x+y*y)-(x-y)/2

def pairB(n,w,src,sign_n,sign_q):
    n,w=jj(n),jj(w);cn,sn=jcos(n),jsin(n);cw,sw=jcos(w),jsin(w)
    q=n-w;cq,sq=jcos(q),jsin(q)
    alpha=(cw+sw)/jcos(w-n);gamma=(cn-sn)/jcos(w-n)
    HN=F(1,2)+(cn+sign_n*sn)/2;HW=F(1,2)+(cw-sw)/2
    HQ=F(1,2)+(cq+sign_q*sq)/2
    if src=="Wp":
        GNx=alpha-jj(r)*sq;GNy=-jj(r)*cq;GWx=gamma+jj(r);GWy=-jj(m);UN=far_signed(GNx,GNy)
    elif src=="Ws":
        GNx=alpha+jj(r)*cq;GNy=-jj(r)*sq;GWx=gamma;GWy=jj(r)-jj(m);UN=jj(rho)*GNx
    elif src=="Np":
        GNx=alpha+jj(r);GNy=J(0);GWx=gamma-jj(r)*sq;GWy=jj(r)*cq-jj(m);UN=jj(rho)*GNx
    elif src=="Ns":
        GNx=alpha;GNy=-jj(r);GWx=gamma+jj(r)*cq;GWy=jj(r)*sq-jj(m);UN=far_signed(GNx,GNy)
    else:
        raise KeyError(src)
    return alpha*HN+gamma*HW+jj(r)*HQ+jj(m)/2-UN-far_signed(GWx,GWy)

BSTAR=pairB(J(0),J(0),"Wp",1,1).v
WLO=-SHI;WHI=-SLO

def reserve(n,w,src,sign_n):
    return pairB(n,w,src,sign_n,1)-J(BSTAR)+J(K)*w

# Ws still uses its N cap branch on the enlarged endpoint.
cap=F(100)
for a,b in X.parts(F(0),F(257,300),F(1,200)):
    t=J(I(a,b));c,s=jcos(t),jsin(t)
    z=F(1,2)/c+jj(r)*c-2*jj(R)*jj(r)*s
    cap=min(cap,z.v.lo)
assert cap>F(1,100),cap

# The hand n-calculus leaves n=-3/10,0,5/12.  Each scalar w edge is
# monotone or concave on [-11/25,-21/50].
EDGES=[(-F(3,10),-1),(F(0),1),(F(5,12),1)]
pairbest=F(100)
for src in ("Wp","Ws","Np","Ns"):
    for n0,sgn in EDGES:
        def edge(w):
            return reserve(J(I(n0)),w,src,sgn)
        dr=X.drange(edge,WLO,WHI,F(1,400))
        dd=X.maxdd(edge,WLO,WHI,F(1,400))
        if dr[0]>0:
            pts=(WLO,)
        elif dr[1]<0:
            pts=(WHI,)
        else:
            assert dd<0,(src,n0,dr,dd)
            pts=(WLO,WHI)
        for w0 in pts:
            pairbest=min(pairbest,edge(J(I(w0))).v.lo)
assert pairbest>F(1,1000),pairbest

def Dcap(beta,delta):
    return J(SQ2)*J(m)*(J(1-rho)*jcos(beta)+J(rho)*jsin(beta))*jcos(delta)
def Dvert(beta,delta):
    cb,sb=jcos(beta),jsin(beta);cd,sd=jcos(delta),jsin(delta)
    return J(SQ2)*J(m)*(((3*cb-sb)/2)*cd-((cb-sb)/2)*sd-J(R)*(cb-sb))
D0=Dcap(J(0),J(0)).v

# w=0 face: vertex pieces are concave in epsilon; cap pieces decrease in
# epsilon.  Thus only the lower vertex endpoint and epsilon=0 cap endpoint
# remain, and each resulting s edge is monotone.
BETA=I(-SHI/2,-SLO/2)
cap_der=-F(100);vert_dd=-F(100)
for a,b in X.parts(-F(31,100),-SLO/2,F(1,500)):
    cap_der=max(cap_der,Dcap(J(BETA),J(I(a,b),1)).d.hi)
for a,b in X.parts(EPSLO-SHI/2,-F(5,17),F(1,500)):
    vert_dd=max(vert_dd,Dvert(J(BETA),J(I(a,b),1)).dd.hi)
assert cap_der<-F(1,100),cap_der
assert vert_dd<-F(1),vert_dd

def face0_cap(s):
    s=jj(s)
    return J(K)*s+Dcap(-s/2,-s/2)-J(D0)
def face0_vert(s):
    s=jj(s)
    return J(K)*s+Dvert(-s/2,J(EPSLO)-s/2)-J(D0)

dc=X.drange(face0_cap,SLO,SHI,F(1,500))
dv=X.drange(face0_vert,SLO,SHI,F(1,500))
assert dc[0]>F(1,20),dc
assert dv[1]<0,dv
face0=min(face0_cap(J(I(SLO))).v.lo,face0_vert(J(I(SHI))).v.lo)
assert face0>F(1,50),face0

print("Pattern 27 high-s pair/w=0: PASS")
print("pair reserve >",float(pairbest))
print("w=0 face >",float(face0))
