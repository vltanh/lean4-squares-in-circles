#!/usr/bin/env python3
"""Exact scalar audit of the repaired Pattern-26 Ws/Sp classification.

No multidimensional search is used. For the low and middle s chambers,
separate concavity first reduces (s,d) to scalar w edges. The W support is
then handled with its actual cap/vertex branch. The high s chamber is closed
by the single central-S stress.
"""
from fractions import Fraction as F
import n6_a2_scalar as X
I,J=X.I,X.J; jj,jcos,jsin,jsqrt=X.jj,X.jcos,X.jsin,X.jsqrt
R,rho,c0,PI=X.R,X.rho,X.c0,X.PI
WR=(-F(2,5),F(2,5)); DR=(F(1,2),PI.lo/4)

def row(W):
    a,b,md,p,q=(F(z,1000) for z in W)
    assert a+b+md+p+q==1 and md==0
    const=-jj(c0)*a-jj(rho)*(b+q)
    def GS(s,sgn):
        s=jj(s);c,t=jcos(s),jsin(s)
        return b*(F(1,2)+(c+sgn*t)/2)-jj(c0)*b*(c-t)
    def KD(z):z=jj(z);return p*(F(1,2)+(jcos(z)+jsin(z))/2)
    def LT(z,sgn=1):z=jj(z);return q*(F(1,2)+(jcos(z)+sgn*jsin(z))/2)
    def MX(z):
        z=jj(z);return -(jj(R)-F(1,2))*jsqrt(p*p+q*q-2*p*q*jcos(z))
    def Wcoords(w):
        w=jj(w);return a*jcos(w),p+a*jsin(w)
    def FW_exact(w,sgn):
        w=jj(w);c,t=jcos(w),jsin(w);wx,wy=Wcoords(w)
        return a*(F(1,2)+(c+sgn*t)/2)-X.support_any(wx,wy)
    def FW_cap(w,sgn):
        w=jj(w);c,t=jcos(w),jsin(w)
        return a*(F(1,2)+(c+sgn*t)/2)-jj(rho)*a*c
    def FW_vert(w,sgn):
        w=jj(w);c,t=jcos(w),jsin(w);wx,wy=Wcoords(w)
        return a*(F(1,2)+(c+sgn*t)/2)-(jj(R)*jsqrt(wx*wx+wy*wy)-(wx+wy)/2)
    return const,GS,KD,LT,MX,Wcoords,FW_exact,FW_cap,FW_vert

def branch_switch(Wcoords,lo,hi,expect,step=F(1,50)):
    """Prove cap (<0) or vertex (>0): 2 R V - |g|."""
    for a,b in X.parts(lo,hi,step):
        w=J(I(a,b)); wx,wy=Wcoords(w); ax,ay=X.jabs(wx),X.jabs(wy)
        norm=jsqrt(wx*wx+wy*wy)
        vlo=min(ax.v.lo,ay.v.lo); vhi=min(ax.v.hi,ay.v.hi)
        swlo=2*R.lo*vlo-norm.v.hi; swhi=2*R.hi*vhi-norm.v.lo
        if expect=='cap': assert swhi<0,(a,b,swlo,swhi)
        else: assert swlo>0,(a,b,swlo,swhi)

def reduce_sd(W,sr):
    const,GS,KD,LT,MX,*_=row(W)
    scuts=[sr[0]]
    if sr[0]<0<sr[1]:scuts.append(F(0))
    scuts.append(sr[1])
    for sa,sb in zip(scuts,scuts[1:]):
        sgn=-1 if sb<=0 else 1
        ta=DR[0]-sb;tb=DR[1]-sa
        assert ta>=0
        sdd=(X.maxdd(lambda z:GS(z,sgn),sa,sb,F(1,50))
             +X.maxdd(LT,ta,tb,F(1,50))
             +X.maxdd(MX,sa-WR[1],sb-WR[0],F(1,50)))
        ddd=(X.maxdd(KD,DR[0]-WR[1],DR[1]-WR[0],F(1,50))
             +X.maxdd(LT,ta,tb,F(1,50)))
        assert sdd<0 and ddd<0,(sa,sb,sdd,ddd)

W1=(664,0,0,178,158); sr1=(-F(27,100),F(1,5))
const,GS,KD,LT,MX,Wcoords,FW,FC,FV=row(W1)
reduce_sd(W1,sr1)
branch_switch(Wcoords,-F(2,5),F(0),'cap',F(1,100))
branch_switch(Wcoords,F(0),F(1,25),'cap',F(1,500))
branch_switch(Wcoords,F(9,200),F(2,5),'vertex',F(1,200))
cases1=[(s,d) for s in (-F(27,100),F(0),F(1,5)) for d in (F(1,2),PI.lo/4)]
transition=F(100); endpoints=F(100)
for s0,d0 in cases1:
    sgn=-1 if s0<0 else 1
    base=const+GS(J(I(s0)),sgn)+LT(J(I(d0-s0)))
    def capneg(w):return base+FC(w,-1)+KD(J(I(d0))-w)+MX(J(I(s0))-w)
    def cappos(w):return base+FC(w,1)+KD(J(I(d0))-w)+MX(J(I(s0))-w)
    def vertpos(w):return base+FV(w,1)+KD(J(I(d0))-w)+MX(J(I(s0))-w)
    dn=X.drange(capneg,-F(2,5),F(0),F(1,50)); dp=X.drange(cappos,F(0),F(1,25),F(1,50))
    assert dn[1]<0 and dp[0]>0,(s0,d0,dn,dp)
    assert X.maxdd(vertpos,F(9,200),F(2,5),F(1,50))<0
    def exact(w):return base+FW(w,1)+KD(J(I(d0))-w)+MX(J(I(s0))-w)
    transition=min(transition,X.minval(exact,F(1,25),F(9,200),F(1,1000)))
    for w0 in (F(0),F(2,5)):
        endpoints=min(endpoints,exact(J(I(w0))).v.lo)
assert transition>F(1,50) and endpoints>F(3,200),(transition,endpoints)

W2=(446,0,0,328,226);sr2=(F(1,5),F(1,2))
const,GS,KD,LT,MX,Wcoords,FW,FC,FV=row(W2)
reduce_sd(W2,sr2)
branch_switch(Wcoords,-F(2,5),F(2,5),'vertex',F(1,100))
cases2=[(s,d) for s in (F(1,5),F(1,2)) for d in (F(1,2),PI.lo/4)]
end2=F(100)
for s0,d0 in cases2:
    base=const+GS(J(I(s0)),1)+LT(J(I(d0-s0)))
    def neg(w):return base+FV(w,-1)+KD(J(I(d0))-w)+MX(J(I(s0))-w)
    def pos(w):return base+FV(w,1)+KD(J(I(d0))-w)+MX(J(I(s0))-w)
    assert X.maxdd(neg,-F(2,5),F(0),F(1,50))<0
    assert X.maxdd(pos,F(0),F(2,5),F(1,50))<0
    for w0 in (-F(2,5),F(0),F(2,5)):
        f=neg if w0<0 else pos
        end2=min(end2,f(J(I(w0))).v.lo)
assert end2>F(7,1000),end2

def high(s):
    s=jj(s);c,t=jcos(s),jsin(s)
    return -jj(rho)+F(1,2)+(c+t)/2-jj(c0)*(c-t)
dh=X.drange(high,F(1,2),F(4,5),F(1,50))
assert dh[0]>F(1,10),dh
high0=high(J(I(F(1,2)))).v.lo
assert high0>F(1,50),high0

print('Pattern 26 Ws/Sp repaired scalar audit: PASS')
print('low transition >',float(transition),'low endpoints >',float(endpoints))
print('middle endpoints >',float(end2),'high endpoint >',float(high0))
