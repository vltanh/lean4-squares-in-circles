#!/usr/bin/env python3
"""Exact scalar audit for the repaired first A2.3 Ds/Ds row."""
from fractions import Fraction as F
import n6_a2_scalar as X
I,J=X.I,X.J; jj,jcos,jsin=X.jj,X.jcos,X.jsin
PI,c0=X.PI,X.c0
W=tuple(F(x,1000) for x in (139,261,18,284,298));mw,ms,md,m7,m8=W
assert sum(W)==1
SR=(-PI.hi/4,-F(1,5));DR=(F(1,2),PI.hi/4);s0=-F(1,5)

def pieces(sw):
 def FW(w):w=jj(w);c,s=jcos(w),jsin(w);return mw*(c+sw*s)/2-jj(c0)*mw*(c+s)
 def GS(s):s=jj(s);c,t=jcos(s),jsin(s);return ms*(c-t)/2-jj(c0)*ms*(c-t)
 def HD(d):d=jj(d);return md*(jcos(d)+jsin(d))/2-jj(c0)*md*(jcos(d)+jsin(d))
 def KD(z):z=jj(z);c,t=jcos(z),jsin(z);return m7*(c+t)/2-X.support_any(mw+m7*t,-m7*c)
 def LT(t):t=jj(t);c,s=jcos(t),jsin(t);return m8*(c+s)/2-X.support_any(ms+m8*c,m8*s)
 const=J(F(1,2))-X.support_any(J(md),J(m7-m8))
 return const,FW,GS,HD,KD,LT

sw=X.sinR(I(-F(2,3),PI.hi/4));cw=X.cosR(I(-F(2,3),PI.hi/4))
ss=X.sinR(I(*SR));cs=X.cosR(I(*SR));sd=X.sinR(I(*DR));cd=X.cosR(I(*DR))
assert mw*cw.lo-ms*ss.hi+md*cd.lo>F(4,25)
assert mw*sw.lo+ms*cs.lo+md*sd.lo>F(1,10)

# The archived full w-concavity claim is false. The far-negative pieces are
# monotone increasing; the remaining pieces are concave.
for wa,wb,lower in [(-F(2,3),-F(2,5),F(2,25)),(-F(2,5),-F(1,5),F(3,200))]:
 _,FW,GS,HD,KD,LT=pieces(-1);de=(DR[0]-wb,DR[1]-wa)
 fd=X.drange(FW,wa,wb,F(1,100));kd=X.drange(KD,*de,F(1,100))
 assert fd[0]-kd[1]>lower
for wa,wb in [(-F(1,5),0),(0,F(1,5)),(F(1,5),F(2,5)),(F(2,5),F(1,2)),(F(1,2),PI.hi/4)]:
 _,FW,GS,HD,KD,LT=pieces(-1 if wb<=0 else 1);de=(max(F(0),DR[0]-wb),DR[1]-wa)
 assert X.maxdd(FW,wa,wb,F(1,100))+X.maxdd(KD,*de,F(1,100)) < -F(1,4)

# Move s to -1/5 by monotonicity before analyzing d.
_,FW,GS,HD,KD,LT=pieces(-1)
gd=X.drange(GS,*SR,F(1,100));ld=X.drange(LT,DR[0]-SR[1],DR[1]-SR[0],F(1,100))
assert gd[1]-ld[0] < -F(1,50)

fixed=(-F(2,3),-F(2,5),-F(1,5),F(0),F(1,5),F(2,5),F(1,2))
for w0 in fixed:
 _,FW,GS,HD,KD,LT=pieces(-1 if w0<0 else 1)
 dlo=max(DR[0],w0)
 def edge(d):return HD(d)+KD(d-J(I(w0)))+LT(d-J(I(s0)))
 assert X.maxdd(edge,dlo,DR[1],F(1,100)) < -F(1,25)

# On the cyclic wall w=d, d increases Phi, so the wall moves to d=1/2.
_,FW,GS,HD,KD,LT=pieces(1)
def cyc(d):return FW(d)+HD(d)+LT(d-J(I(s0)))
dr=X.drange(cyc,*DR,F(1,100));assert dr[0]>F(1,8)

best=F(100)
for w0 in fixed:
 const,FW,GS,HD,KD,LT=pieces(-1 if w0<0 else 1);dlo=max(DR[0],w0)
 for d0 in (dlo,DR[1]):
  z=(const+FW(J(I(w0)))+GS(J(I(s0)))+HD(J(I(d0)))
     +KD(J(I(d0-w0)))+LT(J(I(d0-s0)))).v.lo
  best=min(best,z)
const,FW,GS,HD,KD,LT=pieces(1)
d0=F(1,2)
z=(const+FW(J(I(d0)))+GS(J(I(s0)))+HD(J(I(d0)))
   +KD(J(I(0)))+LT(J(I(d0-s0)))).v.lo
best=min(best,z)
assert best>F(1,10),best
print('A2.3 Ds/Ds first-row exact audit: PASS')
print('endpoint margin >',float(best))
