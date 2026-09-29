#!/usr/bin/env python3
"""Exact scalar repair for the first hard A2.3 Ds/Ss cell."""
from fractions import Fraction as F
import n6_a2_scalar as X
I,J=X.I,X.J; jj,jcos,jsin=X.jj,X.jcos,X.jsin
PI,c0=X.PI,X.c0
W=tuple(F(x,1000) for x in (373,248,76,168,135));mw,ms,md,m7,m8=W
assert sum(W)==1
WR=(-F(2,3),-F(3,5));SR=(-F(1,5),-F(1,10));DR=(F(1,2),PI.hi/4)

def pieces():
 def FW(w):w=jj(w);c,s=jcos(w),jsin(w);return mw*(c-s)/2-jj(c0)*mw*(c+s)
 def GS(s):s=jj(s);c,t=jcos(s),jsin(s);return ms*(c-t)/2-jj(c0)*ms*(c-t)
 def HD(d):d=jj(d);return md*(jcos(d)+jsin(d))/2-jj(c0)*md*(jcos(d)+jsin(d))
 def KD(z):z=jj(z);c,t=jcos(z),jsin(z);return m7*(c+t)/2-X.support_any(mw+m7*t,-m7*c)
 def LT(t):t=jj(t);c,s=jcos(t),jsin(t);return m8*(c+s)/2-X.support_any(md+m8*c,m7-m8*s)
 const=J(F(1,2))-X.support_any(J(ms),J(m8))
 return const,FW,GS,HD,KD,LT
const,FW,GS,HD,KD,LT=pieces()

sw=X.sinR(I(*WR));cw=X.cosR(I(*WR));ss=X.sinR(I(*SR));cs=X.cosR(I(*SR))
sd=X.sinR(I(*DR));cd=X.cosR(I(*DR))
assert mw*cw.lo-ms*ss.hi+md*cd.lo>0
assert mw*sw.lo+ms*cs.lo+md*sd.lo>0

de=(DR[0]-WR[1],DR[1]-WR[0])
assert X.maxdd(FW,*WR,F(1,100))+X.maxdd(KD,*de,F(1,100)) < -F(3,20)

# The archived d-concavity assertion is false. Move s first.
tr=(DR[0]-SR[1],DR[1]-SR[0])
gd=X.drange(GS,*SR,F(1,100));ld=X.drange(LT,*tr,F(1,100))
assert gd[1]-ld[0] < -F(9,50)

s0=-F(1,10);best=F(100)
for w0 in WR:
 def edge(d):
  return const+FW(J(I(w0)))+GS(J(I(s0)))+HD(d)+KD(d-J(I(w0)))+LT(d-J(I(s0)))
 dr=X.drange(edge,*DR,F(1,100));assert dr[0]>F(1,250),(w0,dr)
 z=edge(J(I(F(1,2)))).v.lo;best=min(best,z)
assert best>F(9,500),best
print('A2.3 hard Ds/Ss first-cell exact audit: PASS')
print('endpoint margin >',float(best))
