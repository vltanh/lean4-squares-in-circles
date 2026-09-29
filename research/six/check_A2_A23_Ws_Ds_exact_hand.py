#!/usr/bin/env python3
"""Exact scalar audit for the repaired A2.3 Ws/Ds middle chamber.

Domain: -2/3 <= w <= pi/4, -1/5 <= s <= 1/5,
1/2 <= d <= pi/4, with cyclic constraint w <= d.
Stress: (CW,SC,CD,DW,DS)=(400,59,155,183,203)/1000.

The old checker double-counted the CW/SC source-square half-width constants
and also asserted an s-concavity that is false.  This checker starts from the
correctly normalized five-edge support defect.  G_Cx is positive throughout;
G_Cy may change sign, so both exact central-rectangle support branches are
audited.  The valid reduction is:
  * w-concavity, including the central-y support wall;
  * partial_s Phi < 0, replacing the false s-concavity;
  * one-dimensional d edges and the cyclic wall w=d.
"""
from fractions import Fraction as F
import n6_a2_scalar as X

I,J=X.I,X.J
jj,jcos,jsin=X.jj,X.jcos,X.jsin
c0,PI=X.c0,X.PI
W=tuple(F(x,1000) for x in (400,59,155,183,203))
mw,ms,md,m7,m8=W
assert sum(W)==1
SR=(-F(1,5),F(1,5)); WR=(-F(2,3),PI.hi/4); DR=(F(1,2),PI.hi/4)

def jpos(x):
    x=jj(x)
    if x.v.lo>=0:return x
    if x.v.hi<=0:return J(0)
    return X.hullJ(J(0),x)

def pieces(sw,ss,cy_on):
    def FW(x):
        x=jj(x);c,s=jcos(x),jsin(x)
        return mw*(c+sw*s)/2-jj(c0)*mw*c-(jj(c0)*mw*s if cy_on else J(0))
    def GS(x):
        x=jj(x);c,s=jcos(x),jsin(x)
        return ms*(c+ss*s)/2+jj(c0)*ms*s-(jj(c0)*ms*c if cy_on else J(0))
    def HD(x):
        x=jj(x);c,s=jcos(x),jsin(x)
        return md*(c+s)/2-jj(c0)*md*c-(jj(c0)*md*s if cy_on else J(0))
    def KD(x):
        x=jj(x);c,s=jcos(x),jsin(x)
        return m7*(c+s)/2-X.support_any(md+m7*s,m7*c-m8)
    def LT(x):
        x=jj(x);c,s=jcos(x),jsin(x)
        return m8*(c+s)/2-X.support_any(ms+m8*c,m8*s)
    # The common source-square half-width contribution is
    # (sum weights)/2 = 1/2, once, not once per central edge.
    const=J(F(1,2))-X.support_any(J(mw),J(-m7))
    return const,FW,GS,HD,KD,LT

def exact_gap(sw,ss):
    def FW(x):x=jj(x);return mw*(jcos(x)+sw*jsin(x))/2
    def GS(x):x=jj(x);return ms*(jcos(x)+ss*jsin(x))/2
    def HD(x):x=jj(x);return md*(jcos(x)+jsin(x))/2
    def KD(x):x=jj(x);return m7*(jcos(x)+jsin(x))/2-X.support_any(md+m7*jsin(x),m7*jcos(x)-m8)
    def LT(x):x=jj(x);return m8*(jcos(x)+jsin(x))/2-X.support_any(ms+m8*jcos(x),m8*jsin(x))
    const=J(F(1,2))-X.support_any(J(mw),J(-m7))
    def gap(w,s,d):
        gx=mw*jcos(w)-ms*jsin(s)+md*jcos(d)
        gy=mw*jsin(w)+ms*jcos(s)+md*jsin(d)
        return const+FW(w)+GS(s)+HD(d)+KD(d-w)+LT(d-s)-jj(c0)*(gx+jpos(gy))
    return gap

# G_Cx is positive everywhere, so only G_Cy creates a central-support wall.
cw=X.cosR(I(*WR)); ss0=X.sinR(I(*SR)); cd=X.cosR(I(*DR))
assert mw*cw.lo-ms*ss0.hi+md*cd.lo > F(3,10)

# On either side of G_Cy=0, w is concave.  Since
# dG_Cy/dw=mw cos w>0, crossing the wall as w increases adds
# -c0*dG_Cy/dw to the derivative: a downward jump, preserving concavity.
for cy in (False,True):
    for wa,wb in ((-F(2,3),0),(0,F(1,2)),(F(1,2),PI.hi/4)):
        sw=-1 if wb<=0 else 1
        _,FW,GS,HD,KD,LT=pieces(sw,1,cy)
        de=(max(F(0),DR[0]-wb),DR[1]-wa)
        assert X.maxdd(FW,wa,wb,F(1,100))+X.maxdd(KD,*de,F(1,100)) < -F(1,20)

# After fixed-w reduction, partial_s Phi is negative on both signs of s and
# both central-y branches.  At G_Cy=0 the derivative again jumps downward in
# the direction of increasing s (on either side of s=0).  Hence s moves to 1/5.
for cy in (False,True):
  for w0 in (-F(2,3),F(0)):
    for sa,sb in ((-F(1,5),0),(0,F(1,5))):
      ss=-1 if sb<=0 else 1
      tr=(DR[0]-sb,DR[1]-sa)
      _,FW,GS,HD,KD,LT=pieces(1,ss,cy)
      gd=X.drange(GS,sa,sb,F(1,100))
      ld=X.drange(LT,*tr,F(1,100))
      assert gd[1]-ld[0] < -F(1,100)

# At s=1/5 the remaining d-edge is concave for w=-2/3 and w=0 on either
# central-y branch, so d reduces to 1/2 or pi/4.
s0=F(1,5)
for cy in (False,True):
  for w0 in (-F(2,3),F(0)):
    _,FW,GS,HD,KD,LT=pieces(1,1,cy)
    def dfun(d): return HD(d)+KD(d-J(I(w0)))+LT(d-J(I(s0)))
    assert X.maxdd(dfun,*DR,F(1,100)) < -F(1,100)

# On the cyclic wall w=d, s again moves to 1/5.  There the d derivative is
# positive on either central-y branch, so d=w moves to 1/2.
for cy in (False,True):
  _,FW,GS,HD,KD,LT=pieces(1,1,cy)
  def cyc(d): return FW(d)+HD(d)+LT(d-J(I(s0)))
  dr=X.drange(cyc,*DR,F(1,100))
  assert dr[0] > F(1,20)

# Exact central support on the remaining scalar endpoints.
best=F(100)
for w0 in (-F(2,3),F(0)):
  sw=-1 if w0<0 else 1
  gap=exact_gap(sw,1)
  for d0 in (F(1,2),PI.hi/4):
    z=gap(J(I(w0)),J(I(s0)),J(I(d0))).v.lo
    best=min(best,z)
gap=exact_gap(1,1)
z=gap(J(I(F(1,2))),J(I(s0)),J(I(F(1,2)))).v.lo
best=min(best,z)
assert best > F(1,100),best

print('A2.3 Ws/Ds middle exact audit: PASS')
print('endpoint margin >',float(best))
