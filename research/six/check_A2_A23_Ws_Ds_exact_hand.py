#!/usr/bin/env python3
"""Exact scalar audit for the repaired A2.3 Ws/Ds middle-s chamber.

Domain:
    -2/3 <= w <= pi/4,  -1/5 <= s <= 1/5,  1/2 <= d <= pi/4,
    w <= d.

The old single stress (365,187,106,185,157)/1000 is replaced by five
fixed w-chambers.  The defect is normalized directly from the five separator
weights: the global 1/2 term already contains the source-square half-widths,
so no extra CW/2 or SC/2 constants are added.

Each row has positive central-force coordinates.  The exact outer support is
n6_a2_scalar.support_any.  The valid reduction is:
  * strict w-concavity on each fixed chamber;
  * uniform partial_s Phi < 0 (not s-concavity);
  * scalar d-edge positivity after s=1/5.
"""
from fractions import Fraction as F
import n6_a2_scalar as X

I,J=X.I,X.J
jj,jcos,jsin=X.jj,X.jcos,X.jsin
PI,c0=X.PI,X.c0
DR=(F(1,2),PI.hi/4)
SR=(-F(1,5),F(1,5))

ROWS=[
 ((-F(2,3),-F(2,5)),(371,171,130,163,165)),
 ((-F(2,5),-F(1,5)),(363,82,129,198,228)),
 ((-F(1,5),F(0)),(400,59,155,183,203)),
 ((F(0),F(1,2)),(400,59,155,183,203)),
 ((F(1,2),PI.hi/4),(400,59,155,183,203)),
]
ROWS=[(wr,tuple(F(x,1000) for x in W)) for wr,W in ROWS]
for _,W in ROWS:
    assert sum(W)==1

def pieces(W,sw,ss,ts):
    mw,ms,md,m7,m8=W
    def FW(x):
        x=jj(x); c,s=jcos(x),jsin(x)
        return mw*(c+sw*s)/2-jj(c0)*mw*(c+s)
    def GS(x):
        x=jj(x); c,s=jcos(x),jsin(x)
        return ms*(c+ss*s)/2-jj(c0)*ms*(c-s)
    def HD(x):
        x=jj(x)
        return md*(F(1,2)-jj(c0))*(jcos(x)+jsin(x))
    def KD(x):
        x=jj(x); c,s=jcos(x),jsin(x)
        return m7*(c+s)/2-X.support_any(md+m7*s,m7*c-m8)
    def LT(x):
        x=jj(x); c,s=jcos(x),jsin(x)
        return m8*(c+ts*s)/2-X.support_any(ms+m8*c,m8*s)
    # Sum of all selected pair half-widths has the common source-square
    # contribution (sum weights)/2 = 1/2.  W support is constant in its frame.
    const=J(F(1,2))-X.support_any(J(mw),J(-m7))
    return const,FW,GS,HD,KD,LT

# Fixed positive central-force coordinates on each row, so
# c0 (G_Cx+G_Cy) is the exact central rectangular support.
for wr,W in ROWS:
    mw,ms,md,_,_=W
    sw=X.sinR(I(*wr)); cw=X.cosR(I(*wr))
    ss=X.sinR(I(*SR)); cs=X.cosR(I(*SR))
    sd=X.sinR(I(*DR)); cd=X.cosR(I(*DR))
    gx=mw*cw.lo-ms*ss.hi+md*cd.lo
    gy=mw*sw.lo+ms*cs.lo+md*sd.lo
    assert gx>0 and gy>0,(wr,gx,gy)

# Strict w-concavity on each fixed chamber.  On the final chamber the cyclic
# wall w=d is checked separately below.
for wr,W in ROWS:
    sw=-1 if wr[1]<=0 else 1
    _,FW,GS,HD,KD,LT=pieces(W,sw,1,1)
    delta=(max(F(0),DR[0]-wr[1]),DR[1]-wr[0])
    assert X.maxdd(FW,*wr,F(1,400))+X.maxdd(KD,*delta,F(1,400))<0

# The old proof asserted positive-s concavity.  That is false.  What is true
# for every retuned row is the stronger useful fact partial_s Phi < 0.
for wr,W in ROWS:
    for sa,sb in ((-F(1,5),F(0)),(F(0),F(1,5))):
        ss=-1 if sb<=0 else 1
        _,FW,GS,HD,KD,LT=pieces(W,-1 if wr[1]<=0 else 1,ss,1)
        gd=X.drange(GS,sa,sb,F(1,400))
        td=X.drange(LT,DR[0]-sb,DR[1]-sa,F(1,400))
        # d/ds [G(s)+L(d-s)] = G'(s)-L'(d-s).
        assert gd[1]-td[0]<0,(wr,sa,sb,gd,td)

# After w reduction and s -> 1/5, only one-dimensional d edges remain.
best=[]
s0=F(1,5)
for wr,W in ROWS:
    rowbest=F(100)
    fixed=[wr[0],wr[1]] if wr[1]<=F(1,2) else [wr[0]]
    for w0 in fixed:
        sw=-1 if w0<0 else 1
        const,FW,GS,HD,KD,LT=pieces(W,sw,1,1)
        def edge(d):
            return (const+FW(J(I(w0)))+GS(J(I(s0)))+HD(d)
                    +KD(d-J(I(w0)))+LT(d-J(I(s0))))
        rowbest=min(rowbest,X.minval(edge,DR[0],DR[1],F(1,800)))

    # Cyclic wall w=d on the final chamber.
    if wr[1]>F(1,2):
        da,db=wr
        const,FW,GS,HD,KD,LT=pieces(W,1,1,1)
        def wall(d):
            return (const+FW(d)+GS(J(I(s0)))+HD(d)
                    +KD(J(I(0)))+LT(d-J(I(s0))))
        rowbest=min(rowbest,X.minval(wall,da,db,F(1,800)))

    assert rowbest>F(1,100),(wr,rowbest)
    best.append(rowbest)

print("A2.3 Ws/Ds repaired scalar audit: PASS")
print("scalar margins >",*(float(x) for x in best))
