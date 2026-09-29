#!/usr/bin/env python3
"""Exact scalar audit for the full A2.3 hard Ds/Ss table.

The old checker asserted separate concavity in (w,s,d) on every cell.
That is false.  This replacement keeps the same 53 fixed rational stresses
but uses only valid one-dimensional reductions:

* four cells are increasing in w; every other cell is concave in w;
* every cell is concave in s;
* after w,s reduction each d-edge is increasing, decreasing, or concave,
  except two fixed edges in row 15, handled by explicit rational splits.

No adaptive subdivision or multidimensional box replay is used.
"""
from fractions import Fraction as F
import n6_a2_scalar as X

I,J=X.I,X.J
jj,jcos,jsin=X.jj,X.jcos,X.jsin
PI,c0=X.PI,X.c0
DR=(F(1,2),PI.hi/4)

def R(w0,w1,s0,s1,W):
    return (F(w0),F(w1),F(s0),F(s1),tuple(F(x,1000) for x in W))

ROWS=[
 R("-2/3","-3/5","-1/5","-1/10",(373,248,76,168,135)),
 R("-2/3","-19/30","-1/10","-1/20",(428,252,61,126,133)),
 R("-2/3","-19/30","-1/20","0",(390,236,109,141,124)),
 R("-19/30","-3/5","-1/10","-1/20",(403,254,75,134,134)),
 R("-19/30","-3/5","-1/20","0",(415,229,68,153,135)),
 R("-2/3","-3/5","0","1/8",(402,198,117,150,133)),
 R("-2/3","-3/5","1/8","1/4",(436,185,196,110,73)),
 R("-2/3","-3/5","1/4","3/8",(438,328,37,73,124)),
 R("-2/3","-3/5","3/8","1/2",(536,366,38,29,31)),
 R("-3/5","-11/20","-1/5","-1/10",(307,291,59,171,172)),
 R("-3/5","-11/20","-1/10","0",(416,181,123,154,126)),
 R("-3/5","-11/20","0","1/8",(445,244,45,123,143)),
 R("-3/5","-11/20","1/8","1/4",(375,177,180,151,117)),
 R("-3/5","-11/20","1/4","3/8",(367,256,141,129,107)),
 R("-3/5","-11/20","3/8","1/2",(414,293,125,98,70)),
 R("-11/20","-1/2","-1/5","-1/10",(437,194,99,149,121)),
 R("-11/20","-21/40","-1/10","-1/20",(396,232,70,171,131)),
 R("-11/20","-21/40","-1/20","0",(434,212,45,163,146)),
 R("-21/40","-1/2","-1/10","-1/20",(354,238,101,161,146)),
 R("-21/40","-1/2","-1/20","0",(389,191,108,176,136)),
 R("-11/20","-1/2","0","1/8",(465,229,55,129,122)),
 R("-11/20","-1/2","1/8","1/4",(347,265,93,154,141)),
 R("-11/20","-1/2","1/4","3/8",(448,226,108,117,101)),
 R("-11/20","-1/2","3/8","1/2",(484,261,80,82,93)),
 R("-1/2","-9/20","-1/5","-1/10",(177,331,28,237,227)),
 R("-1/2","-9/20","-1/10","0",(405,201,58,181,155)),
 R("-1/2","-39/80","0","1/32",(471,211,58,138,122)),
 R("-1/2","-39/80","1/32","1/16",(475,178,115,131,101)),
 R("-39/80","-19/40","0","1/32",(417,189,125,151,118)),
 R("-39/80","-19/40","1/32","1/16",(403,198,103,162,134)),
 R("-1/2","-19/40","1/16","1/8",(368,200,122,181,129)),
 R("-19/40","-9/20","0","1/16",(376,230,83,163,148)),
 R("-19/40","-9/20","1/16","1/8",(395,223,94,160,128)),
 R("-1/2","-9/20","1/8","1/4",(332,238,145,161,124)),
 R("-1/2","-9/20","1/4","3/8",(425,218,129,134,94)),
 R("-1/2","-9/20","3/8","1/2",(260,321,153,149,117)),
 R("-9/20","-2/5","-1/5","-1/10",(124,364,14,255,243)),
 R("-9/20","-2/5","-1/10","0",(339,245,85,184,147)),
 R("-9/20","-17/40","0","1/16",(341,202,124,187,146)),
 R("-9/20","-17/40","1/16","1/8",(202,241,168,226,163)),
 R("-17/40","-2/5","0","1/16",(291,237,98,209,165)),
 R("-17/40","-2/5","1/16","1/8",(209,248,165,214,164)),
 R("-9/20","-2/5","1/8","1/4",(283,259,125,183,150)),
 R("-9/20","-2/5","1/4","3/8",(226,271,162,186,155)),
 R("-9/20","-2/5","3/8","1/2",(183,351,160,169,137)),
 R("-2/5","-3/10","-1/5","0",(156,269,148,250,177)),
 R("-2/5","-3/10","0","1/5",(145,273,186,234,162)),
 R("-2/5","-3/10","1/5","7/20",(199,321,149,178,153)),
 R("-2/5","-3/10","7/20","1/2",(119,339,209,187,146)),
 R("-3/10","-1/5","-1/5","0",(182,227,178,247,166)),
 R("-3/10","-1/5","0","1/5",(177,262,168,232,161)),
 R("-3/10","-1/5","1/5","7/20",(96,237,293,244,130)),
 R("-3/10","-1/5","7/20","1/2",(134,315,215,199,137)),
]
for *_,W in ROWS: assert sum(W)==1

# These four cells have small positive w-curvature but a uniformly positive
# w-derivative, so they reduce to their left edge.
W_MONO={36:F(3,50),45:F(1,25),46:F(1,25),48:F(3,100)}

def pieces(W,ss):
    mw,ms,md,m7,m8=W
    def FW(w):
        w=jj(w);c,s=jcos(w),jsin(w)
        return mw*(c-s)/2-jj(c0)*mw*(c+s)
    def GS(s):
        s=jj(s);c,t=jcos(s),jsin(s)
        return ms*(c+ss*t)/2-jj(c0)*ms*(c-t)
    def HD(d):
        d=jj(d);return md*(F(1,2)-jj(c0))*(jcos(d)+jsin(d))
    def KD(z):
        z=jj(z);c,s=jcos(z),jsin(z)
        return m7*(c+s)/2-X.support_any(mw+m7*s,-m7*c)
    def LT(t):
        t=jj(t);c,s=jcos(t),jsin(t)
        return m8*(c+s)/2-X.support_any(md+m8*c,m7-m8*s)
    const=J(F(1,2))-X.support_any(J(ms),J(m8))
    return const,FW,GS,HD,KD,LT

def edge_parts(idx,w0,s0):
    wa,wb,sa,sb,W=ROWS[idx]
    ss=-1 if sb<=0 else 1
    const,FW,GS,HD,KD,LT=pieces(W,ss)
    def edge(d):
        return (const+FW(J(I(w0)))+GS(J(I(s0)))+HD(d)
                +KD(d-J(I(w0)))+LT(d-J(I(s0))))
    return edge

counts={"inc":0,"dec":0,"conc":0,"special":0}
best=F(100)

for idx,(wa,wb,sa,sb,W) in enumerate(ROWS):
    ss=-1 if sb<=0 else 1
    const,FW,GS,HD,KD,LT=pieces(W,ss)

    # Chosen stresses keep the central force in the positive quadrant.
    sw=X.sinR(I(wa,wb));cw=X.cosR(I(wa,wb))
    sx=X.sinR(I(sa,sb));cs=X.cosR(I(sa,sb))
    sd=X.sinR(I(*DR));cd=X.cosR(I(*DR))
    mw,ms,md,_,_=W
    assert mw*cw.lo-ms*sx.hi+md*cd.lo>0
    assert mw*sw.lo+ms*cs.lo+md*sd.lo>0

    de=(DR[0]-wb,DR[1]-wa)
    if idx in W_MONO:
        fd=X.drange(FW,wa,wb,F(1,400))
        kd=X.drange(KD,*de,F(1,400))
        assert fd[0]-kd[1] > W_MONO[idx]
        wends=(wa,)
    else:
        assert X.maxdd(FW,wa,wb,F(1,400))+X.maxdd(KD,*de,F(1,400))<0
        wends=(wa,wb)

    tr=(DR[0]-sb,DR[1]-sa)
    assert X.maxdd(GS,sa,sb,F(1,400))+X.maxdd(LT,*tr,F(1,400))<0

    for w0 in wends:
      for s0 in (sa,sb):
        edge=edge_parts(idx,w0,s0)

        # Two support-switch-sensitive edges in row 15 need a fixed split.
        if idx==15 and s0==F(-1,5) and w0==F(-11,20):
            cuts=(F(1,2),F(3,5),F(7,10),F(3,4),F(77,100),DR[1])
            for a,b in zip(cuts,cuts[1:]):
                dr=X.drange(edge,a,b,F(1,1000))
                assert dr[0]>0
            candidates=cuts
            counts["special"]+=1
        elif idx==15 and s0==F(-1,5) and w0==F(-1,2):
            cuts=(F(1,2),F(3,5),F(7,10),DR[1])
            assert X.maxdd(edge,cuts[0],cuts[1],F(1,500))<0
            assert X.maxdd(edge,cuts[1],cuts[2],F(1,500))<0
            dr=X.drange(edge,cuts[2],cuts[3],F(1,500))
            assert dr[1]<0
            candidates=cuts
            counts["special"]+=1
        else:
            dr=X.drange(edge,*DR,F(1,400))
            dd=X.maxdd(edge,*DR,F(1,400))
            if dr[0]>0:
                candidates=(DR[0],); counts["inc"]+=1
            elif dr[1]<0:
                candidates=(DR[1],); counts["dec"]+=1
            else:
                assert dd<0,(idx,w0,s0,dr,dd)
                candidates=DR; counts["conc"]+=1

        for d0 in candidates:
            best=min(best,edge(J(I(d0))).v.lo)

assert best>F(1,10000),best
print("A2.3 full hard Ds/Ss table exact audit: PASS")
print("edge reductions",counts)
print("weakest terminal margin >",float(best))
