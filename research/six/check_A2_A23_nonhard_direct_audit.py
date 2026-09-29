#!/usr/bin/env python3
"""Independent exact direct-support re-audit of the non-hard A2.3 rows.

This is an audit, not a logical premise of HAND_PROOF.md. It uses directed
52-bit fixed-point interval arithmetic, rational Taylor sine/cosine bounds,
and the exact cap/vertex disk support. It covers every non-hard A2.3
classification row not already handled by a dedicated repaired checker.

The repaired Ws/Ds middle row, first Ds/Dp and Ds/Ds rows, and the hard
53-cell Ds/Ss table have their own exact checkers and are intentionally not
duplicated here.
"""
from fractions import Fraction as F
import argparse
import n6_a2_fixed as X

I,J=X.I,X.J
jj,jcos,jsin=X.jj,X.jcos,X.jsin
PILO=F(X.PI.lo,X.S); PIHI=F(X.PI.hi,X.S)
DR=(F(1,2),PIHI/4); FULL=(-F(2,3),PIHI/4)
Q=lambda t:tuple(F(x,1000) for x in t)

def _sq(a):
    aa=abs(a); return aa*aa
def _support_ordered(U,V,norm):
    cap=X.rho*U; vert=X.R*norm-(U+V)/2; sw=2*X.R*V-norm
    if sw.hi<=0:return cap
    if sw.lo>=0:return vert
    return X.hullI(cap,vert)
def support_val(x,y):
    x,y=jj(x),jj(y); ax,ay=abs(x.v),abs(y.v)
    norm=X.sqrtI(_sq(x.v)+_sq(y.v))
    if ax.lo>=ay.hi:z=_support_ordered(ax,ay,norm)
    elif ay.lo>=ax.hi:z=_support_ordered(ay,ax,norm)
    else:z=X.hullI(_support_ordered(ax,ay,norm),_support_ordered(ay,ax,norm))
    return J(z)
X.support_any=support_val

def signs(lo,hi):
    if hi<=0:return (-1,)
    if lo>=0:return (1,)
    return (-1,1)

def base(W,sw,ss):
    mw,ms,md,m7,m8=W
    def FW(x):x=jj(x);c,s=jcos(x),jsin(x);return mw*(c+sw*s)/2-J(X.c0)*mw*(c+s)
    def GS(x):x=jj(x);c,s=jcos(x),jsin(x);return ms*(c+ss*s)/2-J(X.c0)*ms*(c-s)
    def HD(x):x=jj(x);return md*(F(1,2)-J(X.c0))*(jcos(x)+jsin(x))
    return FW,GS,HD

def p_wsdp(W,sw,ss,ts,extra):
    mw,ms,md,m7,m8=W;FW,GS,HD=base(W,sw,ss)
    def KD(x):x=jj(x);c,s=jcos(x),jsin(x);return m7*(c+s)/2-X.support_any(md+m8+m7*s,m7*c)
    def LT(x):x=jj(x);c,s=jcos(x),jsin(x);return m8*(c+ts*s)/2-X.support_any(ms-m8*s,m8*c)
    return J(F(1,2))-X.support_any(J(mw),J(-m7)),FW,GS,HD,KD,LT

def p_dsdp(W,sw,ss,ts,extra):
    mw,ms,md,m7,m8=W;FW,GS,HD=base(W,sw,ss)
    def KD(x):x=jj(x);c,s=jcos(x),jsin(x);return m7*(c+s)/2-X.support_any(mw+m7*s,-m7*c)
    def LT(x):x=jj(x);c,s=jcos(x),jsin(x);return m8*(c+ts*s)/2-X.support_any(ms-m8*s,m8*c)
    return J(F(1,2))-X.support_any(J(md+m8),J(m7)),FW,GS,HD,KD,LT

def p_dsds(W,sw,ss,ts,extra):
    mw,ms,md,m7,m8=W;FW,GS,HD=base(W,sw,ss)
    def KD(x):x=jj(x);c,s=jcos(x),jsin(x);return m7*(c+s)/2-X.support_any(mw+m7*s,-m7*c)
    def LT(x):x=jj(x);c,s=jcos(x),jsin(x);return m8*(c+ts*s)/2-X.support_any(ms+m8*c,m8*s)
    return J(F(1,2))-X.support_any(J(md),J(m7-m8)),FW,GS,HD,KD,LT

def p_dssp(W,sw,ss,ts,orient):
    mw,ms,md,m7,m8=W;FW,GS,HD=base(W,sw,ss)
    def KD(x):x=jj(x);c,s=jcos(x),jsin(x);return m7*(c+s)/2-X.support_any(mw+m7*s,-m7*c)
    def LT(x):x=jj(x);c,s=jcos(x),jsin(x);return m8*(c+ts*s)/2-X.support_any(md-orient*m8*s,m7-orient*m8*c)
    return J(F(1,2))-J(X.rho)*abs(ms+orient*m8),FW,GS,HD,KD,LT

def p_dsss(W,sw,ss,ts,extra):
    mw,ms,md,m7,m8=W;FW,GS,HD=base(W,sw,ss)
    def KD(x):x=jj(x);c,s=jcos(x),jsin(x);return m7*(c+s)/2-X.support_any(mw+m7*s,-m7*c)
    def LT(x):x=jj(x);c,s=jcos(x),jsin(x);return m8*(c+ts*s)/2-X.support_any(md+m8*c,m7-m8*s)
    return J(F(1,2))-X.support_any(J(ms),J(m8)),FW,GS,HD,KD,LT

def p_wsds(W,sw,ss,ts,extra):
    mw,ms,md,m7,m8=W;FW,GS,HD=base(W,sw,ss)
    def KD(x):x=jj(x);c,s=jcos(x),jsin(x);return m7*(c+s)/2-X.support_any(md+m7*s,m7*c-m8)
    def LT(x):x=jj(x);c,s=jcos(x),jsin(x);return m8*(c+ts*s)/2-X.support_any(ms+m8*c,m8*s)
    return J(F(1,2))-X.support_any(J(mw),J(-m7)),FW,GS,HD,KD,LT

def gap_lower(builder,W,extra,w,s,d):
    wi,si,di=J(I(*w)),J(I(*s)),J(I(*d));tr=(d[0]-s[1],d[1]-s[0]);best=None
    for sw in signs(*w):
      for ss in signs(*s):
       for ts in signs(*tr):
        C,FW,GS,HD,KD,LT=builder(W,sw,ss,ts,extra)
        z=C+FW(wi)+GS(si)+HD(di)+KD(di-wi)+LT(di-si)
        lo=F(z.v.lo,X.S);best=lo if best is None else min(best,lo)
    return best

def audit_row(name,sr,wr,W,extra,builder,maxdepth=34,maxnodes=700000):
    q=[(wr,sr,DR,0)];vis=0;leaf=F(100);maxd=0
    while q:
        w,s,d,dep=q.pop();vis+=1;maxd=max(maxd,dep)
        if vis>maxnodes:raise AssertionError((name,'node limit',vis))
        if w[0]>d[1]:continue
        lo=gap_lower(builder,W,extra,w,s,d)
        if lo>0:leaf=min(leaf,lo);continue
        if dep>=maxdepth:raise AssertionError((name,'depth',w,s,d,lo))
        widths=[float(w[1]-w[0])/1.5,float(s[1]-s[0])/1.6,float(d[1]-d[0])/.29]
        k=max(range(3),key=widths.__getitem__);arr=[w,s,d];a,b=arr[k];m=(a+b)/2
        aa=list(arr);bb=list(arr);aa[k]=(a,m);bb[k]=(m,b)
        q.extend([(aa[0],aa[1],aa[2],dep+1),(bb[0],bb[1],bb[2],dep+1)])
    print(name,'PASS nodes',vis,'depth',maxd,'leaf margin >',float(leaf))

FAMILIES={}
FAMILIES['wsdp']=(p_wsdp,[
 ((-PIHI/4,-F(1,5)),FULL,Q((108,508,10,51,323)),None),
 ((-F(1,5),F(1,5)),FULL,Q((259,379,15,135,212)),None),
 ((F(1,5),F(1,2)),FULL,Q((295,364,54,164,123)),None),
 ((F(1,2),PIHI/4),FULL,Q((285,383,123,143,66)),None)])
FAMILIES['dssp']=(p_dssp,[
 ((-PIHI/4,-F(1,4)),FULL,Q((38,434,63,29,436)),-1),
 ((-F(27,100),F(1,5)),FULL,Q((88,65,233,278,336)),1),
 ((F(1,5),F(1,2)),FULL,Q((343,206,96,190,165)),1),
 ((F(1,2),PIHI/4),FULL,Q((278,367,121,145,89)),1)])
FAMILIES['dsdp']=(p_dsdp,[
 ((-F(1,5),F(1,5)),FULL,Q((237,410,30,116,207)),None),
 ((F(1,5),F(1,2)),FULL,Q((204,443,106,116,131)),None),
 ((F(1,2),PIHI/4),FULL,Q((231,392,185,116,76)),None)])
FAMILIES['dsds']=(p_dsds,[
 ((-F(1,5),F(1,5)),FULL,Q((89,92,59,363,397)),None),
 ((F(1,5),F(1,2)),FULL,Q((294,265,25,201,215)),None),
 ((F(1,2),PIHI/4),FULL,Q((294,323,61,164,158)),None)])
FAMILIES['wsds']=(p_wsds,[
 ((-PIHI/4,-F(1,5)),FULL,Q((303,157,191,163,186)),None),
 ((F(1,5),F(1,2)),(-F(2,3),-F(2,5)),Q((391,246,77,146,140)),None),
 ((F(1,5),F(1,2)),(-F(2,5),-F(1,5)),Q((350,253,32,192,173)),None),
 ((F(1,5),F(1,2)),(-F(1,5),F(0)),Q((324,228,23,222,203)),None),
 ((F(1,5),F(1,2)),(F(0),F(1,2)),Q((315,306,9,184,186)),None),
 ((F(1,5),F(1,2)),(F(1,2),PIHI/4),Q((344,32,33,306,285)),None),
 ((F(1,2),PIHI/4),(-F(2,3),F(0)),Q((285,366,55,167,127)),None),
 ((F(1,2),PIHI/4),(F(0),F(1,2)),Q((248,354,63,180,155)),None),
 ((F(1,2),PIHI/4),(F(1,2),PIHI/4),Q((400,110,33,257,200)),None)])
WC=[(-F(2,3),-F(1,5)),(-F(1,5),F(1,5)),(F(1,5),F(1,2)),(F(1,2),PIHI/4)]
SC=[(-PIHI/4,-F(1,5)),(-F(1,5),F(1,5)),(F(1,5),F(1,2)),(F(1,2),PIHI/4)]
TAB={(0,0):(319,266,57,182,176),(0,3):(240,344,167,130,119),(1,0):(135,353,5,257,250),(1,1):(139,169,318,262,112),(1,2):(116,185,354,253,92),(1,3):(124,361,232,184,99),(2,0):(258,283,4,235,220),(2,1):(254,105,319,249,73),(2,2):(242,152,302,233,71),(2,3):(195,182,348,222,53),(3,0):(305,250,4,233,208),(3,1):(326,115,234,239,86),(3,2):(298,139,257,230,76),(3,3):(321,22,400,250,7)}
FAMILIES['dsss']=(p_dsss,[(SC[j],WC[i],Q(W),None) for (i,j),W in TAB.items()])

SIGNED=[
 ('p1',(-F(2,3),F(0)),(-F(27,100),F(1,5)),1,1,-1,Q((322,219,0,230,229))),
 ('p2',(F(0),F(1,2)),(-F(27,100),F(1,5)),1,-1,1,Q((512,55,0,225,208))),
 ('p3',(F(1,2),F(13,20)),(-F(27,100),F(1,5)),1,-1,1,Q((531,33,0,266,170))),
 ('p4',(-F(2,3),F(0)),(F(1,5),F(1,2)),1,1,-1,Q((309,385,0,155,151))),
 ('p5',(F(0),F(1,2)),(F(1,5),F(1,2)),1,1,1,Q((427,99,0,270,204))),
 ('p6',(F(1,2),PIHI/4),(F(1,5),F(1,2)),1,-1,1,Q((452,59,0,278,211))),
 ('p7a',(-F(2,3),-F(2,5)),(F(1,2),PIHI/4),1,1,-1,Q((389,367,0,142,102))),
 ('p7b',(-F(2,5),-F(1,5)),(F(1,2),PIHI/4),1,1,1,Q((387,366,0,185,62))),
 ('p7c',(-F(1,5),F(0)),(F(1,2),PIHI/4),1,1,1,Q((322,403,0,181,94))),
 ('p8',(F(0),F(1,2)),(F(1,2),PIHI/4),1,1,1,Q((324,392,0,174,110))),
 ('p9',(F(1,2),PIHI/4),(F(1,2),PIHI/4),1,1,1,Q((485,44,0,255,216)))]
SIMPLE=[('neg',(-F(2,3),PIHI/4),(-PIHI/4,-F(1,4)),-1,Q((56,453,41,0,450))),('pos',(F(13,20),PIHI/4),(-F(27,100),F(1,5)),1,Q((138,59,530,0,273)))]

def signed_lower(row,w,s,d):
    name,wr,sr,o,sg,tau,W=row;mw,ms,md,m7,m8=W;wi,si,di=J(I(*w)),J(I(*s)),J(I(*d));tr=(d[0]-s[1],d[1]-s[0]);vals=[]
    C=J(F(1,2))-X.support_any(J(mw),J(-m7))-J(X.rho)*abs(ms+o*m8)
    for sw in signs(*w):
      for ss in signs(*s):
       for ts in signs(*tr):
        def FW(x):x=jj(x);c,t=jcos(x),jsin(x);return mw*(c+sw*t)/2-J(X.c0)*mw*(c+t)
        def GS(x):x=jj(x);c,t=jcos(x),jsin(x);return ms*(c+ss*t)/2-J(X.c0)*ms*(c-t)
        def KD(x):x=jj(x);c,t=jcos(x),jsin(x);return m7*((1+sg)*t+(1+tau)*c)/2
        def LT(x):x=jj(x);c,t=jcos(x),jsin(x);return m8*(c+ts*t-o*(sg*t+tau*c))/2
        z=C+FW(wi)+GS(si)+KD(di-wi)+LT(di-si)-J(X.R)*X.jsqrt(J(m7*m7+m8*m8)-2*o*m7*m8*jcos(si-wi))
        vals.append(F(z.v.lo,X.S))
    return min(vals)

def simple_lower(row,w,s,d):
    name,wr,sr,o,W=row;mw,ms,md,m7,m8=W;wi,si,di=J(I(*w)),J(I(*s)),J(I(*d));vals=[];C=J(F(1,2))-J(X.rho)*mw-J(X.rho)*abs(ms+o*m8)
    for sw in signs(*w):
      for ss in signs(*s):
        def FW(x):x=jj(x);c,t=jcos(x),jsin(x);return mw*(c+sw*t)/2-J(X.c0)*mw*(c+t)
        def GS(x):x=jj(x);c,t=jcos(x),jsin(x);return ms*(c+ss*t)/2-J(X.c0)*ms*(c-t)
        def HD(x):x=jj(x);return md*(F(1,2)-J(X.c0))*(jcos(x)+jsin(x))
        t=di-si;c,st=jcos(t),jsin(t);LT=m8*(c+X.jabs(st))/2-X.support_any(md-o*m8*st,-o*m8*c)
        vals.append(F((C+FW(wi)+GS(si)+HD(di)+LT).v.lo,X.S))
    return min(vals)

def audit_custom(name,wr,sr,lower,row,maxdepth=34,maxnodes=700000):
    q=[(wr,sr,DR,0)];vis=0;leaf=F(100);maxd=0
    while q:
        w,s,d,dep=q.pop();vis+=1;maxd=max(maxd,dep)
        if vis>maxnodes:raise AssertionError((name,'node limit'))
        if w[0]>d[1]:continue
        lo=lower(row,w,s,d)
        if lo>0:leaf=min(leaf,lo);continue
        if dep>=maxdepth:raise AssertionError((name,'depth',w,s,d,lo))
        widths=[float(w[1]-w[0])/1.5,float(s[1]-s[0])/1.6,float(d[1]-d[0])/.29];k=max(range(3),key=widths.__getitem__);arr=[w,s,d];a,b=arr[k];m=(a+b)/2;aa=list(arr);bb=list(arr);aa[k]=(a,m);bb[k]=(m,b);q.extend([(aa[0],aa[1],aa[2],dep+1),(bb[0],bb[1],bb[2],dep+1)])
    print(name,'PASS nodes',vis,'depth',maxd,'leaf margin >',float(leaf))

def run_family(fam,index=None):
    if fam in FAMILIES:
        builder,rows=FAMILIES[fam];ids=range(len(rows)) if index is None else [index]
        for i in ids:
            sr,wr,W,e=rows[i];audit_row(f'{fam}{i}',sr,wr,W,e,builder)
    elif fam=='wssp':
        ids=range(len(SIGNED)) if index is None else [index]
        for i in ids:
            row=SIGNED[i];audit_custom('wssp'+str(i),row[1],row[2],signed_lower,row)
    elif fam=='wssp_simple':
        ids=range(len(SIMPLE)) if index is None else [index]
        for i in ids:
            row=SIMPLE[i];audit_custom('wssp_simple'+str(i),row[1],row[2],simple_lower,row)
    else:raise KeyError(fam)

if __name__=='__main__':
    choices=list(FAMILIES)+['wssp','wssp_simple','all']
    ap=argparse.ArgumentParser();ap.add_argument('family',choices=choices);ap.add_argument('index',nargs='?',type=int);a=ap.parse_args()
    if a.family=='all':
        for f in choices[:-1]:run_family(f)
    else:run_family(a.family,a.index)
