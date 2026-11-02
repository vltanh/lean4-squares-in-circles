#!/usr/bin/env python3
"""Independent exact directed-integer replay of the weak-middle table.

Only the finite preorder split/leaf tags are read from discovery. All roots,
expressions and outward interval arithmetic are reconstructed here. No NumPy,
optimizer, floating arithmetic, generator import, Lean or external solver.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,time

SCALE=1<<80
def ceildiv(n,d):return -((-n)//d)
def lower_fraction(x):x=F(x);return x.numerator*SCALE//x.denominator
def upper_fraction(x):x=F(x);return ceildiv(x.numerator*SCALE,x.denominator)

class I:
    __slots__=('lo','hi')
    def __init__(self,a,b=None,raw=False):
        if raw:self.lo=a;self.hi=a if b is None else b
        else:self.lo=lower_fraction(a);self.hi=upper_fraction(a if b is None else b)
        assert self.lo<=self.hi
    def __add__(a,b):b=iv(b);return I(a.lo+b.lo,a.hi+b.hi,True)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo,True)
    def __sub__(a,b):return a+-iv(b)
    def __rsub__(a,b):return iv(b)+-a
    def __mul__(a,b):
        b=iv(b);p=(a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi)
        return I(min(p)//SCALE,ceildiv(max(p),SCALE),True)
    __rmul__=__mul__
    def __truediv__(a,b):
        b=iv(b);assert b.lo>0
        return a*I(SCALE*SCALE//b.hi,ceildiv(SCALE*SCALE,b.lo),True)
    def __rtruediv__(a,b):return iv(b)/a
    def sq(a):
        lo=0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi)
        hi=max(a.lo*a.lo,a.hi*a.hi)
        return I(lo//SCALE,ceildiv(hi,SCALE),True)
    def ab(a):return I(max(0,a.lo,-a.hi),max(abs(a.lo),abs(a.hi)),True)
    def rt(a):
        assert a.hi>=0
        low=max(0,a.lo)*SCALE;high=a.hi*SCALE
        l=isqrt(low);u=isqrt(high)
        if u*u<high:u+=1
        assert l*l<=low and u*u>=high
        return I(l,u,True)
def iv(x):return x if isinstance(x,I) else I(x)
def imin(*v):v=[iv(x) for x in v];return I(min(x.lo for x in v),min(x.hi for x in v),True)
def imax(*v):v=[iv(x) for x in v];return I(max(x.lo for x in v),max(x.hi for x in v),True)

def orient(t):
    def point(z):
        zz=I(z,raw=True);a=1/(1+zz.sq()).rt();b=zz*a
        return a,b,(a+b)/2,(a-b)/2
    al,bl,hl,kl=point(t.lo);au,bu,hu,ku=point(t.hi)
    return I(au.lo,al.hi,True),I(bl.lo,bu.hi,True),I(hl.lo,hu.hi,True),I(ku.lo,kl.hi,True)
def mainorient(h):
    def point(z):
        zz=I(z,raw=True);k=(F(1,2)-zz.sq()).rt();g=1/(4*zz)
        return zz+k,zz-k,g,zz+g-1
    al,bl,gl,el=point(h.lo);au,bu,gu,eu=point(h.hi)
    return I(au.lo,al.hi,True),I(bl.lo,bu.hi,True),I(gu.lo,gl.hi,True),I(el.lo,eu.hi,True)

def circle_arc_upper(alpha,beta,lo,hi):
    """Exact upper bound of alpha*z+beta*sqrt(Q-z*z) on [lo,hi]."""
    q=F(1105,256);assert beta>0 and 0<=lo<=hi
    if lo*lo>q:return upper_fraction(10**20)
    norm2=alpha*alpha+beta*beta
    if alpha<=0 or q*alpha*alpha<=norm2*lo*lo:
        return (I(alpha*lo)+beta*I(q-lo*lo).rt()).hi
    if hi*hi<q and q*alpha*alpha>=norm2*hi*hi:
        return (I(alpha*hi)+beta*I(q-hi*hi).rt()).hi
    return I(q*norm2).rt().hi

def weighted_reserve(box):
    tp,tr,x,X,hm=[I(*p) for p in box]
    ap,bp,p,kp=orient(tp);ar,br,r,kr=orient(tr)
    am,bm,gm,eta=mainorient(hm)
    delta=-x.ab()-F(1,60);ra=(F(1,2)+delta*bp)/ap;num=F(1,2)+delta*ap
    reach=I(min(p.lo,ra.lo,num.lo*SCALE//bp.hi if bp.hi>0 else 10**100),min(p.hi,ra.hi),True)
    km=(F(1,2)-hm.sq()).rt()
    smp=imax(1+(hm-p).ab(),F(1,2)+imax(km*ap+hm*bp,hm*ap-km*bp))
    dmp=F(61,60)-hm+x.ab()
    nums=[imax(F(1,10),smp-am*dmp),imax(F(1,10),smp-bm*dmp),imax(F(1,10),smp-ap*dmp),imax(F(1,10),smp-bp*dmp)]
    dens=[bm,am,bp,ap]
    flo=min(n.lo*SCALE//v.hi for n,v in zip(nums,dens) if v.hi>0)
    physical=I(flo,min((nums[1]/am).hi,(nums[3]/ap).hi),True)
    ylo=imax(gm+reach,(smp.sq()-dmp.sq()).rt(),physical)-F(2,3)*hm+imax(0,imin((hm-F(1,2))/6,(F(27,50)-hm)/3))+F(1,400)
    support=imax(1+(p-r).ab(),F(1,2)+imax(kp*ar+p*br,p*ar-kp*br))
    lam=F(9,10);kap=F(27,92);C=F(29927,30000)+F(157,184)+kap*F(p.lo,SCALE)+F(eta.lo,SCALE)
    branches=[(F(0),F(r.lo,SCALE)),(F(tr.lo,SCALE),F(SCALE,2*ar.hi)),(F(tr.hi,SCALE),F(SCALE,2*ar.hi))]
    n2=F(1,2)+(X-F(503,480))*ar
    if br.hi>0:branches.append((F(0),F(n2.lo,br.hi)))
    corners=[[(F(kr.lo,SCALE),F(r.lo,SCALE)),(F(r.lo,SCALE),-F(kr.hi,SCALE))],
             [(F(r.lo,SCALE),F(kr.lo,SCALE)),(-F(kr.hi,SCALE),F(r.lo,SCALE))]]
    bounds=[]
    for ai,bi in [(ap,bp),(ar,br)]:
        beta=F(bi.hi,SCALE)+lam;GX=[]
        for slope,constant in branches:
            alpha=F(ai.hi,SCALE)-lam*slope;chir=[]
            for chirality in corners:
                caps=[]
                for c,offset in chirality:
                    term=circle_arc_upper(alpha,beta,F(X.lo,SCALE)+c,F(X.hi,SCALE)+c)
                    term+=upper_fraction(-alpha*c-beta*offset-lam*constant+lam*slope*F(503,480))
                    caps.append(term)
                chir.append(min(caps))
            GX.append(max(chir))
        gx=[]
        for a in [F(ai.lo,SCALE),F(ai.hi,SCALE)]:
            alpha=a/kap
            term=circle_arc_upper(alpha,lam,C-kap*F(x.hi,SCALE),C-kap*F(x.lo,SCALE))
            term+=upper_fraction(-alpha*C-lam);gx.append(term)
        bounds.append(max(GX)+max(gx)-(bi*ylo).lo-support.lo)
    return -max(bounds)

def reserve(box,code):
    if code==13:return weighted_reserve(box)
    tp,tr,x,X,hm=[I(*p) for p in box]
    ap,bp,p,kp=orient(tp);ar,br,r,kr=orient(tr)
    am,bm,gm,eta=mainorient(hm);D=X-x;W=1+r-p-D
    if code==0:return -(x-p+F(451,810)-F(92,27)*eta).hi
    if code==1:return -(r+F(451,810)-X-F(92,27)*eta).hi
    if code==2:return -W.hi
    if code==3:return -(2*D.sq()-(1+(p-r).ab()).sq()).hi
    A=imax(F(59,60),F(157,184)+F(27,92)*(p-x))+eta
    if code==4:return A.lo-upper_fraction(F(61,60))
    if code==9:return -(F(27,92)*W-eta).hi
    if code==10:return -(F(1,30)-eta).hi
    rad=F(1105,256)-(A+F(29927,30000)).sq()
    if code==11:return -rad.hi
    assert code in (5,6,7,8,12)
    if code!=6:
        delta=-x.ab()-F(1,60);ra=(F(1,2)+delta*bp)/ap;num=F(1,2)+delta*ap
        assert num.lo>0
        reach_lo=min(p.lo,ra.lo,(num.lo*SCALE//bp.hi) if bp.hi>0 else 10**100)
        reach=I(reach_lo,min(p.hi,ra.hi),True)
        km=(F(1,2)-hm.sq()).rt()
        smp=imax(1+(hm-p).ab(),F(1,2)+imax(km*ap+hm*bp,hm*ap-km*bp))
        dmp=F(61,60)-hm+x.ab()
        nums=[imax(F(1,10),smp-am*dmp),imax(F(1,10),smp-bm*dmp),imax(F(1,10),smp-ap*dmp),imax(F(1,10),smp-bp*dmp)]
        dens=[bm,am,bp,ap]
        physical_lo=min(num.lo*SCALE//den.hi for num,den in zip(nums,dens) if den.hi>0)
        physical=I(physical_lo,min((nums[1]/am).hi,(nums[3]/ap).hi),True)
        ylo=imax(gm+reach,(smp.sq()-dmp.sq()).rt(),physical)-F(2,3)*hm+imax(0,imin((hm-F(1,2))/6,(F(27,50)-hm)/3))+F(1,400)
        if code==5:return -(p+F(1,10)-ylo).hi
    U=imax(imin((F(1105,256)-(X+kr).sq()).rt()-r,kr+(F(1105,256)-(X+r).sq()).rt()),
           imin((F(1105,256)-(X+r).sq()).rt()-kr,(F(1105,256)-(X-kr).sq()).rt()-r))
    if code==6:
        ca=imax(F(4421,12000)+F(32,9)*eta,1-rad.rt())
        dr=X-F(503,480);rra=(F(1,2)+dr*br)/ar;rnum=F(1,2)+dr*ar
        assert rnum.lo>0
        rlo=min(r.lo,rra.lo,(rnum.lo*SCALE//br.hi) if br.hi>0 else 10**100)
        return ca.lo+rlo-U.hi
    E=U-ylo
    if code==7:return -E.hi
    supp=imax(1+(p-r).ab(),F(1,2)+imax(kp*ar+p*br,p*ar-kp*br))
    Ecap=imin(E,D)
    if code==12:return -(D.sq()+imax(Ecap,0).sq()-supp.sq()).hi
    return -(imax(ap*D+bp*Ecap,ar*D+br*Ecap)-supp).hi

ROOT=((F(0),F(1)),(F(0),F(1)),(F(-23,405),F(23,60)),(F(23,30),F(13,12)),(F(1,2),F(13,20)))

def main():
    ap=argparse.ArgumentParser();base=Path(__file__).parent
    ap.add_argument('--certificate',type=Path,default=base/'weak_middle_below_side_fast_balanced_candidate.json')
    ap.add_argument('--report',type=Path,default=base/'weak_middle_below_side_fast_balanced_exact_replay_report.json')
    ap.add_argument('--progress',action='store_true')
    args=ap.parse_args();start=time.monotonic();raw=args.certificate.read_bytes();data=json.loads(raw)
    events=data['events'];stack=[(ROOT,0)];counts=Counter();leaves=0;depth=0;minimum=None
    for idx,tag in enumerate(events):
        assert stack,('trailing events',idx)
        assert isinstance(tag,int),('noninteger tag',idx)
        box,d=stack.pop();depth=max(depth,d)
        if tag>=0:
            assert tag<5,('invalid split',idx,tag)
            mid=(box[tag][0]+box[tag][1])/2;assert box[tag][0]<mid<box[tag][1]
            left=list(box);right=list(box);left[tag]=(box[tag][0],mid);right[tag]=(mid,box[tag][1])
            stack.append((tuple(right),d+1));stack.append((tuple(left),d+1))
        else:
            code=-tag-1;assert 0<=code<14
            r=reserve(box,code);assert r>0,('false leaf',idx,code,str(F(r,SCALE)),box)
            counts[code]+=1;leaves+=1;minimum=r if minimum is None else min(minimum,r)
            if args.progress and leaves%25000==0:print(json.dumps({'exact_leaves_checked':leaves,'tree_nodes_read':idx+1,'seconds':time.monotonic()-start}),flush=True)
    assert not stack,('incomplete tree',len(stack))
    assert len(events)==2*leaves-1
    report={'status':'EXACT_REPLAY_PASSED','scope':'010/01 low-floor excludes below-main extras on both sides, conditional on exact side-height bump-plus1/400 envelope; full mask still requires central-extra argument',
            'nodes':len(events),'leaves':leaves,'max_depth':depth,'leaf_rules':dict(sorted(counts.items())),
            'root':[[str(a),str(b)] for a,b in ROOT],'scale':SCALE,
            'minimum_exact_reserve':str(F(minimum,SCALE)),'certificate_sha256':hashlib.sha256(raw).hexdigest(),
            'seconds':time.monotonic()-start,'arithmetic':'Directed fixed-point integer arithmetic, rational roots and integer square roots only',
            'full_masks_closed':0,'human_or_kernel_verification':False}
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()
