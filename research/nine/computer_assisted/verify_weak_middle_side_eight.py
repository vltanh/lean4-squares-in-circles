#!/usr/bin/env python3
"""Independent exact evaluator for the wide-main side-triple/lower-side scope.

Reads only split/leaf tags from untrusted discovery. Roots, signed physical
frames, endpoint resource, owner alternatives and directed arithmetic are
reconstructed here, with integer dyadic intervals and rational midpoints.
No producer import, floating-point evaluation, external solver, Lean or CI.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,time
SCALE=1<<80

def ceildiv(a,b):return -((-a)//b)
def down(x):x=F(x);return x.numerator*SCALE//x.denominator
def up(x):x=F(x);return ceildiv(x.numerator*SCALE,x.denominator)
class I:
    __slots__=('lo','hi')
    def __init__(self,a,b=None,raw=False):
        if raw:self.lo=a;self.hi=a if b is None else b
        else:self.lo=down(a);self.hi=up(a if b is None else b)
        assert self.lo<=self.hi
    def __add__(a,b):b=iv(b);return I(a.lo+b.lo,a.hi+b.hi,True)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo,True)
    def __sub__(a,b):return a+-iv(b)
    def __rsub__(a,b):return iv(b)+-a
    def __mul__(a,b):
        b=iv(b);v=(a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi)
        return I(min(v)//SCALE,ceildiv(max(v),SCALE),True)
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
        lo=max(0,a.lo)*SCALE;hi=a.hi*SCALE
        l=isqrt(lo);h=isqrt(hi);h+=h*h<hi
        assert l*l<=lo and h*h>=hi
        return I(l,h,True)
def iv(x):return x if isinstance(x,I) else I(x)
def raw(x):return I(x,raw=True)

def shape(t):
    def point(z):
        z=raw(z);a=1/(1+z.sq()).rt();b=z*a
        return a,b,(a+b)/2,(a-b)/2
    lo=point(t.lo);hi=point(t.hi)
    a=I(hi[0].lo,lo[0].hi,True);b=I(lo[1].lo,hi[1].hi,True)
    h=I(lo[2].lo,hi[2].hi,True);k=I(hi[3].lo,lo[3].hi,True)
    return a,b,h,k,1/(4*h)

Q=F(1105,256);L=F(29,60);U=F(13,12);RHO=F(91,60)
A=F(503,480);K=F(80669,93000);CSTAR=F(4421,12000)
NEG=-1000*SCALE;POS=1000*SCALE

def shape_h(h):
    lo=raw(h.lo);hi=raw(h.hi)
    kl=(F(1,2)-lo.sq()).rt();kh=(F(1,2)-hi.sq()).rt()
    a=I((hi+kh).lo,(lo+kl).hi,True)
    b=I((lo-kl).lo,(hi-kh).hi,True)
    k=I(kh.lo,kl.hi,True)
    return a,b,h,k,1/(4*h)

def eta_h(h):
    def eta(z):
        z=F(z,SCALE);return (z-F(1,2))**2/z
    return I(eta(h.lo),eta(h.hi))

def main_height_floor(h):
    # The accepted piecewise-linear envelope is decreasing on its whole root.
    z=F(h.hi,SCALE)
    return down(-F(2,3)*z+max(F(0),min((z-F(1,2))/6,(F(27,50)-z)/3))+F(1,400))

def div_lower(n,den):
    if den.hi==0:return POS
    if n.lo>=0:return n.lo*SCALE//den.hi
    if den.lo==0:return NEG
    return n.lo*SCALE//den.lo

def support_lower(s,ss,t,st):
    co=s[0]*t[0]+ss*st*s[1]*t[1]
    si=ss*s[1]*t[0]-st*s[0]*t[1]
    return max(SCALE,((1+co.ab()+si.ab())/2).lo)

def psi_upper(t):
    lo=shape(raw(t.lo));hi=shape(raw(t.hi))
    lin=max((lo[0]/2+F(19,54)*lo[1]).hi,(hi[0]/2+F(19,54)*hi[1]).hi)
    if t.lo<=up(F(19,27)) and t.hi>=down(F(19,27)):
        lin=max(lin,(I(1090).rt()/54).hi)
    return min(lin,(1-hi[0]/2+hi[1]/18).hi)

def corner_upper(s,x,sign):
    a,b,h,k,g=s;out=up(RHO)
    for xx,yy in zip((h,sign*k,-h,-sign*k),(-sign*k,h,sign*k,-h)):
        rad=Q-(x+xx).sq()
        if rad.hi<0:return NEG
        out=min(out,rad.rt().hi-yy.lo)
    return out

def main_clearance(s,ss,m,sm,d):
    a,b,h,k,g=s;am,bm,hm,km,gm=m
    sigma=support_lower(s,ss,m,sm)
    D=max(abs(d.lo),abs(d.hi));delta=gm-raw(D)
    reach=min(h.lo,div_lower(F(1,2)+delta*b,a),div_lower(F(1,2)+delta*a,b))
    inset=gm.lo+reach
    owner=POS
    for nx,ny in ((sm*am,bm),(-sm*bm,am),(ss*a,b),(-ss*b,a)):
        if ny.hi==0:continue
        owner=min(owner,div_lower(raw(sigma)-nx*d,ny))
    rad=raw(sigma).sq()-raw(D).sq()
    disk=I(max(0,rad.lo),max(0,rad.hi),True).rt().lo
    return max(inset,owner,disk)

def endpoint_lower(s,sg,x,base,c):
    a,b,h,k,g=s;edge=min(up(A),up(RHO)-c)
    if x.lo+h.lo<=edge:return base
    delta=x-raw(edge)
    def reach(sign):
        return min(h.lo,div_lower(F(1,2)+delta*b,a) if sign>0 else div_lower(F(1,2)+delta*a,b))
    wp=c+reach(sg);wm=c+reach(-sg)
    return max(base,wp) if base+wm>0 else base

def pair_ranges(s,ss,t,st,d,lo,hi,first):
    if lo>hi:return []
    sigma=support_lower(s,ss,t,st);a,b=s[:2];c,e=t[:2];out=[]
    for nx,mag,sign in ((a,b,ss),(b,a,-ss),(c,e,st),(e,c,-st)):
        low=-d.hi;high=d.hi;num=raw(sigma)-nx*d
        if mag.hi==0:
            if num.lo>0:continue
        elif sign>0:low=max(low,div_lower(num,mag))
        else:high=min(high,-div_lower(num,mag))
        if low>high:continue
        out.append((lo-high,hi-low) if first else (lo+low,hi+high))
    return out

def margin(box,kind):
    tl,tp,tr,Z,x,X,c0,hb,hc=[I(*z) for z in box]
    left,p,right=shape(tl),shape(tp),shape(tr)
    bmain,cmain=shape_h(hb),shape_h(hc)
    eb,ec=eta_h(hb),eta_h(hc);V=eb+ec
    psL,psR=psi_upper(tl),psi_upper(tr)
    hmax=min(up(F(8,15)),(1/(4*raw(c0.lo))).hi)
    hh=raw(hmax);jlo=(hh+(F(1,2)-hh.sq()).rt()).lo
    a0max=min(up(F(61,60)),((Q-(1-c0).sq()).rt()-raw(jlo)).hi)
    a0min=(F(157,184)+V+F(27,92)*(X-raw(psR))).lo
    vcap=min(up(F(1,30)),(F(27,92)*(F(451,810)-Z+raw(psL))).hi,
             (F(27,92)*(F(451,810)-X+raw(psR))).hi,
             (F(27,92)*(1-Z-X+raw(psL)+raw(psR))).hi)
    dl=x+Z;dr=X-x
    basic=min(vcap-V.lo,a0max-a0min,(c0-CSTAR-F(32,9)*V).hi,
              (dl-left[4]-p[4]).hi,(dr-p[4]-right[4]).hi,
              (left[2]+p[2]-dl).hi,(p[2]+right[2]-dr).hi)
    if basic<0:return basic
    c3=max((CSTAR+F(32,9)*V).lo,(K-c0+F(32,9)*V).lo)
    arc=(4-F(73,30000)+V-(Q-(1-c0).sq()).rt()).lo
    assert arc>0
    rad=Q-raw(arc).sq()
    if rad.hi<0:return rad.hi
    c3=max(c3,(1-rad.rt()).lo)
    a3min=(F(157,184)+V+F(27,92)*(Z-raw(psL))).lo
    rad=Q-(raw(a3min)+F(29927,30000)).sq()
    if rad.hi<0:return rad.hi
    c3=max(c3,(1-rad.rt()).lo)
    blo=(hb-raw(a0max)).lo;bhi=(F(1,60)-bmain[4]-ec).hi
    clo=(cmain[4]+eb-F(1,60)).lo;chi=(F(61,60)-hc).hi
    dmain=min(chi-blo,(hb+hc).hi)
    basic=min(basic,up(F(1,2))-c3,bhi-blo,chi-clo,dmain-(bmain[4]+cmain[4]).lo)
    if basic<0:return basic
    bouter=(bmain[4]+ec-F(199,120)+F(32,9)*V).lo
    couter=(cmain[4]+eb-F(199,120)+F(32,9)*V).lo
    by=max(main_height_floor(hb),bouter,(raw(c0.lo)-F(121,60)-raw(bhi)).lo)
    cy=max(couter,(raw(c3)+raw(clo)-F(121,60)).lo)
    bx=I(blo,bhi,True);cx=I(clo,chi,True)
    answer=NEG
    for sb in (-1,1):
      for sc in (-1,1):
        sigma=support_lower(bmain,sb,cmain,sc)
        owners=((bmain[0],sb*bmain[1]),(bmain[1],-sb*bmain[0]),
                (cmain[0],sc*cmain[1]),(cmain[1],-sc*cmain[0]))
        for sp in (-1,1):
          cbp=main_clearance(p,sp,bmain,sb,x-bx)
          ccp=main_clearance(p,sp,cmain,sc,x-cx)
          pl=max(by+cbp,cy+ccp)
          ph=corner_upper(p,x,sp)
          if kind=='low_floor':ph=min(ph,(p[2]+F(1,10)).hi)
          if ph<pl:
              answer=max(answer,ph-pl);continue
          for sl in (-1,1):
            cbl=main_clearance(left,sl,bmain,sb,-Z-bx)
            ll=endpoint_lower(left,-sl,Z,by+cbl,c0.lo);lh=corner_upper(left,Z,-sl)
            if lh<ll:
                answer=max(answer,lh-ll);continue
            lefts=pair_ranges(left,sl,p,sp,dl,ll,lh,False)
            for sr in (-1,1):
              ccr=main_clearance(right,sr,cmain,sc,X-cx)
              rl=endpoint_lower(right,sr,X,max(down(F(-9,20)),cy+ccr),c3)
              rh=corner_upper(right,X,sr)
              if kind=='low_right':rh=min(rh,up(F(3,5)))
              if rh<rl:
                  answer=max(answer,rh-rl);continue
              rights=pair_ranges(p,sp,right,sr,dr,rl,rh,True)
              best=NEG
              for p0,p1 in lefts:
                for p2,p3 in rights:
                  pylo=max(pl,p0,p2);pyhi=min(ph,p1,p3)
                  Bhi=min(pyhi-cbp,lh-cbl,-bouter)
                  Chi=min(pyhi-ccp,rh-ccr,-couter)
                  elo=max(-dmain,cy-Bhi);ehi=min(dmain,Chi-by)
                  overlap=min(pyhi-pylo,ehi-elo,Bhi-by,Chi-cy)
                  if overlap>=0:
                      E=I(elo,ehi,True)
                      m=max((nx*raw(dmain)+ny*E).hi-sigma for nx,ny in owners)
                      overlap=min(overlap,m)
                  best=max(best,overlap)
              answer=max(answer,min(ph-pl,lh-ll,rh-rl,best))
    return min(basic,answer)

def root():
    return ((F(0),F(1)),)*3+((L,U),(-F(23,60),F(23,60)),(L,U),(CSTAR,F(1,2)))+((F(1,2),F(13,20)),)*2

def verify(path,progress=0):
    begin=time.monotonic();raw_bytes=path.read_bytes();data=json.loads(raw_bytes)
    kind=data['kind'];assert kind in ('low_floor','low_right')
    assert data['status']=='COMPLETE_DISCOVERY'
    pending=[(root(),0)];leaves=0;depth=0;least=None;nodes=data['events']
    for i,tag in enumerate(nodes):
        assert type(tag)is int and pending,('bad event',i,tag)
        box,d=pending.pop();depth=max(depth,d)
        if 0<=tag<9:
            mid=sum(box[tag])/2;left=list(box);right=list(box)
            left[tag]=(box[tag][0],mid);right[tag]=(mid,box[tag][1])
            pending.append((tuple(right),d+1));pending.append((tuple(left),d+1))
        else:
            assert tag==9,('unknown tag',i,tag)
            upper=margin(box,kind);assert upper<0,('failed leaf',i,box,F(upper,SCALE))
            reserve=-upper;least=reserve if least is None else min(least,reserve);leaves+=1
        if progress and (i+1)%progress==0:
            print(json.dumps({'nodes':i+1,'leaves':leaves,'pending':len(pending),'seconds':time.monotonic()-begin}),flush=True)
    assert not pending,'incomplete cover'
    return {'status':'EXACT_REPLAY_PASS','kind':kind,'nodes':len(nodes),'leaves':leaves,'maximum_depth':depth,
            'least_reserve':str(F(least,SCALE)),'seconds':time.monotonic()-begin,
            'certificate_sha256':hashlib.sha256(raw_bytes).hexdigest(),
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope':'Outer-actual main chain and both-weak side-endpoint cone triple with one original lower-left side square; this is not a full 010/11 assembly.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('certificate',type=Path);p.add_argument('--report',type=Path);p.add_argument('--progress',type=int,default=0);args=p.parse_args()
    result=verify(args.certificate,args.progress)
    if args.report:args.report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()

