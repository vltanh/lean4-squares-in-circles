#!/usr/bin/env python3
"""Floating subdivision search only; every output leaf needs exact replay."""
from math import sqrt
from pathlib import Path
import argparse,json,time

class I:
    __slots__=('lo','hi')
    def __init__(self,a,b=None):self.lo=float(a);self.hi=float(a if b is None else b)
    def __add__(a,b):b=iv(b);return I(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo)
    def __sub__(a,b):return a+-iv(b)
    def __rsub__(a,b):return iv(b)+-a
    def __mul__(a,b):
        b=iv(b);p=(a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi);return I(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=iv(b);assert b.lo>0;return a*I(1/b.hi,1/b.lo)
    def __rtruediv__(a,b):return iv(b)/a
    def sq(a):return I(0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi),max(a.lo*a.lo,a.hi*a.hi))
    def ab(a):return I(max(0,a.lo,-a.hi),max(abs(a.lo),abs(a.hi)))
    def rt(a):return I(sqrt(max(0,a.lo)),sqrt(max(0,a.hi)))
def iv(x):return x if isinstance(x,I) else I(x)
def imin(*v):v=[iv(x) for x in v];return I(min(x.lo for x in v),min(x.hi for x in v))
def imax(*v):v=[iv(x) for x in v];return I(max(x.lo for x in v),max(x.hi for x in v))
def orient(t):
    def p(z):
        a=1/sqrt(1+z*z);b=z*a;return a,b,(a+b)/2,(a-b)/2
    al,bl,hl,kl=p(t.lo);au,bu,hu,ku=p(t.hi)
    return I(au,al),I(bl,bu),I(hl,hu),I(ku,kl)
def mainorient(h):
    def p(z):
        k=sqrt(.5-z*z);return z+k,z-k,1/(4*z),z+1/(4*z)-1
    al,bl,gl,el=p(h.lo);au,bu,gu,eu=p(h.hi)
    return I(au,al),I(bl,bu),I(gu,gl),I(el,eu)

def evaluate(box):
    tp,tr,x,X,hm,ts=[I(*b) for b in box];ap,bp,p,kp=orient(tp);ar,br,r,kr=orient(tr);ass,bss,hs,ks=orient(ts)
    am,bm,gm,eta=mainorient(hm);D=X-x;W=1+r-p-D
    vals=[(x-p+451/810-(92/27)*eta).hi,(r+451/810-X-(92/27)*eta).hi,W.hi,
          (2*D.sq()-(1+(p-r).ab()).sq()).hi]
    A=imax(59/60,157/184+(27/92)*(p-x))+eta
    vals.append((61/60-A).hi)
    def clearance(a1,b1,h1,k1,a2,b2,h2,k2,d):
        support=imax(1+(h1-h2).ab(),.5+imax(k1*a2+h1*b2,h1*a2-k1*b2))
        nums=[imax(1/20,support-a1*d),imax(1/20,support-b1*d),imax(1/20,support-a2*d),imax(1/20,support-b2*d)]
        dens=[b1,a1,b2,a2]
        flo=min(num.lo/den.hi for num,den in zip(nums,dens) if den.hi>0)
        owner=I(flo,min((nums[1]/a1).hi,(nums[3]/a2).hi))
        return imax((support.sq()-d.sq()).rt(),owner)
    km=(.5-hm.sq()).rt();d1=271/480-gm;d2=263/480+x.ab()
    first=clearance(am,bm,hm,km,ass,bss,hs,ks,d1)
    second=clearance(ass,bss,hs,ks,ap,bp,p,kp,d2)
    ylo=gm-199/120+(32/9)*eta+first+second
    vals.append((p+.1-ylo).hi)
    U=imax(imin((1105/256-(X+kr).sq()).rt()-r,kr+(1105/256-(X+r).sq()).rt()),
           imin((1105/256-(X+r).sq()).rt()-kr,(1105/256-(X-kr).sq()).rt()-r))
    rad=1105/256-(A+29927/30000).sq()
    ca=imax(4421/12000+(32/9)*eta,1-rad.rt())
    dr=X-503/480;rra=(.5+dr*br)/ar;rnum=.5+dr*ar
    rlo=min(r.lo,rra.lo,rnum.lo/br.hi if br.hi>0 else 1e100)
    vals.append(U.hi-ca.lo-rlo)
    E=U-ylo;vals.append(E.hi)
    supp=imax(1+(p-r).ab(),.5+imax(kp*ar+p*br,p*ar-kp*br))
    Ecap=imin(E,D)
    vals.append((imax(ap*D+bp*Ecap,ar*D+br*Ecap)-supp).hi)
    vals.extend([((27/92)*W-eta).hi,(1/30-eta).hi,rad.hi])
    vals.append((D.sq()+imax(Ecap,0).sq()-supp.sq()).hi)
    code=min(range(len(vals)),key=vals.__getitem__)
    return vals[code],code

ROOT=((0,1),(0,1),(-23/405,23/60),(23/30,13/12),(.5,.65),(0,1))
WEIGHTS=(.4,.4,1,1,2,.4)
def halves(box,j):
    mid=sum(box[j])/2;left=list(box);right=list(box)
    left[j]=(box[j][0],mid);right[j]=(mid,box[j][1]);return tuple(left),tuple(right)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--nodes',type=int,default=1000000);ap.add_argument('--seconds',type=float,default=180);ap.add_argument('--depth',type=int,default=65);ap.add_argument('--greedy',action='store_true');ap.add_argument('--resume',action='store_true');ap.add_argument('--output',type=Path);args=ap.parse_args()
    base=Path(__file__).parent;out=args.output or base/'weak_middle_above_side_physical_candidate.json'
    start=time.monotonic();stack=[(ROOT,0,None)];events=[];leaves=0;counts={};maxdepth=0;best=0
    if args.resume:
        saved=json.loads(out.read_text());stack=saved['frontier'];events=saved['events'];leaves=saved['leaves'];counts={int(k):v for k,v in saved['counts'].items()};maxdepth=saved['max_depth']
    while stack and len(events)<args.nodes and time.monotonic()-start<args.seconds:
        box,depth,result=stack.pop();maxdepth=max(maxdepth,depth)
        v,code=evaluate(box) if result is None else result
        if v<-1e-9:
            events.append(-code-1);leaves+=1;counts[code]=counts.get(code,0)+1;continue
        if depth>=args.depth:
            stack.append((box,depth,(v,code)));break
        if args.greedy:
            candidates=[]
            widest=max((box[j][1]-box[j][0])*WEIGHTS[j] for j in range(6))
            for j in range(6):
                if (box[j][1]-box[j][0])*WEIGHTS[j]<widest/4:continue
                left,right=halves(box,j);vl=evaluate(left);vr=evaluate(right)
                score=((vl[0]<-1e-9)+(vr[0]<-1e-9),-max(vl[0],vr[0]),-(vl[0]+vr[0]),(box[j][1]-box[j][0])*WEIGHTS[j])
                candidates.append((score,j,left,right,vl,vr))
            _,j,left,right,vl,vr=max(candidates,key=lambda x:x[0])
        else:
            j=max(range(6),key=lambda j:(box[j][1]-box[j][0])*WEIGHTS[j]);left,right=halves(box,j);vl=vr=None
        events.append(j);stack.append((right,depth+1,vr));stack.append((left,depth+1,vl))
        if len(events)%20000<2:print(json.dumps({'nodes':len(events),'leaves':leaves,'frontier':len(stack),'depth':maxdepth,'discovery_volume_processed':1-sum(2.0**(-z[1]) for z in stack),'seconds':time.monotonic()-start}),flush=True)
    report={'status':'DISCOVERY_COMPLETE_AWAITING_EXACT_REPLAY' if not stack else 'INCOMPLETE_DISCOVERY',
            'events':events,'nodes':len(events),'leaves':leaves,'max_depth':maxdepth,'counts':counts,
            'frontier':stack,'seconds':time.monotonic()-start,'root':ROOT,
            'scope':'010/01 low-floor excludes above-main extras on both side strips using two original physical pairs; no full mask closure'}
    out.write_text(json.dumps(report,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('events','frontier','root')},indent=2),flush=True)
if __name__=='__main__':main()
