"""Independent Fraction reconstruction of the upper-central floor table.

No discovery module, optimizer, or directed-integer evaluator is imported.
The physical expressions and tree domain are reconstructed here. Radicals
are enclosed by rational multiples of 2**-90 and integer comparisons.
"""
from fractions import Fraction as F
from pathlib import Path
from collections import Counter
import hashlib, json, sys, time

HERE=Path(__file__).resolve().parent
KERNEL=HERE if (HERE/'interval_fraction.py').exists() else HERE.parent/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(KERNEL))
from interval_fraction import I

ROOT=(F(0),F(1),F(0),F(1),F(-23,405),F(23,60),F(-29,60),F(29,60),F(1,2),F(13,20))

def low_high_max(*v):
    v=[a if isinstance(a,I) else I(a) for a in v]
    return I(max(a.lo for a in v),max(a.hi for a in v))
def low_high_min(*v):
    v=[a if isinstance(a,I) else I(a) for a in v]
    return I(min(a.lo for a in v),min(a.hi for a in v))
def rt(v):return v.sqrt(90)

def orientation(tlo,thi):
    def point(t):
        a=1/rt(1+I(t).sq());b=t*a
        return a,b,(a+b)/2,(a-b)/2
    a,b,h,k=point(tlo);A,B,H,K=point(thi)
    return I(A.lo,a.hi),I(b.lo,B.hi),I(h.lo,H.hi),I(K.lo,k.hi)

def inner_orientation(hlo,hhi):
    k0=rt(I(F(1,2))-I(hlo).sq());k1=rt(I(F(1,2))-I(hhi).sq())
    return (I((hhi+k1).lo,(hlo+k0).hi),I((hlo-k0).lo,(hhi-k1).hi),
            I(hlo,hhi),I(k1.lo,k0.hi),I(1/(4*hhi),1/(4*hlo)),
            I(hlo+1/(4*hlo)-1,hhi+1/(4*hhi)-1))

def physical_support(first,second):
    a,b,h,k=first;A,B,H,K=second
    # Direct relative-frame expression and its collected equivalent.
    direct=(1+a*A+b*B+(a*B-b*A).abs())/2
    collected=F(1,2)+low_high_max(k*A+h*B,h*A-k*B)
    return low_high_max(1+(h-H).abs(),direct,collected)

def vertical_clearance(first,second,horizontal,inset):
    a,b,h,k=first;A,B,H,K=second;s=physical_support(first,second)
    axes=[]
    for nx,ny in [(a,b),(b,a),(A,B),(B,A)]:
        numerator=s-nx*horizontal
        assert numerator.lo>0
        if ny.hi>0: axes.append(numerator.lo/ny.hi)
    squared=s.sq()-I(horizontal).sq()
    disk=rt(I(max(F(0),squared.lo),max(F(0),squared.hi))).lo
    delta=inset-horizontal;proxy=[H.lo]
    for nx,ny in [(B,A),(A,B)]:
        numerator=F(1,2)+delta*nx
        assert numerator.lo>0
        if ny.hi>0:proxy.append(numerator.lo/ny.hi)
    return max(min(axes),disk,inset.lo+min(proxy))

def main_height_lower(lo,hi):
    def f(h):return F(32,9)*h+F(41,36)/h-F(32,9)-F(199,120)
    if 128*hi*hi<=41:return f(hi)
    if 128*lo*lo>=41:return f(lo)
    return (F(4,9)*rt(I(82))-F(32,9)-F(199,120)).lo

def check_leaf(box,rule):
    pl,ph,ul,uh,xlo,xhi,vlo,vhi,hlo,hhi=box
    P=orientation(pl,ph);U=orientation(ul,uh)
    aM,bM,hM,kM,g,eta=inner_orientation(hlo,hhi)
    M=(aM,bM,hM,kM);ap,bp,p,kp=P;au,bu,u,ku=U
    x=I(xlo,xhi);v=I(vlo,vhi)
    if rule==0:return -(x-p+F(451,810)-F(92,27)*eta).hi
    if rule==1:return eta.lo-F(1,30)
    A0=low_high_max(F(23,30),p+F(1,2)-x);A1=F(13,12)
    if rule==2:return A0.lo-A1
    absolute=x.abs()
    horizontal=min(F(31,60),max(absolute.hi-g.lo+F(1,60),F(61,60)-hlo-absolute.lo))
    ylow=main_height_lower(hlo,hhi)+vertical_clearance(M,P,horizontal,g)
    if rule==3:return ylow-p.hi-F(1,10)
    cap=u.hi+F(1,10)
    if vhi<=F(-1,10) and A0.lo<=A1:
        def edge_height(A):
            return (rt(I(F(91,60)**2-A*A))-rt(I(1-(A+vhi)**2))).hi
        cap=min(cap,max(edge_height(A0.lo),edge_height(A1)))
    if rule==4:return ylow-cap
    dy=max(F(0),cap-ylow);dx=(x-v).abs().hi;s=physical_support(P,U).lo
    if rule==5:return s*s-dx*dx-dy*dy
    assert rule==6
    projected=max(ap.hi*dx+bp.hi*dy,bp.hi*dx+ap.hi*dy,
                  au.hi*dx+bu.hi*dy,bu.hi*dx+au.hi*dy)
    return s-projected

def verify(data):
    assert data['type']=='upper_central_floor_prefix_v1'
    assert data['status']=='COMPLETE_PENDING_INDEPENDENT_REPLAY'
    assert tuple(map(F,data['root']))==ROOT
    assert data['remaining']==0 and data['pending']==[]
    pending=[(ROOT,0)];count=0;maximum_depth=0;least=None;rules=Counter()
    for i,tag in enumerate(data['nodes']):
        assert pending and type(tag)is int and 0<=tag<=11,('invalid node',i)
        box,depth=pending.pop();maximum_depth=max(maximum_depth,depth)
        if tag<5:
            cut=(box[2*tag]+box[2*tag+1])/2
            low,high=list(box),list(box);low[2*tag+1]=cut;high[2*tag]=cut
            pending.extend([(tuple(high),depth+1),(tuple(low),depth+1)])
        else:
            value=check_leaf(box,tag-5)
            assert value>0,('false leaf',i,tag-5,str(value),box)
            rules[tag-5]+=1;count+=1;least=value if least is None else min(least,value)
    assert not pending
    assert len(data['nodes'])==2*count-1 and count==data['leaves']
    assert maximum_depth==data['maximum_depth']
    return dict(status='PASS',nodes=len(data['nodes']),leaves=count,maximum_depth=maximum_depth,
                least_reserve=str(least),leaf_rules=dict(sorted(rules.items())),
                arithmetic='Independent Fraction formulas with 90-bit radical bounds',
                scope='Weak-middle upper central square above P has wholefloor greater than 1/10; no complete mask closure alone',
                human_or_kernel_verification=False)

if __name__=='__main__':
    path=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'upper_central_floor_candidate.json'
    raw=path.read_bytes();start=time.monotonic();result=verify(json.loads(raw))
    result.update(seconds=time.monotonic()-start,certificate_sha256=hashlib.sha256(raw).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    path.with_name(path.stem+'_exact_replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)
