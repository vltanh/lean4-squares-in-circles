"""Independent Fraction interval replay of the lower-side height envelope.

Reconstructs geometry and complete coverage; imports no producer or dyadic
arithmetic. Corner maxima use all eight signed/chiral corner formulas.
"""
import hashlib,json,sys,time
from fractions import Fraction as F
from pathlib import Path

HERE=Path(__file__).resolve().parent
KERNEL=HERE if (HERE/'interval_fraction.py').exists() else HERE.parent/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(KERNEL))
from interval_fraction import I

ROOT=(F(1,2),F(13,20),F(0),F(1),F(29,60),F(13,12))
Q=F(1105,256)

def square_root(value):return value.sqrt(90)
def unit_from_h(v):
    k=square_root(I(F(1,2))-v.sq())
    return k,v+k,v-k
def unit_from_t(v):
    a=1/square_root(1+v.sq());b=v*a
    return a,b,(a+b)/2,(a-b)/2

def acceptance_lower(box,target):
    hlo,hhi,tlo,thi,xlo,xhi=box;h=I(hlo,hhi);x=I(xlo,xhi)
    k0,a0,b0=unit_from_h(I(hlo));k1,a1,b1=unit_from_h(I(hhi))
    k=I(k1.lo,k0.hi);aM=I(a1.lo,a0.hi);bM=I(b0.lo,b1.hi)
    aa,ba,ha,ka=unit_from_t(I(tlo));ab,bb,hb,kb=unit_from_t(I(thi))
    a=I(ab.lo,aa.hi);b=I(ba.lo,bb.hi);hs=I(ha.lo,hb.hi);ks=I(kb.lo,ka.hi)
    inset=1/(4*h)
    horizontal=max(xhi-inset.lo+F(1,60),F(61,60)-hlo-xlo)
    # Two independently derived support forms; each is a valid lower bound.
    support0=(1+aM*a+bM*b+(aM*b-bM*a).abs())/2
    support=max(support0.lo,1+(h-hs).abs().lo,
                (F(1,2)+k*a+h*b).lo,(F(1,2)+h*a-k*b).lo)
    axis_bounds=[]
    for nx,ny in [(aM,bM),(bM,aM),(a,b),(b,a)]:
        numerator=I(support)-nx*horizontal
        assert numerator.lo>0
        if ny.hi>0:axis_bounds.append(numerator.lo/ny.hi)
    assert len(axis_bounds)>=2
    distance=square_root(I(support).sq()-I(horizontal).sq()).lo
    delta=inset-horizontal
    proxy_bounds=[hs.lo]
    for nx,ny in [(b,a),(a,b)]:
        numerator=F(1,2)+delta*nx
        assert numerator.lo>0
        if ny.hi>0:proxy_bounds.append(numerator.lo/ny.hi)
    clearance=max(min(axis_bounds),distance,inset.lo+min(proxy_bounds))
    orientations=[[(ks,hs),(hs,-ks),(-ks,-hs),(-hs,ks)],
                  [(hs,ks),(ks,-hs),(-hs,-ks),(-ks,hs)]]
    tops=[]
    for corners in orientations:
        caps=[(square_root(I(Q)-(x+dx).sq())-dy).hi for dx,dy in corners]
        tops.append(min(caps))
    depth=min(max(tops),F(91,60))
    reserve=clearance-depth+F(2,3)*hlo
    if target in('bump','bump_plus_1_400'):
        bump=max(F(0),min((hhi-F(1,2))/6,(F(27,50)-hlo)/3,F(1,225)))
        reserve-=bump
    if target=='bump_plus_1_400':reserve-=F(1,400)
    return reserve

def verify(data):
    assert data['type']=='side_height_envelope_prefix_v1'
    assert data['target']in('linear','bump','bump_plus_1_400')
    assert data['status']=='COMPLETE_PENDING_INDEPENDENT_REPLAY'
    assert tuple(map(F,data['root']))==ROOT
    assert data['remaining']==0 and data['pending']==[]
    todo=[(ROOT,0)];nodes=data['nodes'];leaves=0;least=None;maximum_depth=0
    for tag in nodes:
        assert todo and type(tag)is int and 0<=tag<=3
        box,dep=todo.pop();maximum_depth=max(maximum_depth,dep)
        if tag==3:
            margin=acceptance_lower(box,data['target']);assert margin>0,(box,str(margin))
            leaves+=1;least=margin if least is None else min(least,margin)
        else:
            cut=(box[2*tag]+box[2*tag+1])/2
            low,high=list(box),list(box);low[2*tag+1]=cut;high[2*tag]=cut
            todo.extend([(tuple(high),dep+1),(tuple(low),dep+1)])
    assert not todo and leaves==data['leaves']
    assert len(nodes)==2*leaves-1 and maximum_depth==data['maximum_depth']
    return dict(status='PASS',target=data['target'],nodes=len(nodes),leaves=leaves,maximum_depth=maximum_depth,least_reserve=str(least),arithmetic='Fraction with independently bounded90-bit radicals',scope='Pair height envelope only; no mask closure')

if __name__=='__main__':
    p=Path(sys.argv[1]);raw=p.read_bytes();start=time.monotonic()
    result=verify(json.loads(raw));result.update(seconds=time.monotonic()-start,certificate_sha256=hashlib.sha256(raw).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    p.with_name(p.stem+'_exact_replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)
