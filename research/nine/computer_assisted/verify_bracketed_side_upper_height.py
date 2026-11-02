"""Independent Fraction replay of the bracketed wide-main upper-side theorem."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,sys,time
HERE=Path(__file__).resolve().parent
KERNEL=HERE if (HERE/'interval_fraction.py').exists() else HERE.parents[1]/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(KERNEL))
from interval_fraction import I
ROOT=((F(1,2),F(13,20)),(F(0),F(1)),(F(29,60),F(13,12)))
def sqrt(v):return v.sqrt(90)

def main_frame(h):
    ka=sqrt(I(F(1,2))-I(h.lo).sq());kb=sqrt(I(F(1,2))-I(h.hi).sq())
    return I(h.hi+kb.lo,h.lo+ka.hi),I(h.lo-ka.hi,h.hi-kb.lo),1/(4*h)
def outsider_frame(t):
    a0=1/sqrt(1+I(t.lo).sq());a1=1/sqrt(1+I(t.hi).sq())
    b0=I(t.lo)*a0;b1=I(t.hi)*a1
    return I(a1.lo,a0.hi),I(b0.lo,b1.hi),I(((a0+b0)/2).lo,((a1+b1)/2).hi)

def reserve(box):
    h,t,X=[I(a,b) for a,b in box]
    am,bm,g=main_frame(h);a,b,hs=outsider_frame(t)
    blo=(h-F(61,60)).lo;bhi=(F(1,60)-g).hi
    if blo>bhi:return blo-bhi
    d=-X-I(blo,bhi);D=max(abs(d.lo),abs(d.hi));delta=g-D
    eta=(h.lo-F(1,2))**2/h.lo
    c=F(4421,12000)+F(32,9)*eta
    z=h.hi
    f=-F(2,3)*z+max(F(0),min((z-F(1,2))/6,(F(27,50)-z)/3))+F(1,400)
    heights=[]
    for sm in (-1,1):
      floor=f+(z-F(1,2))/4 if sm>0 else f
      for ss in (-1,1):
        cosine=a*am+ss*sm*b*bm;sine=ss*b*am-sm*a*bm
        sigma=max(F(1),((1+cosine.abs()+sine.abs())/2).lo)
        owner=[]
        for nx,ny in ((sm*am,bm),(-sm*bm,am),(ss*a,b),(-ss*b,a)):
            if ny.hi==0:continue
            numerator=I(sigma)-nx*d;assert numerator.lo>0
            owner.append(numerator.lo/ny.hi)
        distance=sqrt(I(sigma*sigma-D*D)).lo
        proxy=[hs.lo]
        for nx,ny in ((b,a),(a,b)):
            if ny.hi==0:continue
            numerator=F(1,2)+delta*nx;assert numerator.lo>0
            proxy.append(numerator.lo/ny.hi)
        clearance=max(min(owner),distance,g.lo+min(proxy));base=floor+clearance
        edge=min(F(503,480),F(91,60)-c)
        if X.lo+hs.lo>edge:
            dd=X-edge
            def reach(sign):
                nx,ny=(b,a) if sign>0 else (a,b)
                if ny.hi==0:return hs.lo
                numerator=F(1,2)+dd*nx
                # Endpoint reach may have a negative numerator; preserve its sign.
                if numerator.lo>=0:q=numerator.lo/ny.hi
                elif ny.lo>0:q=numerator.lo/ny.lo
                else:q=F(-1000)
                return min(hs.lo,q)
            up=c+reach(-ss);down=c+reach(ss)
            if base+down>0:base=max(base,up)
        heights.append(base)
    return min(heights)-F(3,5)

def verify(path):
    begin=time.monotonic();raw=path.read_bytes();data=json.loads(raw)
    assert data['type']=='bracketed_wide_main_upper_side_v1'
    assert data['status']=='COMPLETE_PENDING_INDEPENDENT_REPLAY' and data['remaining']==0 and data['pending']==[]
    assert tuple(tuple(map(F,r)) for r in data['root'])==ROOT
    todo=[(ROOT,0)];leaves=0;depth=0;least=None
    for i,tag in enumerate(data['nodes']):
        assert type(tag)is int and todo and 0<=tag<=3
        box,d=todo.pop();depth=max(depth,d)
        if tag==3:
            v=reserve(box);assert v>0,('failed leaf',i,box,str(v))
            leaves+=1;least=v if least is None else min(least,v)
        else:
            mid=sum(box[tag])/2;a=list(box);b=list(box)
            a[tag]=(box[tag][0],mid);b[tag]=(mid,box[tag][1])
            todo.extend(((tuple(b),d+1),(tuple(a),d+1)))
    assert not todo and leaves==data['leaves'] and depth==data['maximum_depth']
    return {'status':'EXACT_FRACTION_REPLAY_PASS','nodes':len(data['nodes']),'leaves':leaves,'maximum_depth':depth,
            'least_reserve':str(least),'seconds':time.monotonic()-begin,
            'certificate_sha256':hashlib.sha256(raw).hexdigest(),
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope':'Original upper side square beside a bracketed wide main; no full-mask closure'}
if __name__=='__main__':
    path=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'bracketed_side_upper_height_candidate.json'
    out=verify(path);path.with_name(path.stem+'_exact_replay.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2),flush=True)
