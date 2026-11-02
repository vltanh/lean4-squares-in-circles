"""Independent Fraction reconstruction of the signed side-height theorem."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,sys,time
HERE=Path(__file__).resolve().parent
KERNEL=HERE if (HERE/'interval_fraction.py').exists() else HERE.parents[1]/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(KERNEL))
from interval_fraction import I
Q=F(1105,256)
ROOT=((F(1,2),F(13,20)),(F(0),F(1)),(F(29,60),F(13,12)))

def sqrt(v):return v.sqrt(90)
def frame_h(h):
    k0=sqrt(I(F(1,2))-I(h.lo).sq());k1=sqrt(I(F(1,2))-I(h.hi).sq())
    return I(h.hi+k1.lo,h.lo+k0.hi),I(h.lo-k0.hi,h.hi-k1.lo),h,I(k1.lo,k0.hi),1/(4*h)
def frame_t(t):
    a0=1/sqrt(1+I(t.lo).sq());a1=1/sqrt(1+I(t.hi).sq())
    b0=I(t.lo)*a0;b1=I(t.hi)*a1
    h0=(a0+b0)/2;h1=(a1+b1)/2;k0=(a0-b0)/2;k1=(a1-b1)/2
    return I(a1.lo,a0.hi),I(b0.lo,b1.hi),I(h0.lo,h1.hi),I(k1.lo,k0.hi)

def reserve(box):
    h,t,X=[I(a,b) for a,b in box]
    am,bm,hm,km,g=frame_h(h);a,b,hs,ks=frame_t(t)
    blo=(h-F(61,60)).lo;bhi=(F(1,60)-g).hi
    if blo>bhi:return blo-bhi
    d=-X-I(blo,bhi);D=max(abs(d.lo),abs(d.hi));delta=g-D
    z=h.lo
    target=-F(2,3)*z+max(F(0),min((z-F(1,2))/6,(F(27,50)-z)/3))+F(1,400)+(z-F(1,2))/4
    answers=[]
    for ss in (-1,1):
        # Vertical reflection makes the original S the upper square.
        sm=-1;sf=-ss
        cosine=a*am+sf*sm*b*bm;sine=sf*b*am-sm*a*bm
        sigma=max(F(1),((1+cosine.abs()+sine.abs())/2).lo)
        axes=((sm*am,bm),(-sm*bm,am),(sf*a,b),(-sf*b,a))
        owner=[]
        for nx,ny in axes:
            if ny.hi==0:continue
            numerator=I(sigma)-nx*d;assert numerator.lo>0
            owner.append(numerator.lo/ny.hi)
        physical=min(owner)
        distance=sqrt(I(sigma*sigma-D*D)).lo
        inset=[hs.lo]
        for nx,ny in ((b,a),(a,b)):
            if ny.hi==0:continue
            numerator=F(1,2)+delta*nx;assert numerator.lo>0
            inset.append(numerator.lo/ny.hi)
        clearance=max(physical,distance,g.lo+min(inset))
        corners=((hs,-ss*ks),(ss*ks,hs),(-hs,ss*ks),(-ss*ks,-hs))
        depth=min(F(91,60),*((sqrt(I(Q)-(X+dx).sq())-dy).hi for dx,dy in corners))
        answers.append(clearance-depth-target)
    return min(answers)

def verify(path):
    begin=time.monotonic();raw=path.read_bytes();data=json.loads(raw)
    assert data['type']=='signed_left_main_height_v1'
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
            'scope':'Signed left-main lower-side height theorem only; no full-mask closure'}
if __name__=='__main__':
    path=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'signed_lower_side_height_candidate.json'
    out=verify(path);path.with_name(path.stem+'_exact_replay.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2),flush=True)
