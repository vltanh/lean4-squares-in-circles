"""Exact finite-tree discovery for an upper central unit above low-floor P.

This is a producer, not an acceptance checker.  Only complete trees are
eligible for independent reconstruction.  All square frames are physical.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse, json, sys, time

HERE = Path(__file__).resolve().parent
KERNEL=HERE if (HERE/'verify_joint_five_dyadic.py').exists() else HERE.parent/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(KERNEL))
from verify_joint_five_dyadic import I, SCALE

ROOT = (F(0),F(1), F(0),F(1), F(-23,405),F(23,60),
        F(-29,60),F(29,60), F(1,2),F(13,20))

def point(n): return I.raw(n,n)
def imax(*xs):
    xs=[x if isinstance(x,I) else I(x) for x in xs]
    return I.raw(max(x.lo for x in xs),max(x.hi for x in xs))
def imin(*xs):
    xs=[x if isinstance(x,I) else I(x) for x in xs]
    return I.raw(min(x.lo for x in xs),min(x.hi for x in xs))
def nonnegative_root(x): return I.raw(max(0,x.lo),max(0,x.hi)).sqrt()

def frame_t(t):
    def at(s):
        a=1/(1+s.sq()).sqrt(); b=s*a
        return a,b,(a+b)/2,(a-b)/2
    a0,b0,p0,k0=at(point(t.lo)); a1,b1,p1,k1=at(point(t.hi))
    return (I.raw(a1.lo,a0.hi),I.raw(b0.lo,b1.hi),
            I.raw(p0.lo,p1.hi),I.raw(k1.lo,k0.hi))

def frame_h(h):
    def at(s):
        k=(F(1,2)-s.sq()).sqrt();g=1/(4*s)
        return s+k,s-k,k,g,s+g-1
    a0,b0,k0,g0,e0=at(point(h.lo));a1,b1,k1,g1,e1=at(point(h.hi))
    return (I.raw(a1.lo,a0.hi),I.raw(b0.lo,b1.hi),h,
            I.raw(k1.lo,k0.hi),I.raw(g1.lo,g0.hi),I.raw(e0.lo,e1.hi))

def sigma(f,g):
    a,b,h,k=f; A,B,H,K=g
    return imax(1+(h-H).abs(),F(1,2)+imax(k*A+h*B,h*A-k*B))

def clearance(f,g,d,inset):
    s=sigma(f,g); a,b,h,k=f;A,B,H,K=g
    axis=[]
    for nx,ny in [(a,b),(b,a),(A,B),(B,A)]:
        numerator=s-nx*d
        assert numerator.lo>0
        if ny.hi>0: axis.append(numerator.lo*SCALE//ny.hi)
    axis=min(axis)
    chord=nonnegative_root(s.sq()-d.sq()).lo
    delta=inset-d
    reach=[H.lo]
    for nx,ny in [(B,A),(A,B)]:
        numerator=F(1,2)+delta*nx
        assert numerator.lo>0
        if ny.hi>0: reach.append(numerator.lo*SCALE//ny.hi)
    return point(max(axis,chord,inset.lo+min(reach)))

def base_height(h):
    def at(s): return F(32,9)*s+F(41,36)/s-F(32,9)-F(199,120)
    if h.hi*h.hi*128 <= 41*SCALE*SCALE: return at(point(h.hi)).lo
    if h.lo*h.lo*128 >= 41*SCALE*SCALE: return at(point(h.lo)).lo
    return (F(4,9)*I(82).sqrt()-F(32,9)-F(199,120)).lo

def constraints(box):
    tp,tu,x,v,h=[I(box[2*j],box[2*j+1]) for j in range(5)]
    fp,fu=frame_t(tp),frame_t(tu)
    am,bm,hm,km,g,eta=frame_h(h);fm=(am,bm,hm,km)
    ap,bp,p,kp=fp;au,bu,u,ku=fu
    absolute=x.abs()
    d=imin(imax(absolute-g+F(1,60),F(61,60)-h-absolute),F(31,60))
    # A point upper bound is sufficient in every clearance expression.
    d=point(d.hi)
    ylow=point(base_height(h))+clearance(fm,fp,d,g)
    A0=imax(F(23,30),p+F(1,2)-x);A1=I(F(13,12))
    cap=u+F(1,10)
    if box[7] <= F(-1,10) and A0.lo <= A1.hi:
        # F_v(A) has only a minimum; its maximum on [A0,A1] is
        # at an endpoint. It increases with v throughout this rectangle.
        def outer_gap(A):
            return (I(F(91,60)).sq()-A.sq()).sqrt()-(1-(A+point(v.hi)).sq()).sqrt()
        floor_A=point(min(A0.lo,A1.lo))
        cap=imin(cap,imax(outer_gap(floor_A),outer_gap(A1)))
    dy=imax(0,cap-ylow);dx=(x-v).abs();s=sigma(fp,fu)
    return [x-p+F(451,810)-F(92,27)*eta,
            F(1,30)-eta,A1-A0,p+F(1,10)-ylow,cap-ylow,
            dx.sq()+dy.sq()-s.sq(),
            imax(ap*dx+bp*dy,bp*dx+ap*dy,au*dx+bu*dy,bu*dx+au*dy)-s]

def upper(box):
    vals=constraints(box)
    return min((v.hi,i) for i,v in enumerate(vals))

def children(box,axis):
    cut=(box[2*axis]+box[2*axis+1])/2
    a,b=list(box),list(box);a[2*axis+1]=cut;b[2*axis]=cut
    return tuple(a),tuple(b)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-nodes',type=int,default=1000000)
    args=ap.parse_args();start=last=time.monotonic()
    nodes=[];todo=[(ROOT,0)];count=0;maximum_depth=0;least=None
    path=HERE/'upper_central_floor_candidate.json'
    def save(status):
        path.write_text(json.dumps(dict(type='upper_central_floor_prefix_v1',
            status=status,root=list(map(str,ROOT)),nodes=nodes,leaves=count,
            maximum_depth=maximum_depth,remaining=len(todo),
            pending=[dict(box=list(map(str,b)),depth=d) for b,d in todo],
            least_reserve=None if least is None else str(F(least,SCALE))),separators=(',',':'))+'\n')
    while todo and len(nodes)<args.max_nodes:
        box,dep=todo.pop();maximum_depth=max(maximum_depth,dep);value,rule=upper(box)
        if value<0:
            nodes.append(5+rule);count+=1;least=-value if least is None else min(least,-value)
        else:
            if dep>=60:
                todo.append((box,dep));save('INCOMPLETE_DEPTH');return
            choices=[]
            widths=[(box[2*j+1]-box[2*j])/(ROOT[2*j+1]-ROOT[2*j]) for j in range(5)]
            widest=max(widths)
            for ax in range(5):
                if widths[ax]*2 < widest: continue
                left,right=children(box,ax)
                vals_left,vals_right=constraints(left),constraints(right)
                vl=min(vals_left[j].hi for j in (0,2,5,6))
                vr=min(vals_right[j].hi for j in (0,2,5,6))
                score=max(vl,-SCALE//100)+max(vr,-SCALE//100)
                choices.append((score,max(vl,vr),ax,left,right))
            _,_,ax,left,right=min(choices,key=lambda a:a[:2])
            nodes.append(ax);todo.extend([(right,dep+1),(left,dep+1)])
        now=time.monotonic()
        if now-last>20:
            save('INCOMPLETE_CHECKPOINT');last=now
            print(json.dumps(dict(nodes=len(nodes),leaves=count,depth=maximum_depth,pending=len(todo),seconds=now-start)),flush=True)
    save('COMPLETE_PENDING_INDEPENDENT_REPLAY' if not todo else 'INCOMPLETE_BUDGET')
    print(json.dumps(dict(nodes=len(nodes),leaves=count,depth=maximum_depth,pending=len(todo),seconds=time.monotonic()-start)),flush=True)

if __name__=='__main__':main()
