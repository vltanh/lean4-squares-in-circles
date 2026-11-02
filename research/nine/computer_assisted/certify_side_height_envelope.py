"""Complete exact discovery table for yM > -2hM/3 with a lower side unit.

This producer uses an existing dyadic kernel. Acceptance requires a separate
reconstruction; incomplete checkpoints never assert the theorem.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse,json,sys,time
HERE=Path(__file__).resolve().parent
BASE=HERE if (HERE/'verify_joint_five_dyadic.py').exists() else HERE.parent/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(BASE))
from verify_joint_five_dyadic import I,SCALE

ROOT=(F(1,2),F(13,20),F(0),F(1),F(29,60),F(13,12))
Q=I(F(1105,256));HALF=I(F(1,2));RHO=I(F(91,60))
BUMP=False
SHIFT=False

def framed_h(h):
    k=(HALF-h.sq()).sqrt()
    return k,h+k,h-k

def framed_t(t):
    a=1/(1+t.sq()).sqrt();b=t*a
    return a,b,(a+b)/2,(a-b)/2

def lower(box):
    h=I(box[0],box[1]);t=I(box[2],box[3]);x=I(box[4],box[5])
    kl,al,bl=framed_h(I(box[0]));ku,au,bu=framed_h(I(box[1]))
    km=I.raw(ku.lo,kl.hi);am=I.raw(au.lo,al.hi);bm=I.raw(bl.lo,bu.hi)
    aa,ba,ha,ka=framed_t(I(box[2]));ab,bb,hb,kb=framed_t(I(box[3]))
    a=I.raw(ab.lo,aa.hi);b=I.raw(ba.lo,bb.hi)
    hs=I.raw(ha.lo,hb.hi);ks=I.raw(kb.lo,ka.hi)
    g=1/(4*h)
    # Both original main-center bounds, with either displacement sign.
    d=max((x-g+F(1,60)).hi,(F(61,60)-h-x).hi)
    dd=I.raw(d,d)
    s=max((1+(h-hs).abs()).lo,(HALF+km*a+h*b).lo,(HALF+h*a-km*b).lo)
    ss=I.raw(s,s)
    def quotient(numerator,denominator):
        assert numerator.lo>0
        if denominator.hi==0:return 100*SCALE
        return numerator.lo*SCALE//denominator.hi
    axis=min(quotient(ss-am*dd,bm),quotient(ss-bm*dd,am),
             quotient(ss-a*dd,b),quotient(ss-b*dd,a))
    chord=(ss.sq()-dd.sq()).sqrt().lo
    delta=g-dd
    proxy=min(hs.lo,quotient(HALF+delta*b,a),quotient(HALF+delta*a,b))
    inset=g.lo+proxy
    clear=max(axis,chord,inset)
    plus=min(((Q-(x+ks).sq()).sqrt()-hs).hi,(ks+(Q-(x+hs).sq()).sqrt()).hi)
    minus=min(((Q-(x+hs).sq()).sqrt()-ks).hi,((Q-(x-ks).sq()).sqrt()-hs).hi)
    top=min(max(plus,minus),RHO.hi)
    result=clear-top+(F(2,3)*h).lo
    if BUMP:
        bump=max(0,min(((h-F(1,2))/6).hi,((F(27,50)-h)/3).hi,I(F(1,225)).hi))
        result-=bump
    if SHIFT:result-=I(F(1,400)).hi
    return result

def children(box,axis):
    m=(box[2*axis]+box[2*axis+1])/2
    left,right=list(box),list(box);left[2*axis+1]=m;right[2*axis]=m
    return tuple(left),tuple(right)

def main():
    global BUMP,SHIFT
    ap=argparse.ArgumentParser();ap.add_argument('--max-nodes',type=int,default=400000);ap.add_argument('--bump',action='store_true');ap.add_argument('--shift',action='store_true');args=ap.parse_args()
    BUMP=args.bump
    SHIFT=args.shift
    assert not SHIFT or BUMP
    nodes=[];stack=[(ROOT,0)];leaves=0;depth=0;least=None;start=last=time.monotonic()
    target='bump_plus_1_400'if SHIFT else'bump'if BUMP else'linear'
    path=Path(__file__).with_name('side_height_envelope_'+target+'_candidate.json')
    def save(status):
        path.write_text(json.dumps(dict(type='side_height_envelope_prefix_v1',target=target,status=status,root=list(map(str,ROOT)),nodes=nodes,leaves=leaves,maximum_depth=depth,remaining=len(stack),least_lower=None if least is None else str(F(least,SCALE)),pending=[dict(box=list(map(str,b)),depth=d)for b,d in stack]),separators=(',',':'))+'\n')
    while stack and len(nodes)<args.max_nodes:
        box,dep=stack.pop();depth=max(depth,dep);value=lower(box)
        if value>0:
            nodes.append(3);leaves+=1;least=value if least is None else min(least,value)
        else:
            if dep>=60:
                stack.append((box,dep));save('INCOMPLETE_DEPTH');return
            choices=[]
            for ax in range(3):
                left,right=children(box,ax);ll,rr=lower(left),lower(right)
                score=min(ll,int(.01*SCALE))+min(rr,int(.01*SCALE))
                choices.append((score,min(ll,rr),ax,left,right))
            _,_,ax,left,right=max(choices,key=lambda q:q[:2])
            nodes.append(ax);stack.extend([(right,dep+1),(left,dep+1)])
        now=time.monotonic()
        if now-last>20:
            save('INCOMPLETE_CHECKPOINT');print(json.dumps(dict(nodes=len(nodes),leaves=leaves,depth=depth,pending=len(stack),seconds=now-start)),flush=True);last=now
    save('COMPLETE_PENDING_INDEPENDENT_REPLAY'if not stack else'INCOMPLETE_BUDGET')
    print(json.dumps(dict(nodes=len(nodes),leaves=leaves,depth=depth,pending=len(stack),seconds=time.monotonic()-start)),flush=True)

if __name__=='__main__':main()
