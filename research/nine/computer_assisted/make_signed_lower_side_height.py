"""Untrusted exact-dyadic discovery for the signed left-main height bound."""
from fractions import Fraction as F
from pathlib import Path
import argparse,json,time
import verify_weak_middle_side_eight as q

ROOT=((F(1,2),F(13,20)),(F(0),F(1)),(F(29,60),F(13,12)))

def target(z):
    return -F(2,3)*z+max(F(0),min((z-F(1,2))/6,(F(27,50)-z)/3))+F(1,400)+(z-F(1,2))/4

def lower(box):
    h,t,X=[q.I(*a) for a in box];m=q.shape_h(h);s=q.shape(t)
    blo=(h-F(61,60)).lo;bhi=(F(1,60)-m[4]).hi
    if blo>bhi:return blo-bhi
    d=-X-q.I(blo,bhi,True)
    ceiling=q.up(target(F(h.lo,q.SCALE)))
    return min(q.main_clearance(s,-ss,m,-1,d)-q.corner_upper(s,X,ss)-ceiling for ss in (-1,1))

def run(limit):
    begin=time.monotonic();todo=[(ROOT,0)];nodes=[];leaves=0;depth=0;least=None
    weights=(F(20,3),F(1),F(5,3))
    while todo and len(nodes)<limit:
        box,d=todo.pop();depth=max(depth,d);reserve=lower(box)
        if reserve>0:
            nodes.append(3);leaves+=1;least=reserve if least is None else min(least,reserve)
        else:
            axis=max(range(3),key=lambda j:(box[j][1]-box[j][0])*weights[j])
            mid=sum(box[axis])/2;a=list(box);b=list(box)
            a[axis]=(box[axis][0],mid);b[axis]=(mid,box[axis][1])
            nodes.append(axis);todo.extend(((tuple(b),d+1),(tuple(a),d+1)))
        if len(nodes)%10000==0:print(json.dumps({'nodes':len(nodes),'leaves':leaves,'pending':len(todo),'depth':depth,'seconds':time.monotonic()-begin}),flush=True)
    out={'type':'signed_left_main_height_v1','status':'COMPLETE_PENDING_INDEPENDENT_REPLAY' if not todo else 'INCOMPLETE_DISCOVERY',
         'root':[[str(a),str(b)] for a,b in ROOT],'nodes':nodes,'leaves':leaves,'maximum_depth':depth,'remaining':len(todo),
         'pending':[[[[str(a),str(b)] for a,b in box],d] for box,d in todo],
         'least_dyadic_reserve':str(F(least,q.SCALE)) if least is not None else None,'seconds':time.monotonic()-begin}
    Path(__file__).with_name('signed_lower_side_height_candidate.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('nodes','pending')},indent=2),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--limit',type=int,default=500000);a=p.parse_args();run(a.limit)
