"""Untrusted dyadic discovery: the upper original beside a bracketed wide main."""
from fractions import Fraction as F
from pathlib import Path
import argparse,json,time
import verify_weak_middle_side_eight as q
ROOT=((F(1,2),F(13,20)),(F(0),F(1)),(F(29,60),F(13,12)))

def low_main(z,sign):
    f=-F(2,3)*z+max(F(0),min((z-F(1,2))/6,(F(27,50)-z)/3))+F(1,400)
    return f+(z-F(1,2))/4 if sign>0 else f

def lower(box):
    h,t,X=[q.I(*a) for a in box];m=q.shape_h(h);s=q.shape(t)
    blo=(h-F(61,60)).lo;bhi=(F(1,60)-m[4]).hi
    if blo>bhi:return blo-bhi
    d=-X-q.I(blo,bhi,True);c=(q.CSTAR+F(32,9)*q.eta_h(h)).lo
    heights=[]
    for sm in (-1,1):
        base_main=q.down(low_main(F(h.hi,q.SCALE),sm))
        for ss in (-1,1):
            base=base_main+q.main_clearance(s,ss,m,sm,d)
            heights.append(q.endpoint_lower(s,-ss,X,base,c))
    return min(heights)-q.up(F(3,5))

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
    out={'type':'bracketed_wide_main_upper_side_v1','status':'COMPLETE_PENDING_INDEPENDENT_REPLAY' if not todo else 'INCOMPLETE_DISCOVERY',
         'root':[[str(a),str(b)] for a,b in ROOT],'nodes':nodes,'leaves':leaves,'maximum_depth':depth,'remaining':len(todo),
         'pending':[[[[str(a),str(b)] for a,b in box],d] for box,d in todo],
         'least_dyadic_reserve':str(F(least,q.SCALE)) if least is not None else None,'seconds':time.monotonic()-begin}
    Path(__file__).with_name('bracketed_side_upper_height_candidate.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('nodes','pending')},indent=2),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--limit',type=int,default=500000);a=p.parse_args();run(a.limit)
