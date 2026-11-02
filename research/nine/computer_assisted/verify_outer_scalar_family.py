#!/usr/bin/env python3
"""Independent exact replay for the extended R-owned scalar envelopes."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys,time
import verify_joint_five_dyadic as ar


def initial_boxes(goal):
    if goal=='orthogonal_negative':return [(F(-2,3),F(6),F(1,6),F(6))]
    return [(F(-2,3),F(-1,80),F(0),F(6)),
            (F(1,80),F(6),F(0),F(6)),
            (F(-1,80),F(1,80),F(1,80),F(6))]


def evaluate(interval,row,goal):
    assert goal in('linear_negative','linear_positive','orthogonal_negative')
    assert row['den']==4096 and isinstance(row['k'],int)and row['k']>=0
    assert len(row['faces'])==4 and all(isinstance(q,int)and q>=0 for q in row['faces'])
    w=ar.A(ar.I(interval[0],interval[1]),[1,0,0,0])
    t=ar.A(ar.I(interval[2],interval[3]),[0,1,0,0])
    z=t if goal=='linear_positive'else-t
    k=F(row['k'],4096);b=F(27,2)
    ev=[46+k*w,ar.A(-k)];sv=[b-k*w,k+b*z]
    endpoint=ar.unfixed_bound(ev,[[ar.A(46),ar.A(0)],[-k*w,ar.A(k)]],True,
                             (F(89,60),F(91,60),F(-1,8),F(1,8)))
    axis=[ar.A(1),w]
    shoulder=ar.boxed_bound(sv,axis,(F(23,30),F(13,12),F(25,32),F(21,16)),[F(q,4096)for q in row['faces']])
    shoulder-=ar.support_total([[ar.A(b),b*z],[-k*w,ar.A(k)]],axis)
    if goal=='linear_negative':target=F(211,4)-16*t
    elif goal=='linear_positive':target=F(211,4)+F(29,2)*t
    else:
        assert interval[0]<=interval[1]and F(1,6)<=interval[2]<=interval[3]<=6
        target=F(211,4)-b/2-b*ar.R*t+b*ar.length([ar.A(1),t])+(t-1/t)/2
    return endpoint+shoulder-target


def upper(interval,row,goal):
    full=evaluate(interval,row,goal);mid=[(interval[0]+interval[1])/2,(interval[2]+interval[3])/2]
    centered=evaluate(tuple(v for m in mid for v in(m,m)),row,goal).x
    for j,m in enumerate(mid):centered+=full.der[j]*ar.I(interval[2*j]-m,interval[2*j+1]-m)
    return F(min(full.x.hi,centered.hi),ar.SCALE)


def verify(data,allow=False,progress=False):
    assert data['type']=='outer_R_scalar_family_cover_v1'
    goal=data['goal'];assert goal in('linear_negative','linear_positive','orthogonal_negative')
    assert data['Q']=='1105/256'and data['T']=='211/4'and data['b']=='27/2'and data['local_epsilon']=='1/80'
    roots=initial_boxes(goal);assert data['root_indices']==list(range(len(roots)))
    nodes,certs=data['nodes'],data['certificates'];todo=[(i,box,0)for i,box in enumerate(roots)]
    seen=set();leaves=analytic=missing=depthmax=0;largest=None;started=last=time.monotonic()
    while todo:
        i,expected,depth=todo.pop();assert isinstance(i,int)and 0<=i<len(nodes)and i not in seen
        seen.add(i);depthmax=max(depthmax,depth);node=nodes[i];box=tuple(map(F,node['box']));assert box==expected
        if 'children'in node:
            assert 'certificate'not in node and'terminal'not in node
            dim=node['split'];assert isinstance(dim,int)and dim in(0,1)
            kids=node['children'];assert len(kids)==2 and kids[0]!=kids[1]
            m=(box[2*dim]+box[2*dim+1])/2;lo,hi=list(box),list(box);lo[2*dim+1]=m;hi[2*dim]=m
            todo.extend([(kids[0],tuple(lo),depth+1),(kids[1],tuple(hi),depth+1)])
        elif 'terminal'in node:
            assert goal!='orthogonal_negative'and node['terminal']=='local_linear_1_80'and'certificate'not in node
            assert -F(1,80)<=box[0]<=box[1]<=F(1,80)and 0<=box[2]<=box[3]<=F(1,80)
            analytic+=1
        elif 'certificate'in node:
            ci=node['certificate'];assert isinstance(ci,int)and 0<=ci<len(certs)
            bound=upper(box,certs[ci],goal);assert bound<0,(goal,i,str(bound),box)
            largest=bound if largest is None else max(largest,bound);leaves+=1
        else:
            assert allow,'unclosed scalar leaf';missing+=1
        now=time.monotonic()
        if progress and now-last>25:print('SCALAR REPLAY',goal,'leaves',leaves,'analytic',analytic,'open',missing,'seconds',round(now-started,1),flush=True);last=now
    assert len(seen)==len(nodes)and leaves+analytic==data['closed']
    if not allow:assert missing==0 and data['remaining']==0 and data['proof_status']=='producer_complete_pending_independent_replay'
    return {'goal':goal,'nodes':len(seen),'interval_leaves':leaves,'analytic_leaves':analytic,'unclosed_leaves':missing,'complete':missing==0,'max_depth':depthmax,'largest_replayed_upper':None if largest is None else str(largest),'seconds':time.monotonic()-started}


def main():
    path=Path(sys.argv[1]);raw=path.read_bytes();answer=verify(json.loads(raw),'--allow-incomplete'in sys.argv,True)
    answer.update({'sha256':hashlib.sha256(raw).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'arithmetic_sha256':hashlib.sha256(Path(ar.__file__).read_bytes()).hexdigest(),'proof_status':'independent_outer_scalar_replay_passed'if answer['complete']else'incomplete_scalar_checkpoint_replayed','arithmetic':'independent directed integer intervals,64fractional bits; exact rational root and split coverage'})
    path.with_name(path.stem+'_verification_report.json').write_text(json.dumps(answer,indent=2)+'\n');print(json.dumps(answer),flush=True)


if __name__=='__main__':main()
