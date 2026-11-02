#!/usr/bin/env python3
"""Independent exact replay of the central singleton-floor scalar cover."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys,time
HERE=Path(__file__).resolve().parent
BASE=HERE if(HERE/'verify_joint_five_dyadic.py').is_file()else HERE.parent/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(BASE))
import verify_joint_five_dyadic as ar

def square_root(value):
    rad=value.x.sqrt();assert rad.lo>0
    return ar.A(rad,[p/(2*rad)for p in value.der])

def frame(t):
    den=ar.length([ar.A(1),t])
    return(1+t)/(2*den),(1-t)/(2*den),1/den,t/den,den

def top_height(x,t):
    h,k,a,b,den=frame(t);q=F(1105,256)
    edge=square_root(q-(x+h).sq())
    first=ar.least([square_root(q-(x+k).sq())-h,edge+k])
    second=ar.least([square_root(q-(x-k).sq())-h,edge-k])
    return ar.least([ar.CENTER_RADIUS,ar.greatest([first,second])])

def evaluate(box):
    parameters=[]
    for j in range(4):
        derivative=[0]*4;derivative[j]=1
        parameters.append(ar.A(ar.I(box[2*j],box[2*j+1]),derivative))
    v,w,s,t=parameters
    h1,k1,a1,b1,d1=frame(s);h2,k2,a2,b2,d2=frame(t)
    delta=F(331,20000);base=F(269,310)-F(1,1000)
    loss1=ar.greatest([ar.A(0),s*(k1+v+delta),(v+delta-k1)/s])
    loss2=ar.greatest([ar.A(0),t*(k2-w+delta)])
    floor1,floor2=base-loss1,base-loss2
    low1,low2=h1+floor1,h2+floor2
    high1,high2=top_height(v,s),top_height(w,t)
    dx=v+w;dy=ar.greatest([ar.A(0),high2-low1])
    support=(1+(1+s*t+(s-t).absolute())/(d1*d2))/2
    axis_gap=ar.greatest([a1*dx+b1*dy,b1*dx+a1*dy,a2*dx+b2*dy,b2*dx+a2*dy])-support
    return ar.least([F(9,20)-floor1,high1-low1,high2-low2,high2-low1,dx-F(29,60),axis_gap])

def upper(box):
    full=evaluate(box);m=[(box[2*j]+box[2*j+1])/2 for j in range(4)]
    center=evaluate(tuple(v for mm in m for v in(mm,mm))).x
    for j,mm in enumerate(m):center+=full.der[j]*ar.I(box[2*j]-mm,box[2*j+1]-mm)
    return F(min(full.x.hi,center.hi),ar.SCALE)

def verify(data,progress=False):
    assert data['type']=='central_singleton_floor_scalar_cover_v1'
    assert data['Q']=='1105/256'and data['delta']=='331/20000'
    assert data['proof_status']=='producer_complete_pending_independent_replay'
    assert data['root_indices']==[0]and data['remaining']==0 and data['pending']==[]
    root=(F(0),F(29,60),F(0),F(29,60),F(1,1000),F(1),F(0),F(1))
    nodes=data['nodes'];stack=[(0,root,0)];seen=set();leaves=depthmax=0;largest=None;start=last=time.monotonic()
    while stack:
        i,expected,depth=stack.pop();assert isinstance(i,int)and 0<=i<len(nodes)and i not in seen
        seen.add(i);depthmax=max(depthmax,depth);node=nodes[i];box=tuple(map(F,node['box']));assert box==expected
        if 'children'in node:
            assert'terminal'not in node and'upper'not in node
            dim=node['split'];assert isinstance(dim,int)and 0<=dim<4
            kids=node['children'];assert len(kids)==2 and kids[0]!=kids[1]
            mid=(box[2*dim]+box[2*dim+1])/2;left,right=list(box),list(box);left[2*dim+1]=mid;right[2*dim]=mid
            stack.extend([(kids[0],tuple(left),depth+1),(kids[1],tuple(right),depth+1)])
        else:
            assert node['terminal']=='strict_scalar'
            u=upper(box);assert u<0,(i,str(u),box)
            leaves+=1;largest=u if largest is None else max(largest,u)
        now=time.monotonic()
        if progress and now-last>=25:
            print('SINGLETON REPLAY',leaves,'seconds',round(now-start,1),flush=True);last=now
    assert len(seen)==len(nodes)and leaves==data['closed']
    return {'nodes':len(seen),'strict_interval_leaves':leaves,'maximum_depth':depthmax,'largest_replayed_upper':str(largest),'complete':True,'seconds':time.monotonic()-start}

def main():
    path=Path(sys.argv[1]);raw=path.read_bytes();report=verify(json.loads(raw),True)
    report.update(proof_status='independent_central_singleton_floor_replay_passed',certificate_sha256=hashlib.sha256(raw).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),arithmetic_sha256=hashlib.sha256(Path(ar.__file__).read_bytes()).hexdigest())
    path.with_name(path.stem+'_replay.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)

if __name__=='__main__':main()
