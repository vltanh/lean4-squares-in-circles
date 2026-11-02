"""Exact two-variable outer support envelopes with rational row multipliers."""
from pathlib import Path
from fractions import Fraction as F
import argparse,json,math,time
from scipy.optimize import minimize_scalar
import outer_scalar_support as base
from outer_scalar_support import scalar

D,V,S=base.D,base.V,base.S
K,B,T,EPS=base.K,base.B,base.T,F(1,80)
GOALS=('linear_negative','linear_positive','orthogonal_negative')


def roots(goal):
    if goal=='orthogonal_negative':return [(F(-2,3),F(6),F(1,6),F(6))]
    return [(F(-2,3),-EPS,F(0),F(6)),(EPS,F(6),F(0),F(6)),(-EPS,EPS,EPS,F(6))]


def expression(box,cert,goal):
    t=D(V(box[2],box[3]),[0,1,0,0])
    if goal=='linear_positive':
        return base.expression(box,cert,'positive')+(B-F(29,2))*t+B*(base.norm([D(1),t])-1)
    raw=base.expression(box,cert,'negative')
    if goal=='linear_negative':return raw+(16-B)*t
    return raw+B/2+B*(base.rad-1)*t-B*base.norm([D(1),t])-(t-1/t)/2


def ceiling(box,cert,goal):
    full=expression(box,cert,goal);mids=[(box[0]+box[1])/2,(box[2]+box[3])/2]
    at=expression(tuple(v for m in mids for v in(m,m)),cert,goal).v
    for j,m in enumerate(mids):at+=full.g[j]*V(box[2*j]-m,box[2*j+1]-m)
    return min(full.v.h,at.h),full


def target(t,goal):
    if goal=='linear_positive':return float(T)+14.5*t
    if goal=='linear_negative':return float(T)-16*t
    return float(T)-float(B)/2-float(B)*math.sqrt(1105/256)*t+float(B)*math.sqrt(1+t*t)+(t-1/t)/2


def certificate(w,t,k,goal):
    return base.certificate(w,t,k,'positive'if goal=='linear_positive'else'negative')


def proposal(w,t,goal,normalized=True):
    z=t if goal=='linear_positive'else -t
    gap=lambda k:scalar(w,z,k)-target(t,goal)
    objective=(lambda k:gap(k)/(20+k))if normalized else gap
    fit=minimize_scalar(objective,bounds=(0,128),method='bounded',options={'xatol':1e-8,'maxiter':100})
    ks=[0.,float(K),float(K)/(1+max(w,0)),float(B)*t,float(fit.x)]
    if w>0:ks.append(min(128,float(B)/w))
    best=min(ks,key=objective)
    return certificate(w,t,best,goal)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--goal',choices=GOALS,required=True);ap.add_argument('--max-nodes',type=int,default=100000);ap.add_argument('--resume',action='store_true');args=ap.parse_args();goal=args.goal
    out=Path(__file__).with_name(f'outer_R_{goal}_cover.json');initial=roots(goal)
    nodes=[{'box':list(map(str,x))}for x in initial];certs=[];ct={};stack=[(j,x,None,0)for j,x in reversed(list(enumerate(initial)))];processed=closed=0;started=last=time.monotonic()
    def ci(c):
        key=json.dumps(c,sort_keys=True,separators=(',',':'))
        if key not in ct:ct[key]=len(certs);certs.append(c)
        return ct[key]
    if args.resume:
        old=json.loads(out.read_text());assert old['goal']==goal
        nodes=old['nodes'];certs=old['certificates'];ct={json.dumps(c,sort_keys=True,separators=(',',':')):i for i,c in enumerate(certs)};processed=old['processed'];closed=old['closed']
        stack=[(p['node'],tuple(map(F,nodes[p['node']]['box'])),None if p['seed']is None else certs[p['seed']],p['depth'])for p in old['pending']]
    stop=processed+args.max_nodes
    def save(status):
        pending=[{'node':j,'seed':None if c is None else ci(c),'depth':dep}for j,box,c,dep in stack]
        data={'type':'outer_R_scalar_family_cover_v1','proof_status':status,'goal':goal,'Q':'1105/256','T':'211/4','b':'27/2','local_epsilon':'1/80','root_indices':list(range(len(initial))),'nodes':nodes,'certificates':certs,'pending':pending,'remaining':len(stack),'processed':processed,'closed':closed}
        out.write_text(json.dumps(data,separators=(',',':'))+'\n')
    while stack and processed<stop:
        idx,box,parent,depth=stack.pop();processed+=1
        if goal!='orthogonal_negative'and -EPS<=box[0]<=box[1]<=EPS and 0<=box[2]<=box[3]<=EPS:
            nodes[idx]['terminal']='local_linear_1_80';closed+=1;continue
        mids=[(box[0]+box[1])/2,(box[2]+box[3])/2];w,t=map(float,mids);best=None;up=full=None;attempts=[]
        def consider(c):
            nonlocal best,up,full
            attempts.append(c);u,ff=ceiling(box,c,goal)
            if up is None or u<up:best,up,full=c,u,ff
        if parent is not None:consider(parent)
        if up is None or up>=0:consider(certificate(w,t,float(K)/(1+max(w,0)),goal))
        if up>=0:consider(certificate(w,t,float(K),goal))
        if up>=0:consider(proposal(w,t,goal,True))
        if up>=0:
            point=tuple(v for m in mids for v in(m,m));at=expression(point,best,goal).v.h
            if at>=0:
                consider(proposal(w,t,goal,False));at=min(expression(point,c,goal).v.h for c in attempts)
                if at>=0:
                    nodes[idx]['unresolved_point']={'value':str(F(at,S))};stack.append((idx,box,best,depth));save('incomplete_unresolved_point');print('UNRESOLVED',goal,box,float(F(at,S)),flush=True);return
        if up<0:nodes[idx]['certificate']=ci(best);nodes[idx]['upper']=str(F(up,S));closed+=1
        else:
            if depth>=70:stack.append((idx,box,best,depth));save('incomplete_depth_limit');return
            dim=max(range(2),key=lambda j:float(box[2*j+1]-box[2*j])*max(abs(full.g[j].l),abs(full.g[j].h))/S)
            left=list(box);right=list(box);left[2*dim+1]=mids[dim];right[2*dim]=mids[dim];li=len(nodes);ri=li+1;nodes.extend([{'box':list(map(str,left))},{'box':list(map(str,right))}]);nodes[idx].update(split=dim,children=[li,ri]);stack.extend([(ri,tuple(right),best,depth+1),(li,tuple(left),best,depth+1)])
        now=time.monotonic()
        if now-last>25:save('incomplete_checkpoint');print('SCALAR',goal,'nodes',processed,'leaves',closed,'pending',len(stack),'seconds',round(now-started,1),flush=True);last=now
    save('producer_complete_pending_independent_replay'if not stack else'incomplete_node_budget');print('FINISH',goal,'nodes',processed,'leaves',closed,'pending',len(stack),'seconds',round(time.monotonic()-started,1),flush=True)


if __name__=='__main__':main()
