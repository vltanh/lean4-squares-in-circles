#!/usr/bin/env python3
"""Exact producer for the widened outer envelopes, pending separate replay."""
from pathlib import Path
from fractions import Fraction as F
import argparse,json,sys,time
import wider_outer_support as discover
sys.path.insert(0,str(discover.BASE))
import joint_five_interval as ar

D,V=ar.D,ar.V
EPS=F(1,80)
EBOX=(F(89,60),F(91,60),F(-1,8),F(1,8))
SBOX=(F(0),F(13,12),F(3,5),F(91,60))

def initial(owner,chart):
    bound=F(1) if owner=='S' else F(7,100)
    return [(-bound,bound,F(-57),F(24))]

def free_component(vec,costs,box,limited=False,faces=None,den=4096):
    if faces is None:faces=[0,0,0,0]
    lam=[F(v,den)for v in faces]
    xl,xh,yl,yh=box
    moved=[vec[0]+lam[0]-lam[1],vec[1]+lam[2]-lam[3]]
    toll=-xl*lam[0]+xh*lam[1]-yl*lam[2]+yh*lam[3]
    p=ar.free_sum(costs,limited)
    boxval=((xl+xh)*vec[0]+(yl+yh)*vec[1]+(xh-xl)*vec[0].abs()+(yh-yl)*vec[1].abs())/2
    return ar.minimum([ar.rad*ar.norm(moved)-ar.free_sum([moved,*costs],limited)+toll,
                       ar.rho*ar.norm(moved)-p+toll,boxval-p])

def expression(box,cert,owner,chart):
    w=D(V(box[0],box[1]),[1,0,0,0]);z=D(V(box[2],box[3]),[0,1,0,0])
    if chart=='up':n=[-w,D(1)];axis=[D(1),w]
    else:n=[D(-1),w];axis=[D(1),-w]
    k=F(cert['k'],cert['den']);b=F(27,2)
    ve=[46-k*n[0],-k*n[1]];vs=[b+k*n[0],b*z+k*n[1]]
    ec=[[D(46),D(0)],ar.scale(k,n)];sc=[[D(b),b*z],ar.scale(k,n)]
    if owner=='S':
        ep=free_component(ve,ec,EBOX,True)
        sh=ar.center_with_faces(vs,axis,SBOX,cert['faces'],cert['den'])-ar.fixed_sum(sc,axis)
    else:
        ep=ar.center_with_faces(ve,axis,EBOX,cert['efaces'],cert['den'])-ar.fixed_sum(ec,axis)
        sh=free_component(vs,sc,SBOX,faces=cert['faces'],den=cert['den'])
    target=F(211,4)+F(29,2)*z+F(3,2)*ar.minimum([D(0),ar.maximum([D(-1),z])])
    return ep+sh-target

def ceiling(box,cert,owner,chart):
    full=expression(box,cert,owner,chart)
    mids=[(box[0]+box[1])/2,(box[2]+box[3])/2]
    center=expression(tuple(x for m in mids for x in(m,m)),cert,owner,chart).v
    for j,m in enumerate(mids):center+=full.g[j]*V(box[2*j]-m,box[2*j+1]-m)
    return min(full.v.h,center.h),full

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--owner',choices=['E','S'],required=True);ap.add_argument('--chart',choices=['up','left'],required=True);ap.add_argument('--max-nodes',type=int,default=100000);ap.add_argument('--resume',action='store_true');args=ap.parse_args()
    owner,chart=args.owner,args.chart;roots=initial(owner,chart)
    out=Path(__file__).with_name(f'wider_outer_{owner}_{chart}_cover.json')
    nodes=[{'box':list(map(str,box))}for box in roots];certs=[];lookup={}
    stack=[(i,box,None,0)for i,box in enumerate(roots)];processed=closed=0;started=last=time.monotonic()
    def ci(cert):
        key=json.dumps(cert,sort_keys=True,separators=(',',':'))
        if key not in lookup:lookup[key]=len(certs);certs.append(cert)
        return lookup[key]
    if args.resume:
        old=json.loads(out.read_text());assert old['owner']==owner and old['chart']==chart
        nodes,certs=old['nodes'],old['certificates'];lookup={json.dumps(c,sort_keys=True,separators=(',',':')):i for i,c in enumerate(certs)}
        processed,closed=old['processed'],old['closed']
        stack=[(p['node'],tuple(map(F,nodes[p['node']]['box'])),None if p['seed']is None else certs[p['seed']],p['depth'])for p in old['pending']]
    stop=processed+args.max_nodes
    def save(status):
        pending=[{'node':i,'seed':None if c is None else ci(c),'depth':dep}for i,box,c,dep in stack]
        data={'type':'wider_outer_support_cover_v1','proof_status':status,'owner':owner,'chart':chart,'Q':'1105/256','T':'211/4','b':'27/2','local_epsilon':'1/80','shoulder_box':list(map(str,SBOX)),'root_indices':[0],'nodes':nodes,'certificates':certs,'pending':pending,'remaining':len(stack),'processed':processed,'closed':closed}
        out.write_text(json.dumps(data,separators=(',',':'))+'\n')
    while stack and processed<stop:
        idx,box,parent,depth=stack.pop();processed+=1
        if chart=='up' and -EPS<=box[0]<=box[1]<=EPS and -EPS<=box[2]<=box[3]<=EPS:
            nodes[idx]['terminal']='local_unboxed_1_80';closed+=1;continue
        mids=[(box[0]+box[1])/2,(box[2]+box[3])/2];point=tuple(v for m in mids for v in(m,m))
        best=parent;up=full=None
        if best is not None:up,full=ceiling(box,best,owner,chart)
        if up is None or up>=0:
            _,candidate=discover.proposal(*map(float,mids),chart,owner)
            candidate_up,candidate_full=ceiling(box,candidate,owner,chart)
            if up is None or candidate_up<up:best,up,full=candidate,candidate_up,candidate_full
            if up>=0:
                pc=expression(point,candidate,owner,chart).v.h
                pp=expression(point,best,owner,chart).v.h
                if min(pc,pp)>=0:
                    nodes[idx]['unresolved_point']=str(F(min(pc,pp),ar.S));stack.append((idx,box,best,depth));save('incomplete_unresolved_point');print('UNRESOLVED',owner,chart,box,float(F(min(pc,pp),ar.S)),flush=True);return
        if up<0:
            nodes[idx]['certificate']=ci(best);nodes[idx]['upper']=str(F(up,ar.S));closed+=1
        else:
            if depth>=70:stack.append((idx,box,best,depth));save('incomplete_depth_limit');return
            dim=max(range(2),key=lambda j:float(box[2*j+1]-box[2*j])*max(abs(full.g[j].l),abs(full.g[j].h))/ar.S)
            lo,hi=list(box),list(box);lo[2*dim+1]=mids[dim];hi[2*dim]=mids[dim]
            li=len(nodes);ri=li+1;nodes.extend([{'box':list(map(str,lo))},{'box':list(map(str,hi))}]);nodes[idx].update(split=dim,children=[li,ri]);stack.extend([(ri,tuple(hi),best,depth+1),(li,tuple(lo),best,depth+1)])
        now=time.monotonic()
        if now-last>25:
            save('incomplete_checkpoint');print('WIDER',owner,chart,'nodes',processed,'closed',closed,'pending',len(stack),'seconds',round(now-started,1),flush=True);last=now
    save('producer_complete_pending_independent_replay'if not stack else'incomplete_node_budget')
    print('FINISH',owner,chart,'nodes',processed,'closed',closed,'pending',len(stack),'seconds',round(time.monotonic()-started,1),flush=True)

if __name__=='__main__':main()
