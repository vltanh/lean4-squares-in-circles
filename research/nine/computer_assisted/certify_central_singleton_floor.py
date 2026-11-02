#!/usr/bin/env python3
"""Exact producer for the central singleton-floor obstruction."""
from pathlib import Path
from fractions import Fraction as F
import sys,json,time,argparse
HERE=Path(__file__).resolve().parent
BASE=HERE if(HERE/'joint_five_interval.py').is_file()else HERE.parent/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(BASE))
import joint_five_interval as ar
D,V=ar.D,ar.V
Q=F(1105,256);L=F(29,60);DELTA=F(331,20000);R=F(269,310)-F(1,1000)
ROOT=(F(0),L,F(0),L,F(1,1000),F(1),F(0),F(1))

def hk(t):
 den=(1+t.square()).sqrt()
 return(1+t)/(2*den),(1-t)/(2*den),1/den,t/den,den

def ymax(x,t):
 h,k,a,b,den=hk(t)
 outer=(Q-(x+h).square()).sqrt()
 plus=ar.minimum([(Q-(x+k).square()).sqrt()-h,outer+k])
 minus=ar.minimum([(Q-(x-k).square()).sqrt()-h,outer-k])
 return ar.minimum([ar.rho,ar.maximum([plus,minus])])

def expression(box):
 vv=[]
 for j in range(4):
  grad=[0]*4;grad[j]=1;vv.append(D(V(box[2*j],box[2*j+1]),grad))
 v,w,tg,th=vv
 hg,kg,ag,bg,dg=hk(tg);hh,kh,ah,bh,dh=hk(th)
 lg=ar.maximum([D(0),tg*(kg+v+DELTA),(v+DELTA-kg)/tg])
 lh=ar.maximum([D(0),th*(kh-w+DELTA)])
 fg=R-lg;fh=R-lh;yg=hg+fg;yh=hh+fh
 mg=ymax(v,tg);mh=ymax(w,th);span=v+w
 dy=ar.maximum([D(0),mh-yg])
 sigma=(1+(1+tg*th+(tg-th).abs())/(dg*dh))/2
 sep=ar.maximum([ag*span+bg*dy,bg*span+ag*dy,ah*span+bh*dy,bh*span+ah*dy])-sigma
 return ar.minimum([F(9,20)-fg,mg-yg,mh-yh,mh-yg,span-L,sep])

def ceiling(box):
 wide=expression(box);mids=[(box[2*j]+box[2*j+1])/2 for j in range(4)]
 at=expression(tuple(t for m in mids for t in(m,m))).v
 for j,m in enumerate(mids):at+=wide.g[j]*V(box[2*j]-m,box[2*j+1]-m)
 return min(wide.v.h,at.h),wide

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--max-nodes',type=int,default=100000);ap.add_argument('--resume',action='store_true');args=ap.parse_args()
 out=HERE/'central_singleton_floor_cover.json';nodes=[{'box':list(map(str,ROOT))}];stack=[(0,ROOT,0)];closed=processed=0;start=last=time.monotonic()
 if args.resume:
  data=json.loads(out.read_text());nodes=data['nodes'];closed=data['closed'];processed=data['processed'];stack=[(d['node'],tuple(map(F,nodes[d['node']]['box'])),d['depth'])for d in data['pending']]
 stop=processed+args.max_nodes
 def save(status):
  out.write_text(json.dumps({'type':'central_singleton_floor_scalar_cover_v1','proof_status':status,'Q':str(Q),'delta':str(DELTA),'root_indices':[0],'nodes':nodes,'closed':closed,'processed':processed,'remaining':len(stack),'pending':[{'node':i,'depth':dep}for i,b,dep in stack]},separators=(',',':'))+'\n')
 while stack and processed<stop:
  idx,box,depth=stack.pop();processed+=1;upper,wide=ceiling(box)
  if upper<0:
   nodes[idx]['upper']=str(F(upper,ar.S));nodes[idx]['terminal']='strict_scalar';closed+=1
  else:
   mids=[(box[2*j]+box[2*j+1])/2 for j in range(4)];point=expression(tuple(v for m in mids for v in(m,m))).v.h
   if point>=0:
    nodes[idx]['unresolved_point']=str(F(point,ar.S));stack.append((idx,box,depth));save('incomplete_unresolved_point');print('UNRESOLVED',box,float(F(point,ar.S)),flush=True);return
   if depth>=80:stack.append((idx,box,depth));save('incomplete_depth_limit');return
   dim=max(range(4),key=lambda j:float(box[2*j+1]-box[2*j])*max(abs(wide.g[j].l),abs(wide.g[j].h))/ar.S)
   lo,hi=list(box),list(box);lo[2*dim+1]=mids[dim];hi[2*dim]=mids[dim]
   li=len(nodes);ri=li+1;nodes.extend([{'box':list(map(str,lo))},{'box':list(map(str,hi))}]);nodes[idx].update(split=dim,children=[li,ri]);stack.extend([(ri,tuple(hi),depth+1),(li,tuple(lo),depth+1)])
  now=time.monotonic()
  if now-last>25:
   save('incomplete_checkpoint');print('SINGLETON',processed,closed,len(stack),'seconds',round(now-start,1),flush=True);last=now
 save('producer_complete_pending_independent_replay'if not stack else'incomplete_node_budget');print('FINISH',processed,closed,len(stack),'seconds',round(time.monotonic()-start,1),flush=True)

if __name__=='__main__':main()
