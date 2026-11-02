#!/usr/bin/env python3
"""Exact four-variable exclusion for a good central square left of -1/10."""
from pathlib import Path
from fractions import Fraction as F
import sys,json,time,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import joint_five_interval as ar
D,V=ar.D,ar.V
Q=F(1105,256);GX=F(217,480);GY=F(221,600);EDGE=F(3,2)-GX
SIGNS=[(-1,-1),(-1,1),(1,-1),(1,1)]
ROOTS=[(F(4,5),F(13,12),F(1,10),F(29,60),tl,th,F(0),F(1))for signs in SIGNS for tl,th in[(F(0),F(1,4)),(F(1,4),F(1))]]
def hk(t):
 den=(1+t.square()).sqrt();return(1+t)/(2*den),(1-t)/(2*den),1/den,t/den,den

def top(x,t,sign):
 h,k,a,b,den=hk(t);edge=(Q-(x+h).square()).sqrt()
 # All centers are on the negative x side; reflect the physical frame.
 if sign==-1:return ar.minimum([ar.rho,(Q-(x+k).square()).sqrt()-h,edge+k])
 return ar.minimum([ar.rho,(Q-(x-k).square()).sqrt()-h,edge-k])

def expression(box,signs,chart):
 vals=[]
 for j in range(4):
  grad=[0]*4;grad[j]=1;vals.append(D(V(box[2*j],box[2*j+1]),grad))
 z,v,t,s=vals;sl,sp=signs
 hl,kl,al,bl,dl=hk(t);hp,kp,ap,bp,dp=hk(s)
 horizontal=EDGE-z
 # Keep the actual physical chirality. Negative-horizontal upward axes
 # have the extra gx penalty and are dominated by the top facet.
 if sl==-1:loss=ar.maximum([D(0),t*(kl+horizontal)])
 elif chart==0:loss=D(0)
 else:loss=ar.maximum([D(0),(horizontal-kl)/t])
 lowl=ar.maximum([D(F(31,50)),GY+hl-loss]);lowp=hp+F(1,10)
 highl=top(z,t,sl);highp=top(v,s,sp);dx=z-v
 dylo=ar.maximum([lowp-highl,-dx]);dyhi=ar.minimum([highp-lowl,dx])
 support=(1+(al*ap+sl*sp*bl*bp).abs()+(sp*al*bp-sl*bl*ap).abs())/2
 axis=[]
 for a,b,sg in[(al,bl,sl),(ap,bp,sp)]:
  axis.extend([a*dx+sg*b*(dyhi if sg==1 else dylo),b*dx-sg*a*(dylo if sg==1 else dyhi)])
 return ar.minimum([highl-lowl,highp-lowp,dyhi-dylo,dx-1/(4*hl)-1/(4*hp),ar.maximum(axis)-support])

def ceiling(box,signs,chart):
 wide=expression(box,signs,chart);mids=[(box[2*j]+box[2*j+1])/2 for j in range(4)]
 at=expression(tuple(x for m in mids for x in(m,m)),signs,chart).v
 for j,m in enumerate(mids):at+=wide.g[j]*V(box[2*j]-m,box[2*j+1]-m)
 return min(wide.v.h,at.h),wide

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--max-nodes',type=int,default=100000);ap.add_argument('--resume',action='store_true');args=ap.parse_args()
 out=HERE/'low_endpoint_central_position_cover.json';nodes=[{'box':list(map(str,b)),'signs':list(SIGNS[i//2]),'chart':i%2}for i,b in enumerate(ROOTS)];stack=[(i,b,0)for i,b in reversed(list(enumerate(ROOTS)))];processed=closed=0;start=last=time.monotonic()
 if args.resume:
  d=json.loads(out.read_text());nodes=d['nodes'];processed=d['processed'];closed=d['closed'];stack=[(r['node'],tuple(map(F,nodes[r['node']]['box'])),r['depth'])for r in d['pending']]
 stop=processed+args.max_nodes
 def save(status):out.write_text(json.dumps({'type':'low_endpoint_central_position_scalar_cover_v1','proof_status':status,'Q':str(Q),'gx':str(GX),'gy':str(GY),'root_indices':list(range(8)),'nodes':nodes,'closed':closed,'processed':processed,'remaining':len(stack),'pending':[{'node':i,'depth':dep}for i,b,dep in stack]},separators=(',',':'))+'\n')
 while stack and processed<stop:
  i,box,dep=stack.pop();processed+=1;sg=nodes[i]['signs'];ch=nodes[i]['chart'];upper,wide=ceiling(box,sg,ch)
  if upper<0:nodes[i].update(terminal='strict_scalar',upper=str(F(upper,ar.S)));closed+=1
  else:
   mids=[(box[2*j]+box[2*j+1])/2 for j in range(4)];point=expression(tuple(x for m in mids for x in(m,m)),sg,ch).v.h
   if point>=0:
    nodes[i]['unresolved_point']=str(F(point,ar.S));stack.append((i,box,dep));save('incomplete_unresolved_point');print('UNRESOLVED',sg,ch,list(map(float,mids)),float(F(point,ar.S)),flush=True);return
   if dep>=100:stack.append((i,box,dep));save('incomplete_depth_limit');return
   dim=max(range(4),key=lambda j:float(box[2*j+1]-box[2*j])*max(abs(wide.g[j].l),abs(wide.g[j].h))/ar.S)
   lo,hi=list(box),list(box);lo[2*dim+1]=mids[dim];hi[2*dim]=mids[dim];li=len(nodes);ri=li+1
   nodes.extend([{'box':list(map(str,lo)),'signs':sg,'chart':ch},{'box':list(map(str,hi)),'signs':sg,'chart':ch}]);nodes[i].update(split=dim,children=[li,ri]);stack.extend([(ri,tuple(hi),dep+1),(li,tuple(lo),dep+1)])
  now=time.monotonic()
  if now-last>25:save('incomplete_checkpoint');print('CENTRAL X',processed,closed,len(stack),'seconds',round(now-start,1),flush=True);last=now
 save('producer_complete_pending_independent_replay'if not stack else'incomplete_node_budget');print('FINISH',processed,closed,len(stack),'seconds',round(time.monotonic()-start,1),flush=True)
if __name__=='__main__':main()
