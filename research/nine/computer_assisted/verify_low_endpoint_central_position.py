#!/usr/bin/env python3
"""Independent directed-dyadic replay of the low-endpoint position lemma."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib,time,sys
import verify_joint_five_dyadic as ar
HERE=Path(__file__).resolve().parent
SIGNS=[(-1,-1),(-1,1),(1,-1),(1,1)]
ROOTS=[(F(4,5),F(13,12),F(1,10),F(29,60),tl,th,F(0),F(1))for signs in SIGNS for tl,th in[(F(0),F(1,4)),(F(1,4),F(1))]]
def root(value):
 r=value.x.sqrt();assert r.lo>0
 return ar.A(r,[v/(2*r)for v in value.der])
def frame(t):
 d=ar.length([ar.A(1),t]);a=1/d;b=t/d
 return(a+b)/2,(a-b)/2,a,b

def circle_upper(x,t,sign):
 h,k,a,b=frame(t);q=F(1105,256);edge=root(q-(x+h).sq())
 if sign==-1:
  return ar.least([ar.CENTER_RADIUS,root(q-(x+k).sq())-h,edge+k])
 return ar.least([ar.CENTER_RADIUS,root(q-(x-k).sq())-h,edge-k])

def evaluate(box,signs,chart):
 variables=[]
 for j in range(4):
  grad=[0]*4;grad[j]=1;variables.append(ar.A(ar.I(box[2*j],box[2*j+1]),grad))
 z,v,t,s=variables;sl,sp=signs
 hl,kl,al,bl=frame(t);hp,kp,ap,bp=frame(s);gapy=F(221,600);gapx=F(503,480)-z
 # Reconstruct the physical endpoint-facet thresholds directly.
 wrongway=F(3,2)-z+F(217,480)
 if chart==0:
  threshold=gapy+1/(2*al)-t*gapx if sl==-1 else gapy+hl
 elif sl==-1:
  threshold=ar.least([gapy+hl,gapy+1/(2*al)-t*gapx,gapy+1/(2*bl)+wrongway/t])
 else:
  threshold=ar.least([gapy+hl,gapy+1/(2*al)+t*wrongway,gapy+1/(2*bl)-gapx/t])
 lower_l=ar.greatest([ar.A(F(31,50)),threshold]);lower_p=hp+F(1,10)
 upper_l=circle_upper(z,t,sl);upper_p=circle_upper(v,s,sp)
 dx=z-v;bottom=ar.greatest([lower_p-upper_l,-dx]);top=ar.least([upper_p-lower_l,dx])
 cosrel=(al*ap+sl*sp*bl*bp).absolute();sinrel=(sp*al*bp-sl*bl*ap).absolute();required=(1+cosrel+sinrel)/2
 projections=[]
 for a,b,sg in[(al,bl,sl),(ap,bp,sp)]:
  projections.append(a*dx+sg*b*(top if sg==1 else bottom))
  projections.append(b*dx-sg*a*(bottom if sg==1 else top))
 return ar.least([upper_l-lower_l,upper_p-lower_p,top-bottom,dx-1/(4*hl)-1/(4*hp),ar.greatest(projections)-required])

def upper(box,signs,chart):
 full=evaluate(box,signs,chart);mid=[(box[2*j]+box[2*j+1])/2 for j in range(4)]
 at=evaluate(tuple(x for m in mid for x in(m,m)),signs,chart).x
 for j,m in enumerate(mid):at+=full.der[j]*ar.I(box[2*j]-m,box[2*j+1]-m)
 return F(min(full.x.hi,at.hi),ar.SCALE)

def verify(data,progress=False):
 assert data['type']=='low_endpoint_central_position_scalar_cover_v1'
 assert data['proof_status']=='producer_complete_pending_independent_replay'
 assert data['Q']=='1105/256'and data['gx']=='217/480'and data['gy']=='221/600'
 assert data['root_indices']==list(range(8))and data['remaining']==0 and data['pending']==[]
 nodes=data['nodes'];todo=[(i,b,SIGNS[i//2],i%2,0)for i,b in enumerate(ROOTS)];seen=set();leaves=depthmax=0;largest=None;start=last=time.monotonic()
 while todo:
  i,box,signs,chart,depth=todo.pop();assert isinstance(i,int)and 0<=i<len(nodes)and i not in seen
  seen.add(i);node=nodes[i];depthmax=max(depthmax,depth)
  assert tuple(map(F,node['box']))==box and tuple(node['signs'])==signs and node['chart']==chart
  if 'children'in node:
   assert'terminal'not in node and'upper'not in node;dim=node['split'];assert isinstance(dim,int)and 0<=dim<4
   kids=node['children'];assert len(kids)==2 and kids[0]!=kids[1]
   m=(box[2*dim]+box[2*dim+1])/2;left,right=list(box),list(box);left[2*dim+1]=m;right[2*dim]=m
   todo.extend([(kids[0],tuple(left),signs,chart,depth+1),(kids[1],tuple(right),signs,chart,depth+1)])
  else:
   assert node['terminal']=='strict_scalar';value=upper(box,signs,chart);assert value<0,(i,str(value))
   leaves+=1;largest=value if largest is None else max(largest,value)
  now=time.monotonic()
  if progress and now-last>=25:print('CENTRAL X REPLAY',leaves,'seconds',round(now-start,1),flush=True);last=now
 assert len(seen)==len(nodes)and leaves==data['closed']
 return{'complete':True,'nodes':len(seen),'strict_interval_leaves':leaves,'maximum_depth':depthmax,'largest_replayed_upper':str(largest),'seconds':time.monotonic()-start}
def main():
 p=Path(sys.argv[1]);raw=p.read_bytes();report=verify(json.loads(raw),True)
 report.update(proof_status='independent_low_endpoint_central_position_replay_passed',certificate_sha256=hashlib.sha256(raw).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),arithmetic_sha256=hashlib.sha256(Path(ar.__file__).read_bytes()).hexdigest())
 p.with_name(p.stem+'_replay.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
if __name__=='__main__':main()
