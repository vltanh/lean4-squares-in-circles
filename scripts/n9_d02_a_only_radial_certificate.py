#!/usr/bin/env python3
"""Exact closed-domain cover of both physical radial A-only endpoints.

The radial endpoint may have unequal or zero individual corner weights.
It is not assumed to have a radial channel direction. All computations
are dyadic outward interval operations from the shared A-only engine.
"""
from pathlib import Path
from fractions import Fraction
from collections import Counter
import argparse,hashlib,json,time
import n9_d02_a_only_both_unique_certificate as shared
from n9_d02_a_only_both_unique_certificate import (
 I,SCALE,Bad,atanhalf,angle_sum_intervals,get_u,ratio_v,ratio_m,frame,
 dot,add,sub,mul,norm,
)

ROOT=shared.initial_box()[:2]
KIND='d02_l135_a_only_all_physical_radial_endpoints'

def evaluate(box,which):
 try:
  a,b=[I(*x,raw=True) for x in box]
  s,c=atanhalf(a);S,C=atanhalf(b)
  if (s-c).h<=(I(1)/625).l or (S-C).h<=0:return 'angle'
  delta=(s-c).intr(I(1)/625,1)
  H,k=angle_sum_intervals(a,b)
  if k.h<=0 or k.l>=SCALE//2:return 'angle'
  H=H.intr(I(3).sqrt()/2,1);k=k.intr(0,I(1)/2)
  p=(H-k).intr((I(3).sqrt()-1)/2,1);q=(H+k).intr(1,(I(3).sqrt()+1)/2)
  u=get_u(a,b,s,c,S,C,H,k,p).intr(I(1)/12,s/(s+S)).intr(0,I(3)/5)
  t=(1-(s/S)*(1-u)).intr(0,S/(s+S)).intr(0,I(3)/5)
  omega=((1-u)*H/S).intr(0,1)
  mu=u*t;nu=delta*p;F=(mu*c-nu*k,mu*s+nu*H)
  Fsq=mu.sq()+nu.sq()+2*mu*nu*C
  if ((I(1105)/64)*(nu*S).sq()-Fsq).h<0 or ((I(1105)/64)*(mu+nu*C).sq()-Fsq).h<0:return 'V_corner'
  v=ratio_v(u,a).intr(0,1);m=ratio_m(t,k).intr(0,4)
  a0,b0=frame(v);cY,cX=frame(m)
  bvec=(-a0,-b0);cvec=(-cX,cY);wB=(-b0,a0);wC=(-cY,-cX)
  east=(c,s);north=(-s,c);nd=(-k,H);td=(-H,-k)
  DB=add(add(east,mul(1-omega,north)),(I(1),I(1)))
  DC=add(add(east,north),add(nd,mul(t,td)))
  if which=='B':f=bvec;ww=wB;D=DB;other=DC;of=mul(-1,cvec)
  else:f=mul(-1,cvec);ww=mul(-1,wC);D=DC;other=DB;of=bvec
  L=1-dot(D,f);Ff=dot(F,f);Fw=dot(F,ww)
  if L.h<=0:return 'radial_L'
  den=(L.sq()*Fsq+Fw.sq()/4).sqrt()-L*Ff
  if den.l<=0:return None
  lam=(L.sq()+I(1)/4)/den
  Rsq=lam.sq()*Fsq
  if Rsq.h<(I(79)/40).sq().l or Rsq.l>(I(1105)/256).h:return 'radius'
  fnorm=Fsq.sqrt()
  if fnorm.l<=0:return None
  lam=lam.intr((I(79)/40)/fnorm,(I(1105).sqrt()/16)/fnorm)
  Z=mul(lam,F);AR=lam*Ff+L
  AR=AR.intr(((I(79)/40).sq()-I(1)/4).sqrt(),((I(1105)/256)-I(1)/4).sqrt())
  Qrad=sub(Z,D);qr=dot(Qrad,ww)
  if qr.h<=0 or qr.l>=SCALE//2:return 'radial_port'
  if (dot(sub(Z,other),of)-(AR-1)).l>0:return 'other_owned_support'
  P0=sub(sub(Z,east),north);RA=add(P0,mul(omega,north))
  quad=lambda o,x,y:[o,add(o,x),add(add(o,x),y),add(o,y)]
  V=quad(P0,east,north)
  A=quad(sub(RA,(I(1),I(1))),(I(1),I(0)),(I(0),I(1)))
  DD=quad(sub(P0,mul(t,td)),mul(-1,nd),td)
  radial=quad(sub(mul(AR-1,f),mul(I(1)/2,ww)),f,ww)
  for name,row in [('V',V),('A',A),('D',DD),('radial',radial)]:
   for pt in row:
    if (dot(pt,pt)-(I(1105)/256)).l>0:return name+'_vertex'
  return None
 except Bad as e:
  return 'empty_range' if str(e)=='empty' else None

def split(box,k):
 lo,hi=box[k];mid=(lo+hi)//2
 if not lo<mid<hi:raise ValueError('dyadic precision exhausted')
 le=list(box);ri=list(box);le[k]=(lo,mid);ri[k]=(mid,hi)
 return tuple(le),tuple(ri)

def generate(limit):
 nodes=[None,None];stack=[(1,ROOT,'C',0),(0,ROOT,'B',0)]
 counts=Counter();depth=0;start=time.monotonic()
 while stack:
  index,box,which,lev=stack.pop();depth=max(depth,lev)
  rule=evaluate(box,which)
  if rule is not None:nodes[index]=[rule];counts[which+':'+rule]+=1
  else:
   if len(nodes)+2>limit:
    return None,dict(status='OPEN',nodes=len(nodes),pending=len(stack)+1,box=box,which=which,counts=dict(counts),depth=depth)
   k=max(range(2),key=lambda j:Fraction(box[j][1]-box[j][0],ROOT[j][1]-ROOT[j][0]))
   le,ri=split(box,k);ii=len(nodes);nodes.extend([None,None]);nodes[index]=['split',k,ii,ii+1]
   stack.extend([(ii+1,ri,which,lev+1),(ii,le,which,lev+1)])
  if len(nodes)%20000==0:print(json.dumps(dict(nodes=len(nodes),pending=len(stack),which=which,depth=depth)),flush=True)
 data={'version':1,'kind':KIND,'precision_bits':shared.P,'root_box':ROOT,'roots':{'B':0,'C':1},'nodes':nodes,
       'shared_engine_sha256':hashlib.sha256(Path(shared.__file__).read_bytes()).hexdigest()}
 return data,dict(status='CLOSED',nodes=len(nodes),leaves=sum(counts.values()),depth=depth,seconds=round(time.monotonic()-start,2),counts=dict(counts))

def require(ok,message):
 if not ok:raise ValueError(message)

def verify(data):
 require(data['version']==1 and data['kind']==KIND,'wrong kind')
 require(data['precision_bits']==shared.P and tuple(map(tuple,data['root_box']))==ROOT,'wrong root')
 require(data['shared_engine_sha256']==hashlib.sha256(Path(shared.__file__).read_bytes()).hexdigest(),'wrong arithmetic engine')
 require(data['roots']=={'B':0,'C':1},'wrong feature roots')
 nodes=data['nodes'];seen=set();counts=Counter();stack=[(0,ROOT,'B'),(1,ROOT,'C')]
 while stack:
  i,box,which=stack.pop();require(0<=i<len(nodes) and i not in seen,'invalid/repeated node');seen.add(i);row=nodes[i]
  if row[0]=='split':
   require(len(row)==4 and row[1] in range(2),'invalid split');le,ri=split(box,row[1]);stack.extend([(row[2],le,which),(row[3],ri,which)])
  else:
   require(len(row)==1 and evaluate(box,which)==row[0],'unproved leaf');counts[which+':'+row[0]]+=1
 require(len(seen)==len(nodes),'unreachable nodes')
 return dict(status='EXACT COMPLETE RADIAL COVER REPLAYED',nodes=len(nodes),counts=dict(counts),Lean_verified=False)

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);ap.add_argument('--verify',type=Path);ap.add_argument('--limit',type=int,default=1000000);args=ap.parse_args()
 if args.verify:print(json.dumps(verify(json.loads(args.verify.read_text())),indent=2));return
 data,stats=generate(args.limit);print(json.dumps(stats,indent=2),flush=True)
 if data is not None:
  print(json.dumps(verify(data),indent=2),flush=True)
  if args.output:args.output.write_text(json.dumps(data,separators=(',',':'))+'\n')

if __name__=='__main__':main()
