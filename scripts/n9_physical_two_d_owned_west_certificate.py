#!/usr/bin/env python3
"""Exact full-domain candidate cover for the physical-two D-owned West/strict row.

The evaluator retains the complete V/A/D moments and uses actual contained
points of the unchanged exterior unit B. No loaded endpoint or N premise
is used. Failed subdivisions are not accepted as proof.
"""
from __future__ import annotations
import argparse,hashlib,json,time
from pathlib import Path
from collections import Counter
from fractions import Fraction
import n9_d02_a_only_both_unique_certificate as common
from n9_d02_a_only_both_unique_certificate import I,Bad,SCALE,atanhalf,angle_sum_intervals,dot,mul,add,sub
KIND='physical_two_west_strict_A_owned_roof_D_owned_AD_genuine_West'
ROOT=((0,SCALE),((I(2).sqrt()-1).l,SCALE),(SCALE//2,SCALE),((I(9)/10).l,(I(61)/60).h))
NAMES=('alpha_half_tangent','beta_half_tangent','roof_height_gap','radial_inner_support')
BASE=Path(__file__).resolve().parents[1]
def evaluator(box):
 try:
  aa,bb,j,d=[I(*p,raw=True) for p in box]
  s,c=atanhalf(aa);S,C=atanhalf(bb)
  H,k=angle_sum_intervals(aa,bb)
  if k.h<=0 or (S-C).h<=0:return 'strict_angle'
  k=k.intr(0,I(1)/I(2).sqrt());H=H.intr(I(1)/I(2).sqrt(),1)
  H=H.intr((1-k.sq()).sqrt(),(1-k.sq()).sqrt())
  p=H-k
  if p.h<=0:return 'strict_angle'
  p=p.intr(0,1);delta=(S-C).intr(0,1)
  U=H-j*S;T=H-j*s
  if U.h<=0 or T.h<=0:return 'genuine_port'
  U=U.intr(0,H);T=T.intr(0,H);u=(U/H).intr(0,1);t=(T/H).intr(0,1)
  tau=j-I(1)/2;kap=d*s+c/2
  eq=tau*U*T-p*delta*H.sq()*kap
  if not eq.zero():return 'full_torque'
  # V retains both individual physical circle coefficients.
  if (2*(d+1)*tau*s-tau*c-kap).l>0:return 'physical_V_weights'
  R2=(d+1).sq()+I(1)/4
  if R2.l>(I(1105)/256).h or R2.h<(I(79)/40).sq().l:return 'radius'
  K=(d-c+u*s,I(1)/2+s+u*c)
  # FB is a positive multiple of -A*h+B*nD.
  # The two choices use the exact same original force via the full hub torque.
  # They cover each other's potentially vanishing comparison boundaries.
  for label,A,B in [('hub',p*H,U),('roof',tau*T,delta*kap*H)]:
   F=(-A*c+B*C,A*s+B*S)
   fsq=A.sq()+B.sq()+2*k*A*B
   fn=fsq.sqrt();KF=dot(K,F)
   if (KF-d*fn).l>0:return 'B_support_'+label
   if ((dot(K,K)+1-R2)*fn+2*KF).l>0:return 'B_point_'+label
  # Four original contained A vertices and D vertices supply independent caps.
  h=(c,-s);e=(s,c);P0=(d,I(1)/2)
  nD=(C,S);tD=(-S,C);Q=(d,I(1)/2-j)
  for hh in [0,1]:
   for ee in [u-1,u]:
    z=add(sub(P0,mul(hh,h)),mul(ee,e))
    if (dot(z,z)-R2).l>0:return 'A_containment'
  for nn in [0,1]:
   for tt in [0,1]:
    z=add(sub(Q,mul(nn,nD)),mul(tt,tD))
    if (dot(z,z)-R2).l>0:return 'D_containment'
  return None
 except Bad as ex:
  return 'empty_range' if str(ex)=='empty' else None

def split(box,k):
 l,h=box[k];m=(l+h)//2
 if not l<m<h:raise ValueError('precision limit')
 x=list(box);y=list(box);x[k]=(l,m);y[k]=(m,h)
 return tuple(x),tuple(y)
def choose(box):
 widths=[Fraction(h-l,ROOT[k][1]-ROOT[k][0])*(Fraction(1,4) if k==3 else 1) for k,(l,h) in enumerate(box)]
 return max(range(4),key=lambda k:widths[k])
def generate(limit):
 st=time.monotonic();nodes=[None];stack=[(0,ROOT,0)];cnt=Counter();depth=0
 while stack:
  i,box,dep=stack.pop();depth=max(depth,dep);rule=evaluator(box)
  if rule is not None:nodes[i]=[rule];cnt[rule]+=1
  else:
   if len(nodes)+2>limit:
    return None,dict(status='UNRESOLVED',nodes=len(nodes),pending=len(stack)+1,depth=depth,counts=dict(cnt),seconds=round(time.monotonic()-st,2),box=[[str(Fraction(x,SCALE)) for x in p] for p in box])
   k=choose(box);le,ri=split(box,k);j=len(nodes);nodes.extend([None,None]);nodes[i]=['split',k,j,j+1];stack.extend([(j+1,ri,dep+1),(j,le,dep+1)])
  if len(nodes)%10000==1:print(json.dumps({'nodes':len(nodes),'pending':len(stack),'depth':depth}),flush=True)
 stats=dict(status='CLOSED',nodes=len(nodes),leaves=sum(cnt.values()),counts=dict(cnt),depth=depth,seconds=round(time.monotonic()-st,2),pending=0)
 data=dict(version=1,kind=KIND,precision_bits=common.P,root=ROOT,nodes=nodes,stats=stats,arithmetic_sha256=hashlib.sha256(Path(common.__file__).read_bytes()).hexdigest())
 return data,stats
def verify(data):
 if data['version']!=1 or data['kind']!=KIND or data['precision_bits']!=common.P or tuple(map(tuple,data['root']))!=ROOT:raise ValueError('bad metadata')
 if data['arithmetic_sha256']!=hashlib.sha256(Path(common.__file__).read_bytes()).hexdigest():raise ValueError('arithmetic engine hash changed')
 st=time.monotonic();nodes=data['nodes'];seen=set();stack=[(0,ROOT,0)];cnt=Counter();depth=0
 while stack:
  i,b,dep=stack.pop()
  if i in seen or not 0<=i<len(nodes):raise ValueError('duplicate/invalid node')
  seen.add(i);row=nodes[i];depth=max(depth,dep)
  if row[0]=='split':
   if len(row)!=4 or row[1] not in range(4):raise ValueError('bad split')
   le,ri=split(b,row[1]);stack.extend([(row[2],le,dep+1),(row[3],ri,dep+1)])
  else:
   if len(row)!=1 or evaluator(b)!=row[0]:raise ValueError('unproved leaf')
   cnt[row[0]]+=1
 if len(seen)!=len(nodes):raise ValueError('unreached node')
 if data['stats']['counts']!=dict(cnt):raise ValueError('bad counts')
 return dict(verified=True,nodes=len(nodes),leaves=sum(cnt.values()),counts=dict(cnt),depth=depth,seconds=round(time.monotonic()-st,2))
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--limit',type=int,default=1000000);ap.add_argument('--output',type=Path);ap.add_argument('--verify',type=Path);args=ap.parse_args()
 if args.verify:print(json.dumps(verify(json.loads(args.verify.read_text())),indent=2));return
 data,stats=generate(args.limit);print(json.dumps(stats,indent=2),flush=True)
 if data is None:return
 if args.output:args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(data,separators=(',',':'))+'\n')
 print(json.dumps(verify(data),indent=2),flush=True)
if __name__=='__main__':main()
