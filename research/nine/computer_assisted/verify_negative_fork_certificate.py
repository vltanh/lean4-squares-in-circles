#!/usr/bin/env python3
"""Independent directed-integer replay of negative-fork certificates.

The producer uses Fraction intervals and 44-bit radical enclosures. This
verifier imports no producer and uses directed integer arithmetic with 96
fractional bits for every operation. It checks the complete rectangle
cover and separately rechecks the local derivative proof.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from copy import deepcopy
import json,hashlib,sys,gzip
S=1<<96
def ceildiv(a,b):return -((-a)//b)
class V:
 def __init__(self,l,h=None,raw=False):
  if isinstance(l,V):self.l,self.h=l.l,l.h
  elif raw:self.l,self.h=l,h
  else:
   l=F(l);h=F(l if h is None else h)
   self.l=l.numerator*S//l.denominator;self.h=ceildiv(h.numerator*S,h.denominator)
  assert self.l<=self.h
 def __add__(self,o):o=V(o);return V(self.l+o.l,self.h+o.h,True)
 __radd__=__add__
 def __neg__(self):return V(-self.h,-self.l,True)
 def __sub__(self,o):return self+-V(o)
 def __rsub__(self,o):return V(o)+-self
 def __mul__(self,o):
  o=V(o);p=[a*b for a in (self.l,self.h) for b in (o.l,o.h)]
  return V(min(p)//S,ceildiv(max(p),S),True)
 __rmul__=__mul__
 def __truediv__(self,o):
  o=V(o);assert o.l>0
  return V(min(a*S//b for a in (self.l,self.h) for b in (o.l,o.h)),max(ceildiv(a*S,b) for a in (self.l,self.h) for b in (o.l,o.h)),True)
 def __rtruediv__(self,o):return V(o)/self
 def square(self):
  low=0 if self.l<=0<=self.h else min(self.l*self.l,self.h*self.h)
  return V(low//S,ceildiv(max(self.l*self.l,self.h*self.h),S),True)
 def abs(self):return V(0 if self.l<=0<=self.h else min(abs(self.l),abs(self.h)),max(abs(self.l),abs(self.h)),True)
 def sqrt(self):
  assert self.l>=0
  l=isqrt(self.l*S);h=isqrt(self.h*S)
  if h*h<self.h*S:h+=1
  return V(l,h,True)
def length(x):return (x[0].square()+x[1].square()).sqrt()
def inner(x,y):return x[0]*y[0]+x[1]*y[1]
def det(x,y):return x[0]*y[1]-x[1]*y[0]
def fixed_cost(vectors,axis):
 return sum((inner(v,axis).abs()+det(v,axis).abs() for v in vectors),V(0))/(2*length(axis))
def arbitrary_cost(vectors,limited=False):
 axes=[[V(1),V(F(7,100))],[V(1),V(F(-7,100))]] if limited else []
 for x,y in vectors:
  ax,ay=x.abs(),y.abs()
  if limited and not (ay.l<=(F(7,100)*ax).h or ax.l<=(F(7,100)*ay).h):continue
  if x.l==x.h==0:
   if y.l==y.h==0:continue
   axes.append([V(0),V(1)])
  elif y.l==y.h==0:axes.append([V(1),V(0)])
  else:axes.append([x,y])
 bounds=[0 if length(u).l==0 else fixed_cost(vectors,u).l for u in axes]
 assert bounds
 universal=sum(length(v).l for v in vectors)//2
 return max(universal,min(bounds))
def upper_bound(box,p,owner):
 w=V(box[0],box[1]);z=V(box[2],box[3]);k,mu,nu=map(F,p)
 a=F(46);b=F(27,2)
 e=[a+k*w,-V(k)];r=[mu+nu-k*w,mu*z+k+nu];q=[V(b-mu-nu),-mu*z-nu]
 ec=[[V(a),V(0)],e,[-k*w,V(k)]]
 rc=[r,[V(mu),mu*z],[-k*w,V(k)]]
 pc=[[V(b),V(0)],q,[V(mu),mu*z]]
 e_low=fixed_cost(ec,[V(1),w]).l if owner=='E' else arbitrary_cost(ec,True)
 r_low=fixed_cost(rc,[V(1),w]).l if owner=='R' else arbitrary_cost(rc)
 p_low=arbitrary_cost(pc)
 total=(b+V(F(1105,256)).sqrt()*(length(e)+length(r)+length(q))).h
 return F(total-e_low-r_low-p_low,S)
def local_check():
 a=F(46);b=F(27,2);kap=F(207,16);rad=V(F(1105,256)).sqrt();answer=[]
 for sign,ws in [('plus',(F(0),F(1,64))),('minus',(F(-1,64),F(0)))]:
  w=V(*ws);z=V(F(-1,64),0);k=kap/(1+w);K=kap/(1+w).square()
  A=length([a+k*w,-k]);B=length([b-k*w,k+b*z])
  d=(a+k*w-k)/A-(b-k*w+b*z+k)/B
  dw=K*(rad*d+2+w)-k+28*w if sign=='plus' else K*(rad*d+2)+74*w
  dz=b*(rad*((k+b*z)/B-1)+1)+28*z
  if sign=='plus':assert -8*S<dw.l and dw.h<-4*S
  else:assert 4*S<dw.l and dw.h<8*S
  assert 3*S<dz.l and dz.h<6*S
  answer.append({'side':sign,'dw':[str(F(dw.l,S)),str(F(dw.h,S))],'dz':[str(F(dz.l,S)),str(F(dz.h,S))]})
 assert a*a+kap*kap==529*F(1105,256)
 assert b*b+kap*kap==81*F(1105,256)
 assert 32*F(1105,256)-a-b-2*kap==F(211,4)
 assert F(95,2)+46*F(828,65)/49-(46+F(92,7)+F(23,112))==F(5623,50960)>0
 assert F(73,4)+b*F(828,65)*F(4095,4096)/20-(b+F(92,7))==F(58349,286720)>0
 return answer
def verify(c):
 assert c['type']=='negative_fork_interval_certificate_v1'
 owner=c['owner'];assert owner in ('E','R')
 assert c['Q']=='1105/256' and c['a']=='46' and c['b']=='27/2' and c['T']=='211/4'
 assert c['E_tangent_bound']=='7/100' and c['local_box']==['-1/64','1/64','-1/64','0']
 eps=F(1,64);lo,hi=(F(-2,3),F(6)) if owner=='R' else (F(-7,100),F(7,100))
 roots=[(lo,-eps,F(-4),F(0)),(eps,hi,F(-4),F(0)),(-eps,eps,F(-4),-eps)]
 assert c['root_indices']==[0,1,2]
 nodes=c['nodes'];todo=list(zip(c['root_indices'],roots));seen=set();leaves=0;maximum=F(-10**6)
 while todo:
  idx,expected=todo.pop();assert isinstance(idx,int) and 0<=idx<len(nodes) and idx not in seen
  seen.add(idx);node=nodes[idx];box=tuple(map(F,node['box']));assert box==expected and box[0]<box[1] and box[2]<box[3]
  if 'multipliers' in node:
   assert 'children' not in node;assert len(node['multipliers'])==3
   p=tuple(map(F,node['multipliers']));assert all(v>=0 for v in p)
   recorded=F(node['upper']);assert recorded<F(211,4)
   computed=upper_bound(box,p,owner);assert computed<=recorded,(idx,computed,recorded)
   maximum=max(maximum,recorded);leaves+=1
  else:
   j=node['split_dimension'];assert j in (0,1);mid=F(node['split_value'])
   assert box[2*j]<mid<box[2*j+1]
   children=node['children'];assert len(children)==2 and children[0]!=children[1]
   left=list(box);right=list(box);left[2*j+1]=mid;right[2*j]=mid
   todo.extend([(children[0],tuple(left)),(children[1],tuple(right))])
 assert len(seen)==len(nodes) and leaves==c['leaf_count']
 assert maximum==F(c['largest_upper'])
 return leaves
def verify_compact(c):
 assert c['type']=='negative_fork_compact_v1' and c['multiplier_denominator']==64
 owner=c['owner'];assert owner in ('E','R')
 eps=F(1,64);lo,hi=(F(-2,3),F(6)) if owner=='R' else (F(-7,100),F(7,100))
 roots=[(lo,-eps,F(-4),F(0)),(eps,hi,F(-4),F(0)),(-eps,eps,F(-4),-eps)]
 stream=c['preorder'];cursor=0;leaves=0;nodes=0;maximum=F(-10**6)
 def visit(box):
  nonlocal cursor,leaves,nodes,maximum
  assert cursor<len(stream);tag=stream[cursor];cursor+=1;nodes+=1
  assert isinstance(tag,int)
  if tag in (-1,-2):
   j=-1-tag;mid=(box[2*j]+box[2*j+1])/2
   left=list(box);right=list(box);left[2*j+1]=mid;right[2*j]=mid
   visit(tuple(left));visit(tuple(right))
  else:
   assert tag>0 and cursor+1<len(stream)
   mu,nu=stream[cursor:cursor+2];cursor+=2
   assert isinstance(mu,int) and mu>0 and isinstance(nu,int) and nu>=0
   result=upper_bound(box,[F(tag,64),F(mu,64),F(nu,64)],owner)
   assert result<F(211,4),(box,result)
   leaves+=1;maximum=max(maximum,result)
 for root in roots:visit(root)
 assert cursor==len(stream) and leaves==c['leaf_count']
 return leaves,nodes,maximum
def main():
 p=Path(sys.argv[1]);raw=p.read_bytes();c=json.loads(gzip.decompress(raw) if p.suffix=='.gz' else raw)
 compact=c['type']=='negative_fork_compact_v1'
 if compact:leaves,node_count,maximum=verify_compact(c)
 else:leaves=verify(c);node_count=len(c['nodes']);maximum=F(c['largest_upper'])
 local=local_check()
 controls=[]
 if compact:
  d=deepcopy(c);d['preorder'].pop();controls.append(d)
  d=deepcopy(c);d['preorder'][0]=-3;controls.append(d)
  d=deepcopy(c);i=next(j for j,v in enumerate(d['preorder']) if v>0);d['preorder'][i]=0;controls.append(d)
 else:
  d=deepcopy(c);d['nodes'][0]['box'][0]='0';controls.append(d)
  d=deepcopy(c);leaf=next(x for x in d['nodes'] if 'multipliers' in x);leaf['upper']='-1000000';controls.append(d)
  d=deepcopy(c);leaf=next(x for x in d['nodes'] if 'multipliers' in x);leaf['multipliers'][0]='-1';controls.append(d)
 for d in controls:
  try:verify_compact(d) if compact else verify(d)
  except (AssertionError,ZeroDivisionError):continue
  raise AssertionError('A deliberately invalid certificate passed')
 report={'status':'PASS_COMPONENT_ONLY','owner':c['owner'],'leaf_count':leaves,'nodes':node_count,'sha256':hashlib.sha256(raw).hexdigest(),'largest_upper':str(maximum),'arithmetic':'96-bit directed integer intervals; no producer import','local_derivatives':local,'negative_controls_rejected':len(controls),'whole_mask_closed':False}
 base=p.name.split('.')[0].replace('_certificate','');out=p.with_name(base+'_verification_report.json');out.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items() if k!='local_derivatives'},indent=2))
if __name__=='__main__':main()
