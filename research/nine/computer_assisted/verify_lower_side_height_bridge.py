#!/usr/bin/env python3
"""Independent rational replay; imports no producer.
The only trusted inputs are the two printed rational rectangles and the
standalone physical inequalities reconstructed here.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json,hashlib,sys
P=1<<90
class R:
 def __init__(self,low,high=None):
  self.low=F(low);self.high=self.low if high is None else F(high)
  if self.low>self.high:raise ValueError('reversed interval')
 def __add__(x,y):y=coerce(y);return R(x.low+y.low,x.high+y.high)
 __radd__=__add__
 def __neg__(x):return R(-x.high,-x.low)
 def __sub__(x,y):return x+-coerce(y)
 def __rsub__(x,y):return coerce(y)+-x
 def __mul__(x,y):
  y=coerce(y);z=[a*b for a in (x.low,x.high) for b in (y.low,y.high)];return R(min(z),max(z))
 __rmul__=__mul__
 def __truediv__(x,y):
  y=coerce(y)
  if y.low<=0:raise ValueError('division reaches zero')
  return x*R(1/y.high,1/y.low)
 def __rtruediv__(x,y):return coerce(y)/x
 def abs(x):return R(0 if x.low<=0<=x.high else min(abs(x.low),abs(x.high)),max(abs(x.low),abs(x.high)))
 def sq(x):return R(0 if x.low<=0<=x.high else min(x.low*x.low,x.high*x.high),max(x.low*x.low,x.high*x.high))
def coerce(x):return x if isinstance(x,R) else R(x)
def minimum(*xs):xs=[coerce(x)for x in xs];return R(min(x.low for x in xs),min(x.high for x in xs))
def maximum(*xs):xs=[coerce(x)for x in xs];return R(max(x.low for x in xs),max(x.high for x in xs))
def root(x):
 x=coerce(x)
 if x.low<0:raise ValueError('negative radicand')
 lo=isqrt(x.low.numerator*P*P//x.low.denominator)
 hi=isqrt(x.high.numerator*P*P//x.high.denominator)
 if F(hi*hi,P*P)<x.high:hi+=1
 assert F(lo*lo,P*P)<=x.low and F(hi*hi,P*P)>=x.high
 return R(F(lo,P),F(hi,P))
def main_frame(low,high):
 low=F(low);high=F(high)
 kl=root(F(1,2)-low*low);kh=root(F(1,2)-high*high)
 return (R((R(high)+kh).low,(R(low)+kl).high),R((R(low)-kl).low,(R(high)-kh).high),R(1/(4*high),1/(4*low)),R(low+1/(4*low)-1,high+1/(4*high)-1))
def necessary(box,which):
 H=R(*box[0]);K=R(*box[1]);a,b,g,eta=main_frame(*box[0]);A,B,G,theta=main_frame(*box[1]);V=eta+theta
 d=minimum(F(61,30)-H-K,H+K);sigma=1+(H-K).abs()
 facet=minimum(*[(sigma-c*d)/maximum(z,F(1,40))for c,z in [(a,b),(b,a),(A,B),(B,A)]])
 radial=root(maximum(0,sigma.sq()-d.sq()))
 gap=maximum(facet,radial)
 m=G+eta-F(199,120)+F(32,9)*V
 target=3*H-F(211,100)if which==0 else R(F(-1,4))
 return [F(1,30)-V,target-m-gap]
ROOTS=[[(F(57,100),F(31,50)),(F(1,2),F(13,20))],[(F(31,50),F(13,20)),(F(1,2),F(13,20))]]
def verify(path):
 raw=Path(path).read_bytes();d=json.loads(raw)
 if d['schema']!='lower_side_height_bridge_v1':raise ValueError('wrong schema')
 if d['roots']!=[[[str(a),str(b)]for a,b in r]for r in ROOTS]:raise ValueError('wrong roots')
 if len(d['events'])!=2:raise ValueError('wrong forest')
 reports=[];reserve=None
 for which,(rr,ev)in enumerate(zip(ROOTS,d['events'])):
  if any(type(t)is not int for t in ev):raise ValueError('noninteger event')
  stack=[(rr,0)];at=0;leaves=0;maxdepth=0;rules=[0,0];minres=None
  while stack:
   box,depth=stack.pop();maxdepth=max(maxdepth,depth)
   if at>=len(ev):raise ValueError('missing event')
   tag=ev[at];at+=1
   if tag in (0,1):
    lo,hi=box[tag];mid=(lo+hi)/2;left=box.copy();right=box.copy();left[tag]=(lo,mid);right[tag]=(mid,hi);stack.extend([(right,depth+1),(left,depth+1)])
   elif tag in (-1,-2):
    vals=necessary(box,which);rule=-tag-1;r=-vals[rule].high
    if r<=0:raise ValueError(('nonnegative leaf',which,at,box,str(r)))
    leaves+=1;rules[rule]+=1;minres=r if minres is None else min(minres,r)
   else:raise ValueError('unknown event')
  if at!=len(ev):raise ValueError('trailing event')
  if len(ev)!=2*leaves-1:raise ValueError('wrong binary count')
  reports.append(dict(root=which,nodes=at,leaves=leaves,max_depth=maxdepth,rules=rules,minimum_reserve=str(minres)))
  reserve=minres if reserve is None else min(reserve,minres)
 assert F(1)-F(289,300)**2-F(217,1200)**2==F(56575,1440000)>0
 return dict(result='PASS',complete=True,strict_leaves=sum(r['leaves']for r in reports),nodes=sum(r['nodes']for r in reports),frontier=0,minimum_reserve=str(reserve),roots=reports,certificate_sha256=hashlib.sha256(raw).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),arithmetic='independent Fraction rational intervals, outward 90-bit radicals, no producer imports')
if __name__=='__main__':
 p=sys.argv[1]if len(sys.argv)>1 else 'lower_side_height_bridge.json';report=verify(p);out=sys.argv[2]if len(sys.argv)>2 else 'lower_side_height_bridge_independent_replay.json';Path(out).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
