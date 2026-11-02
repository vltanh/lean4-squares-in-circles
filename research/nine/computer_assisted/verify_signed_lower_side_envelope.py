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

def frame_point(t):
 t=R(t);a=1/root(1+t.sq());b=t*a;return a,b,(a+b)/2,(a-b)/2

def frame(t):
 left=frame_point(t.low);right=frame_point(t.high)
 return R(right[0].low,left[0].high),R(left[1].low,right[1].high),R(left[2].low,right[2].high),R(right[3].low,left[3].high)

def exact_support_at(t,u,sg):
 a,b,_,_=frame_point(t);c,d,_,_=frame_point(u)
 return (1+(a*c+sg*b*d).abs()+(a*d-sg*b*c).abs())/2

def support(t,u,sg):
 # The folded angle difference for sg=+1 lies in [-pi/4,pi/4].
 # For sg=-1 the angle sum lies in [0,pi/2], with its unique
 # maximum at pi/4. Both extrema are reconstructed algebraically.
 if sg>0:
  a=exact_support_at(t.low,u.high,sg);b=exact_support_at(t.high,u.low,sg)
  lo=min(a.low,b.low)
  if t.low<=u.high and u.low<=t.high:lo=F(1)
  return R(lo,max(a.high,b.high))
 a=exact_support_at(t.low,u.low,sg);b=exact_support_at(t.high,u.high,sg)
 hi=max(a.high,b.high)
 if t.low+u.low+t.low*u.low<=1<=t.high+u.high+t.high*u.high:hi=max(hi,((1+root(2))/2).high)
 return R(min(a.low,b.low),hi)

def main_parts(H):
 kl=root(F(1,2)-H.low*H.low);kr=root(F(1,2)-H.high*H.high)
 al=H.low+kl;ar=H.high+kr;bl=H.low-kl;br=H.high-kr
 a=R(ar.low,al.high);b=R(max(0,bl.low),br.high);g=R(1/(4*H.high),1/(4*H.low))
 t=R(max(0,(bl/al).low),(br/ar).high)
 return a,b,g,t

def upper_height(z,fr,ss):
 a,b,h,k=fr
 offsets=[(h,-ss*k),(ss*k,h),(-h,ss*k),(-ss*k,-h)]
 return minimum(*[root(F(1105,256)-(z+vx).sq())-vy for vx,vy in offsets])

def scalar(box,rid):
 h,t,z=[R(a,b)for a,b in box];sm=1 if rid&2 else -1;ss=1 if rid&1 else -1
 a,b,g,tm=main_parts(h);A,B,H,K=frame(t);sigma=support(tm,t,sm*ss)
 heights=[]
 for xm in [g-F(1,60),F(61,60)-h]:
  dx=xm-z
  for nx,ny in [(sm*a,b),(-sm*b,a),(ss*A,B),(-ss*B,A)]:
   heights.append((sigma-nx*dx)/maximum(ny,F(1,40)))
 clear=minimum(*heights)
 U=upper_height(z,(A,B,H,K),-ss)
 def poly(x):return -F(331,1000)-F(9,20)*(x-F(1,2))-F(7,4)*(x-F(1,2))**2
 target=R(F(-1,3))if sm<0 else R(poly(h.high),poly(h.low))
 return target-clear+U
ROOT=[(F(1,2),F(13,20)),(F(0),F(1)),(F(29,60),F(13,12))]
def verify(path):
 raw=Path(path).read_bytes();d=json.loads(raw)
 if d.get('schema')!='signed_lower_side_envelope_v1' or d.get('complete')is not True:raise ValueError('wrong schema or incomplete')
 ev=d['events'];at=0;stats=[];minimum_margin=None
 for rid in range(4):
  stack=[(ROOT.copy(),0)];n=0;leaf=0;dep=0;reserve=None
  while stack:
   box,depth=stack.pop();dep=max(dep,depth)
   if at>=len(ev):raise ValueError('missing event')
   tag=ev[at];at+=1;n+=1
   if type(tag)is not int:raise ValueError('noninteger tag')
   if tag in (0,1,2):
    l,u=box[tag];mid=(l+u)/2;left=box.copy();right=box.copy();left[tag]=(l,mid);right[tag]=(mid,u);stack.extend([(right,depth+1),(left,depth+1)])
   elif tag==-1:
    r=-scalar(box,rid).high
    if r<=0:raise ValueError(('invalid leaf',rid,at,box,str(r)))
    leaf+=1;reserve=r if reserve is None else min(reserve,r)
   else:raise ValueError('unknown axis or rule')
  if n!=2*leaf-1:raise ValueError('count mismatch')
  minimum_margin=reserve if minimum_margin is None else min(minimum_margin,reserve)
  stats.append(dict(root=rid,main_sign=1 if rid&2 else -1,side_sign=1 if rid&1 else -1,nodes=n,leaves=leaf,depth=dep,minimum_reserve=str(reserve)))
 if at!=len(ev):raise ValueError('trailing events')
 if d.get('nodes')!=at or d.get('leaves')!=sum(s['leaves']for s in stats) or d.get('perroot')!=[s['leaves']for s in stats]:raise ValueError('metadata count mismatch')
 return dict(result='PASS',complete=True,strict_leaves=sum(s['leaves']for s in stats),nodes=at,frontier=0,roots=stats,minimum_reserve=str(minimum_margin),certificate_sha256=hashlib.sha256(raw).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),arithmetic='independent Fraction intervals, 90-bit outward radicals; no producer import')
if __name__=='__main__':
 p=sys.argv[1]if len(sys.argv)>1 else 'signed_lower_side_envelope.json';d=verify(p);out=sys.argv[2]if len(sys.argv)>2 else 'signed_lower_side_envelope_independent_replay.json';Path(out).write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2))
