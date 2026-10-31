#!/usr/bin/env python3
"""Exact full-domain upper-C visibility separation for the low aligned S root.

All decisions use Fraction intervals and outward dyadic radical bounds.
The root-authored physical theorem states the complete scalar domain.
No numerical pose or floating-point comparison is used.
"""
from fractions import Fraction as F
from math import isqrt
import json
from hashlib import sha256
from pathlib import Path

class I:
 def __init__(self,l,u=None):self.l=F(l);self.u=F(l if u is None else u);assert self.l<=self.u
 def __add__(a,b):
  if not isinstance(b,I):b=I(b)
  return I(a.l+b.l,a.u+b.u)
 __radd__=__add__
 def __neg__(a):return I(-a.u,-a.l)
 def __sub__(a,b):return a+-b if isinstance(b,I) else a+(-F(b))
 def __rsub__(a,b):return -a+b
 def __mul__(a,b):
  if not isinstance(b,I):b=I(b)
  q=[a.l*b.l,a.l*b.u,a.u*b.l,a.u*b.u];return I(min(q),max(q))
 __rmul__=__mul__
 def __truediv__(a,b):
  if not isinstance(b,I):b=I(b)
  assert b.l>0
  return a*I(1/b.u,1/b.l)
 def sq(a):
  return I(min(a.l*a.l,a.u*a.u) if a.l*a.u>=0 else 0,max(a.l*a.l,a.u*a.u))
 def cut(a,l=None,u=None):
  lo=a.l if l is None else max(a.l,F(l));hi=a.u if u is None else min(a.u,F(u))
  return I(lo,hi) if lo<=hi else None
 def pair(a):return [str(a.l),str(a.u)]

scale=1<<48
def sqrtI(a):
 assert a.u>=0
 def low(z):
  assert z>=0
  k=isqrt(z.numerator*scale*scale//z.denominator)
  return F(k,scale)
 l=low(max(F(0),a.l));u=low(a.u)
 if u*u<a.u:u+=F(1,scale)
 return I(l,u)

initial=[I(F(14,15),1),I(F(29,50),F(2,3)),I(F(2,25),1)]
widths=[p.u-p.l for p in initial]
def check(box):
 d,h,t=box;a=1-d;g=1-h
 b=sqrtI(1-t.sq())
 R2=(d+1).sq()+F(1,4)
 if R2.u<=4:return 'R>2',None
 Y=g+b+t
 X2=R2-Y.sq()
 if X2.u<=0:return 'X>0',None
 X=sqrtI(X2)
 x=(X-b+t).cut(F(3,10),d.u)
 if x is None:return 'x in (3/10,d)',None
 x=x.cut(t.l)
 if x is None:return 'x>t',None
 # Contract the original dependent X=x+b-t after narrowing x.
 z=(x+b-t).cut(X.l,X.u)
 if z is None:return 'lower point identity',None
 X=z
 if ((d-x)*t-(h-F(1,2))*b).u<0:return 'actual leaf screen',None
 w=x+a
 if w.l<=0 or X.l<=0:return None,None
 # Monotone component formulas avoid loss from normalizing a whole box.
 c=I(1)/sqrtI(1+(h/w).sq())
 s=I(1)/sqrtI(1+(w/h).sq())
 N=a*c+h*s;K=x*s
 W2=R2-(N+1).sq()
 if W2.u<0:return 'upper circle W real',None
 W=sqrtI(W2)
 rho=(W-K).cut(F(7,8),1)
 if rho is None:return 'upper actual mean rho',None
 delta=1-rho
 if W.l<=0:return None,None
 lam=((K-N*rho)/W).cut(0,F(197,925))
 if lam is None:return 'upper proper concurrence',None
 A=a+x-t
 L0=delta*s;H0=1-delta*c
 L1=lam*c+delta*s;H1=1+lam*s-delta*c
 G0=(A+L0)*H0-F(99,70)*L0
 G1=(A+L1)*H1-F(99,70)*L1
 G0b=A*H0+L0*(H0-F(99,70))
 G1b=A*H1+L1*(H1-F(99,70))
 G0lo=max(G0.l,G0b.l)
 B=s*A+(1-F(99,70))*c+delta*(s.sq()-c.sq())
 cs=(c*s).l
 ustar=max(lam.l,min(lam.u,-B.l/(2*cs)))
 quad=G0lo+B.l*ustar+cs*ustar*ustar
 G1lo=max(G1.l,G1b.l,quad)
 lower=min(G0lo,G1lo)
 target=I(lower,max(lower,G0.u,G1.u))
 if target.l>0:return 'strict target',target.l
 return None,target.l

stack=[('',initial)];leaves=[];nodes=0;maxdepth=0
while stack:
 path,box=stack.pop();nodes+=1;depth=len(path);maxdepth=max(maxdepth,depth)
 reason,reserve=check(box)
 if reason:
  leaves.append({'path':path,'reason':reason,'reserve':str(reserve) if reserve is not None else None})
  continue
 assert nodes<200000 and depth<42,(path,box)
 k=max(range(3),key=lambda j:(box[j].u-box[j].l)/widths[j])
 m=(box[k].l+box[k].u)/2
 left=box.copy();right=box.copy();left[k]=I(box[k].l,m);right[k]=I(m,box[k].u)
 stack.append((path+'1',right));stack.append((path+'0',left))
from collections import Counter
paths={item['path'] for item in leaves};assert len(paths)==len(leaves)
while paths!={''}:
 depth=max(map(len,paths));parents={p[:-1] for p in paths if len(p)==depth}
 for p in parents:
  assert p+'0' in paths and p+'1' in paths
  paths.remove(p+'0');paths.remove(p+'1');paths.add(p)
assert nodes==2*len(leaves)-1
positive=[F(item['reserve']) for item in leaves if item['reserve'] is not None]
assert min(positive)>F(1,1000000)
payload=json.dumps(leaves,sort_keys=True,separators=(',',':')).encode()
record={'parameters':['d','h','t'],'initial':[i.pair() for i in initial],'square_root_dyadic_bits':48,'nodes':nodes,'max_depth':maxdepth,'leaf_count':len(leaves),'reason_counts':dict(Counter(l['reason'] for l in leaves)),'unresolved_boxes':0,'complete_prefix_cover':True,'uniform_strict_floor':'1/1000000','smallest_margin':str(min(positive)),'canonical_leaf_sha256':sha256(payload).hexdigest(),'sampled_poses':False,'leaves':leaves}
out=Path('/tmp/aligned_low_s_upper_c_visibility_certificate.json');out.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='leaves'},indent=2))
