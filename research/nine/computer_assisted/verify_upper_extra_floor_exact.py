#!/usr/bin/env python3
"""Independent exact arithmetic replay of the upper-extra-floor discovery tree.

No floating arithmetic, optimizer, or interval producer is imported. The sole
input from discovery is a finite binary subdivision tree and its leaf tags.
Every root endpoint, interval operation, and square-root enclosure is rational.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from collections import Counter
import argparse,json,time,hashlib
SCALE=1<<44
class Q:
 __slots__=('lo','hi')
 def __init__(self,lo,hi=None):self.lo=F(lo);self.hi=F(lo if hi is None else hi);assert self.lo<=self.hi
 def __add__(a,b):b=asq(b);return Q(a.lo+b.lo,a.hi+b.hi)
 __radd__=__add__
 def __neg__(a):return Q(-a.hi,-a.lo)
 def __sub__(a,b):return a+-asq(b)
 def __rsub__(a,b):return asq(b)+-a
 def __mul__(a,b):
  b=asq(b);v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi];return Q(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(a,b):b=asq(b);assert b.lo>0;return a*Q(1/b.hi,1/b.lo)
 def __rtruediv__(a,b):return asq(b)/a
 def sq(a):return Q(0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi),max(a.lo*a.lo,a.hi*a.hi))
 def ab(a):return Q(max(a.lo,-a.hi,0),max(abs(a.lo),abs(a.hi)))
 def root(a):
  assert a.hi>=0
  low=max(a.lo,0);high=a.hi
  n=isqrt(low.numerator*SCALE*SCALE//low.denominator)
  m=isqrt(high.numerator*SCALE*SCALE//high.denominator)
  if F(m*m,SCALE*SCALE)<high:m+=1
  l=F(n,SCALE);u=F(m,SCALE)
  assert l*l<=low and u*u>=high
  return Q(l,u)
def asq(x):return x if isinstance(x,Q) else Q(x)
def qmax(*v):v=[asq(x) for x in v];return Q(max(x.lo for x in v),max(x.hi for x in v))
def qmin(*v):v=[asq(x) for x in v];return Q(min(x.lo for x in v),min(x.hi for x in v))
def orient(t):
 def point(z):
  den=Q(1+z*z).root();a=1/den
  return a,z*a,(1+z)*a/2,(1-z)*a/2
 al,bl,hl,kl=point(t.lo);au,bu,hu,ku=point(t.hi)
 # a,k decrease; b,h increase on the exact closed interval [0,1].
 return Q(au.lo,al.hi),Q(bl.lo,bu.hi),Q(hl.lo,hu.hi),Q(ku.lo,kl.hi)

def leaf_reserve(box,code):
 tp,tu,x,v=[Q(*r) for r in box]
 ap,bp,p,kp=orient(tp);au,bu,u,ku=orient(tu);D=x-v
 if code==0:return -(x-p+F(451,810)).hi
 if code==1:return -(D-F(3,5)).hi
 A=qmax(Q(F(23,30)),p+F(1,2)-x)
 def cap(a):return (Q(F(91,60)**2)-a.sq()).root()-(1-(v+a).sq()).root()
 Yu=qmin(u+F(1,10),qmax(cap(A),cap(Q(F(13,12)))))
 V=Yu-p+F(857,1240)
 if code==2:return -V.hi
 assert code==3
 supp=qmax(1,(1+ap*au+bp*bu+(ap*bu-bp*au).ab())/2)
 return -(qmax(ap*D+bp*V,bp*D+ap*V,au*D+bu*V,bu*D+au*V)-supp).hi

def main():
 start=time.monotonic();base=Path(__file__).parent
 parser=argparse.ArgumentParser()
 parser.add_argument('--certificate',type=Path,default=base/'upper_extra_floor_certificate.json')
 parser.add_argument('--report',type=Path,default=base/'upper_extra_floor_verification_report.json')
 args=parser.parse_args();src=args.certificate;data=json.loads(src.read_text());events=data['events']
 root=((F(0),F(1)),(F(0),F(1)),(F(7,60),F(23,60)),(F(-29,60),F(-13,60)))
 stack=[(root,0)];counts=Counter();depth=0;leaves=0;minimum=None
 for idx,tag in enumerate(events):
  assert stack,('trailing tree events',idx)
  box,d=stack.pop();depth=max(depth,d)
  if tag>=0:
   assert tag<4;left=list(box);right=list(box);mid=(box[tag][0]+box[tag][1])/2
   assert box[tag][0]<mid<box[tag][1]
   left[tag]=(box[tag][0],mid);right[tag]=(mid,box[tag][1])
   stack.append((tuple(right),d+1));stack.append((tuple(left),d+1))
  else:
   code=-tag-1;assert 0<=code<4
   reserve=leaf_reserve(box,code)
   assert reserve>F(1,100000),('invalid exact leaf or small reserve',idx,code,str(reserve),box)
   counts[code]+=1;leaves+=1;minimum=reserve if minimum is None else min(minimum,reserve)
 assert not stack,('incomplete tree',len(stack))
 assert len(events)==2*leaves-1
 result={'status':'EXACT_REPLAY_PASSED','scope':'complete routed 000/01 plus central U above P implies yU-hU>1/10; not by itself the full mask',
 'nodes':len(events),'leaves':leaves,'max_depth':depth,'leaf_reasons':dict(sorted(counts.items())),
 'root_rationals':[[str(a),str(b)] for a,b in root],'sqrt_scale':SCALE,
 'uniform_positive_leaf_reserve':'1/100000','minimum_exact_reserve':str(minimum),
 'certificate_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
 'seconds':time.monotonic()-start,'arithmetic':'fractions.Fraction and math.isqrt only; no floating arithmetic; no producer import'}
 args.report.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='minimum_exact_reserve'},indent=2),flush=True)
if __name__=='__main__':main()
