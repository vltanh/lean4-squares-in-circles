#!/usr/bin/env python3
"""Independent exact arithmetic replay of the inner-main-height discovery tree.

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

CAP=Q(F(451,810));DISK=Q(F(1105,256));B=Q(F(263,480));Cb=Q(F(2093,1800));J=Q(F(29927,30000))
def leaf_reserve(box,code):
 tp,tr,x,X=[Q(*b) for b in box];ap,bp,p,kp=orient(tp);ar,br,r,kr=orient(tr);D=X-x
 if code==0:return -(x-p+CAP).hi
 if code==1:return -(r+CAP-X).hi
 if code==2:return -(1+r-p-D).hi
 if code==3:return -(2*D.sq()-(1+(p-r).ab()).sq()).hi
 A=qmax(Q(F(59,60)),Q(F(157,184))+F(27,92)*(p-x))
 if code==4:return A.lo-F(61,60)
 W=1+r-p-D
 g=qmax(Q(F(15,31)),1/(2+F(27,46)*W))
 deltaP=-x.ab()-F(1,60)
 innerA=(Q(F(1,2))+deltaP*bp)/ap
 innerNum=Q(F(1,2))+deltaP*ap
 assert innerNum.lo>0
 innerLows=[p.lo,innerA.lo]
 if bp.hi>0:innerLows.append(innerNum.lo/bp.hi)
 innerReach=Q(min(innerLows),min(p.hi,innerA.hi))
 ylo=g+innerReach-F(7,20)
 if code==5:return -(p+F(1,10)-ylo).hi
 plus=qmin((DISK-(X+kr).sq()).root()-r,kr+(DISK-(X+r).sq()).root())
 minus=qmin((DISK-(X+r).sq()).root()-kr,(DISK-(X-kr).sq()).root()-r)
 Yu=qmax(plus,minus)
 if code==6:
  ca=qmax(Q(F(221,600)),1-(DISK-(A+J).sq()).root())
  delta=X-Q(F(503,480));reachA=(Q(F(1,2))+delta*br)/ar
  numerator=Q(F(1,2))+delta*ar
  assert numerator.lo>0
  lows=[r.lo,reachA.lo]
  if br.hi>0:lows.append(numerator.lo/br.hi)
  return ca.lo+min(lows)-Yu.hi
 E=Yu-ylo
 if code==7:return -E.hi
 assert code==8
 supp=(1+ap*ar+bp*br+(ap*br-bp*ar).ab())/2
 return -(qmax(ap*D+bp*E,ar*D+br*E)-supp).hi

def main():
 start=time.monotonic();base=Path(__file__).parent
 args=argparse.ArgumentParser()
 args.add_argument('--certificate',type=Path,default=base/'badfloor_mainheight_certificate.json')
 args.add_argument('--report',type=Path,default=base/'badfloor_mainheight_verification_report.json')
 parsed=args.parse_args()
 src=parsed.certificate;data=json.loads(src.read_text());events=data['events']
 root=((F(0),F(1)),(F(0),F(1)),(F(-23,405),F(23,60)),(F(23,30),F(13,12)))
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
   code=-tag-1;assert 0<=code<9
   reserve=leaf_reserve(box,code)
   assert reserve>0,('invalid exact leaf',idx,code,str(reserve),box)
   assert reserve>F(1,10000000000),('smaller than reported uniform reserve',idx,code,str(reserve))
   counts[code]+=1;leaves+=1;minimum=reserve if minimum is None else min(minimum,reserve)
 assert not stack,('incomplete tree',len(stack))
 assert len(events)==2*leaves-1
 result={'status':'EXACT_REPLAY_PASSED','scope':'complete 000/01 plus yP-hP<=1/10 implies yM1,yM2<-7/20; not the full mask',
 'nodes':len(events),'leaves':leaves,'max_depth':depth,'leaf_reasons':dict(sorted(counts.items())),
 'root_rationals':[[str(a),str(b)] for a,b in root], 'sqrt_scale':SCALE,
 'uniform_positive_leaf_reserve':'1/10000000000', 'minimum_exact_reserve':str(minimum),
 'discovery_tree_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
 'seconds':time.monotonic()-start,'arithmetic':'fractions.Fraction and math.isqrt only; no floating arithmetic; no producer import'}
 parsed.report.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='minimum_exact_reserve'},indent=2),flush=True)
if __name__=='__main__':main()
