"""Exact rational certificate for the unique strict-incoming S123 B star.

The three rows are the actual tilted strict-channel identity, the entire
actual tilted zero-t channel mean, and the actual aligned-South identity.
All arithmetic uses outward integer intervals at denominator 2**40.
The binary trees partition the full closed rational parameter boxes.
No sampled value, floating point, pose search or numerical tolerance
is used in any branch or assertion. See the companion scalar source.
"""
from collections import Counter
from fractions import Fraction as Q
from math import isqrt

D = 1 << 40

def floorq(q):
    return q.numerator // q.denominator

def ceilq(q):
    return -((-q.numerator) // q.denominator)

class I:
    __slots__ = ('lo', 'hi')
    def __init__(self, lo, hi):
        self.lo, self.hi = lo, hi
    @staticmethod
    def rational(q):
        q = Q(q)
        return I(floorq(q*D), ceilq(q*D))
    @staticmethod
    def range(lo, hi):
        return I(floorq(Q(lo)*D), ceilq(Q(hi)*D))
    def __add__(a,b):
        b=cv(b); return I(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo)
    def __sub__(a,b):return a+-cv(b)
    def __rsub__(a,b):return cv(b)+-a
    def __mul__(a,b):
        b=cv(b)
        v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return I(min(v)//D,-((-max(v))//D))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=cv(b)
        if b.lo<=0:raise ArithmeticError('nonpositive interval divisor')
        return a*I((D*D)//b.hi,-((-(D*D))//b.lo))
    def __rtruediv__(a,b):return cv(b)/a
    def sq(a):
        lo=0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi)
        hi=max(a.lo*a.lo,a.hi*a.hi)
        return I(lo//D,-((-hi)//D))
    def sqrt(a):
        if a.hi<0:raise ArithmeticError('negative square root')
        lo=isqrt(max(0,a.lo)*D)
        v=a.hi*D; hi=isqrt(v)
        if hi*hi<v:hi+=1
        return I(lo,hi)
    def intersect(a,b):
        return I(max(a.lo,b.lo),min(a.hi,b.hi))
    def empty(a):return a.lo>a.hi
    def above(a,q):return Q(a.lo,D)>q
    def below(a,q):return Q(a.hi,D)<q

def cv(x):return x if isinstance(x,I) else I.rational(x)

def bound(v,lo,hi):return v.intersect(I.range(lo,hi))
def check(kind,box):
 e,z=(I.range(*v) for v in box);d=1+e;R2=(d+1).sq()+Q(1,4)
 if kind=='aligned':
  A=z
  h=(e*(2*A-e)).sqrt();F=1-h
  x=1-e/A;t=h/A
 else:
  k=z
  if kind=='strict':
   a=1-2*e*(d-k.sq())/(d+k).sq()
   aa=bound(a,0,1)
   if aa.empty():return 'empty',None
   a=aa;b0=(1-a.sq()).sqrt()
   ratio=b0*k/(1-a*k);x=1/(1+ratio.sq()).sqrt();t=ratio*x
  else:
   a=(1-e)/d;b0=2*e.sqrt()/d;x=cv(1);t=cv(0)
  F=1-d*b0;A=a*(d-k)
 if F.hi<=cv(Q(37,50)).lo or A.hi<=cv(Q(1,2)).lo or A.lo>=D:return 'empty',None
 F=bound(F,Q(37,50),1);A=bound(A,Q(1,2),1)
 if F.empty() or A.empty():return 'empty',None
 P2=A.sq()+F.sq();K=(R2-P2-1)/2;J2=P2-K.sq()
 if J2.hi<=cv(Q(1,4)).lo or J2.lo>=D:return 'empty',None
 J=bound(J2,Q(1,4),1).sqrt()
 c=(A*J+F*K)/P2;s=(A*K-F*J)/P2
 if s.hi<=0 or c.hi<=0 or A.lo>=c.hi:return 'empty',None
 c=bound(c,0,1);s=bound(s,0,Q(3,7))
 if c.empty() or s.empty():return 'empty',None
 delta=J/(A+s)
 margins={}
 qx=c-A;qy=F+s;qn=x*qx-t*qy
 if qn.hi>e.lo:
  gf=t*c+x*(s-delta)
  if gf.hi>=0:return 'split',None
  margins['near_sign']=-gf.hi
 qx=c-A-c*s*delta;qy=F+s+c.sq()*delta;qn=x*qx-t*qy;qf=t*qx+x*qy
 if qn.hi>e.lo:
  inward=(qx+c).sq()+(qy+s).sq()-R2
  chord=(d-qn).sq()+(qf-Q(1,2)).sq()-2
  margin=max(inward.lo,chord.lo)
  if margin<=0:return 'split',None
  margins['side_separation']=margin
 return 'pass',margins

def run(kind):
 initial=((Q(0),Q(1,60)),(Q(1,2),Q(61,60)) if kind=='aligned' else (Q(0),Q(31,60)))
 stack=[(initial,0)];count=Counter();depths=Counter();mins={}
 while stack:
  box,dep=stack.pop()
  try:status,res=check(kind,box)
  except ArithmeticError:status,res='split',None
  count[status]+=1;depths[dep]+=1
  if status=='split':
   if dep>=40:raise RuntimeError((kind,'unresolved',box,count))
   j=max(range(2),key=lambda j:(box[j][1]-box[j][0])*(20 if j==0 else 1))
   l,h=box[j];m=(l+h)/2
   for seg in [(l,m),(m,h)]:
    child=list(box);child[j]=seg;stack.append((tuple(child),dep+1))
  elif status=='pass':
   for k,v in res.items():mins[k]=min(mins.get(k,10*D),v)
 assert count['pass']+count['empty']==count['split']+1
 print(kind,dict(count),'maxdepth',max(depths),flush=True)
 print('depths',dict(sorted(depths.items())),flush=True)
 print('margins',mins,flush=True)
if __name__ == '__main__':
    for kind in ('strict', 'side', 'aligned'):
        run(kind)
