"""Exact interval bounds for a common point of narrow ring arcs."""
from fractions import Fraction as F
from functools import lru_cache
from exact_arcs import asin_bounds,acos_bounds,PI_HI
if not __debug__:
 raise RuntimeError('Run without -O: exact comparisons use assertions.')
U=F(49013,10000);R0=F(11,10);R=F(5,4);HALF=F(27,40);POINT=F(3,2)
def asin_extended(x):
 assert -1<=x<=1
 if x<0:
  lo,hi=asin_bounds(-x);return -hi,-lo
 return asin_bounds(x)
def round_out(interval):
 scale=10**10;lo,hi=interval
 a=lo.numerator*scale//lo.denominator
 b=-((-hi.numerator*scale)//hi.denominator)
 return F(a,scale),F(b,scale)
@lru_cache(maxsize=None)
def sine_bounds(x):
 if x<0:
  lo,hi=sine_bounds(-x);return -hi,-lo
 assert 0<=x<=F(3,2)
 value=F(0);term=x
 for k in range(12):
  value+=term if k%2==0 else -term
  term*=x*x/F((2*k+2)*(2*k+3))
 return round_out((value,value+term))
@lru_cache(maxsize=None)
def cosine_bounds(x):
 if x<0:return cosine_bounds(-x)
 assert 0<=x<=F(3,2)
 value=F(0);term=F(1)
 for k in range(12):
  value+=term if k%2==0 else -term
  term*=x*x/F((2*k+1)*(2*k+2))
 return round_out((value,value+term))
def discard(box):
 a,A,b,B=box
 if A<b:return 'below-diagonal'
 if A*A+B*B<R0*R0:return 'inside-shell'
 if (a+F(1,2))**2+(b+F(1,2))**2>U:return 'outside-disk'
 return None
@lru_cache(maxsize=None)
def assess(box):
 a,A,b,B=box
 why=discard(box)
 if why:return why
 if a<F(3,4):return None
 assert A<=F(7,4) and B<=F(7,4)
 al=acos_bounds((A-F(1,2))/R)[0]
 ah=acos_bounds((a-F(1,2))/R)[1]
 bl=asin_extended((b-F(1,2))/R)[0]
 bh=asin_extended((B-F(1,2))/R)[1]
 cl=asin_extended(min(F(1),(b+F(1,2))/R))[0]
 ch=asin_extended(min(F(1),(B+F(1,2))/R))[1]
 low=(max(-ah,bl),max(-al,bh))
 high=(min(al,cl),min(ah,ch))
 if high[0]-low[1]>2*HALF:return 'wide-arc'
 # Any admissible own-frame arc contains its centre's radial direction,
 # which is in [0,pi/4]. Intersect with that global rotation restriction.
 lower=max(-HALF-low[1],-HALF-PI_HI/4)
 upper=min(HALF-high[0],HALF)
 if lower>upper:return 'empty-rotation'
 lower,upper=round_out((lower,upper))
 assert -F(3,2)<lower<=upper<F(3,2)
 sylo=sine_bounds(lower)[0];syhi=sine_bounds(upper)[1]
 largest=max(abs(lower),abs(upper))
 smallest=F(0) if lower<=0<=upper else min(abs(lower),abs(upper))
 cxlo=cosine_bounds(largest)[0];cxhi=cosine_bounds(smallest)[1]
 xlo,xhi=POINT*cxlo,POINT*cxhi
 ylo,yhi=-POINT*syhi,-POINT*sylo
 if xlo>A-F(1,2) and xhi<a+F(1,2) and ylo>B-F(1,2) and yhi<b+F(1,2):
  return 'common-point'
 return None
