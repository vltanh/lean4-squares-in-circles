"""Independent exact reconstruction of the new opposite-sign quarter row.

The companion is not imported. Circle derivatives are evaluated from the
chain rule, Taylor sums use different orders, and square bounds use a
different rational mesh. The accompanying note records the continuous audit.
"""
from fractions import Fraction as F
from math import factorial,isqrt
from pathlib import Path
from hashlib import sha256
import json

class B:
 def __init__(self,l,h=None):
  if isinstance(l,B):self.l,self.h=l.l,l.h
  else:self.l,self.h=F(l),F(l if h is None else h)
  assert self.l<=self.h
 def __add__(a,b):b=B(b);return B(a.l+b.l,a.h+b.h)
 __radd__=__add__
 def __neg__(a):return B(-a.h,-a.l)
 def __sub__(a,b):return a+-B(b)
 def __rsub__(a,b):return B(b)+-a
 def __mul__(a,b):
  b=B(b);v=[x*y for x in [a.l,a.h] for y in [b.l,b.h]];return B(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(a,b):
  b=B(b);assert not b.l<=0<=b.h;return a*B(1/b.h,1/b.l)
 def __rtruediv__(a,b):return B(b)/a
 def __pow__(a,n):
  if n==2:return B(0 if a.l<=0<=a.h else min(a.l*a.l,a.h*a.h),max(a.l*a.l,a.h*a.h))
  p=B(1)
  for _ in range(n):p=p*a
  return p
 def root(a):
  assert a.l>0;den=10**20
  l=F(isqrt(a.l.numerator*den*den//a.l.denominator),den)
  h=F(isqrt(a.h.numerator*den*den//a.h.denominator)+1,den)
  assert l*l<=a.l and h*h>a.h
  return B(l,h)

P=Path(__file__).resolve().parent;S=P.parents[1]/'proof_integration'
labels=json.loads((S/'wrong_0011011_labels.json').read_text())
expected={'P':('0','O+',[2478,0,93015,2363,-11055]),'R':('3','O+',[0,-1025,16031,0,63457])}
cf={}
for n,(role,key,row) in expected.items():
 assert labels['independent_roles'][role][key]==row
 cf[n]=[F(v,100000) for v in row]
Q=B(F(9789,2500));rootQ=Q.root();d=(Q/2).root()-F(1,2);a0=(Q-F(1,4)).root()-F(1,2);b1=(Q-F(9,4)).root()-F(1,2)
def trig(x):
 x=F(x)
 def part(o,n):return sum(((-1)**j*x**(o+2*j)/F(factorial(o+2*j)) for j in range(n+1)),F(0))
 return B(part(1,9),part(1,10)),B(part(0,9),part(0,10))
def arctan(x,n):
 x=F(x);return sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n+1)),F(0))
halfpi=B(8*arctan('1/5',25)-2*arctan('1/239',6),8*arctan('1/5',24)-2*arctan('1/239',7))
def arc(x):
 x=B(x);u=(Q-(x+F(1,2))**2).root();a=u-F(1,2)
 return a,u,-(x+F(1,2))/u,-Q/u**3
def label(n,x):
 x=B(x);a,u,ap,app=arc(x);c,p,q,r,t=cf[n]
 value=c+p*a+q*x+r*x*x+t*a*x
 first=p*ap+q+2*r*x+t*(ap*x+a)
 second=p*app+2*r+t*(app*x+2*ap)
 return value,first,second
checks=[]
def positive(name,value):
 value=B(value);assert value.l>0,(name,str(value.l))
 checks.append({'name':name,'strict_reserve':str(value.l)})
def gt(name,v,b):positive(name,B(v)-B(b))
def lt(name,v,b):positive(name,B(b)-B(v))

def cap(x):
 s,c=trig(x);Z=F(1,2)+c;Y=(Q-Z*Z).root();U=Z*c+Y*s;V=Y*c-Z*s;f=1-s/Y
 fp=(F(1,2)+(F(5,4)-Q)*c+c*c/2)/Y**3
 return V-F(1,2),U,V,f,fp
for lo,hi,bound in [('0','.1','2.25'),('.1','.2','1.39'),('.2','.3','.66')]:
 z0,U0,V0,f0,fp0=cap(lo);z1,U1,V1,f1,fp1=cap(hi)
 speed=U0*f1;upper_second=-V1*f1*f1-U1*fp0
 positive('axial upper second derivative sign '+lo,upper_second)
 _,rp,rpp=label('R',z1)
 gt('axial curvature '+lo+':'+hi,-rpp*speed**2-rp*upper_second,bound)
z,U,V,f,fp=cap('.15017')
gt('axial minimum reference',halfpi-F('.15017')-label('P',0)[0]-label('R',z)[0],'.8977853')
hp=-1+label('R',z)[1]*U*f
gt('axial reference slope lower',hp,'-.00001');lt('axial reference slope upper',hp,'.00001')
gt('aligned decisive endpoint',halfpi-label('P',b1)[0]-label('R',0)[0],'.8977861')

s,c=trig('.7')
for lo,hi,bound in [('0','.3','.966'),('.3','.5','.973'),('.5','.7','.993'),('.7','.8','.933'),('.8','.9','.924')]:
 u=arc(lo)[1];rh=(F(hi)+F(1,2))/arc(hi)[1]
 lt('P projection-speed row '+lo+':'+hi,label('P',hi)[1]*(u-c/(c+rh*s)),bound)
g=F('.83829');h=F('1.061')
for lo,hi,bound in [('.01','.1','-.33'),('.1','.2','-.31'),('.2','.3','-.29'),('.3','.4','-.25'),('.4','.5','-.19'),('.5','.6','-.11'),('.6','.7','-.015')]:
 sl,cl=trig(lo);sh,ch=trig(hi);nl=(g*g+h*h-2*g*h*sl).root();nh=(g*g+h*h-2*g*h*sh).root()
 lt('tail support curvature '+lo+':'+hi,-h*ch-rootQ*g*h*sl/nl+rootQ*g*g*h*h*cl**2/nh**3,bound)
for x,bound in [('.01','.8982'),('.7','.986')]:
 s,c=trig(x);n=(g*g+h*h-2*g*h*s).root()
 gt('tail support endpoint '+x,halfpi-F(x)-label('P',0)[0]-label('R',0)[0]-rootQ*n+h*c+(g+h)/2,bound)

z=d-F(1,2)
def ratio(x):
 x=B(x);a,u,_,_=arc(x);v=x+F(1,2);q=Q+1-2*u;K=(q-z*z).root()
 return (Q-u)/(u*q)+v*z/(u*q*K)
gt('target ratio initial reserve',ratio(0)-label('R',0)[1],'.001')
for lo,hi,bound in [('0','.2','.05'),('.2','.4','.21'),('.4','.6','.47'),('.6','.8','.89'),('.8','.9','1.65')]:
 x=B(lo,hi);a,u,_,_=arc(x);r=(x+F(1,2))/u;q=Q+1-2*u;K=(q-z*z).root()
 def nn(u):return 4*Q*u-2*u*u-Q*(Q+1)
 numerator=B(nn(B(u.l)).l,nn(B(u.h)).h)
 derivative=-r*numerator/(u*u*q*q)+z/(q*K)*(Q/u**3-2*r*r/q-r*r/K**2)
 gt('target ratio derivative '+lo+':'+hi,derivative-label('R',lo)[2],bound)
for name,value in [
 ('short-strip endpoint direction',F('.9269')-F('1.061')*F('.871')),
 ('upper exit denominator',F('.2905')*F('.921')-F('.5')*F('.39')),
 ('upper exit speed exceeds one',F('.86')*F('.921')-F('.39')-F('.4')),
 ('lower axis2 stationary direction',F('1.75')*F('.773')-1),
 ('axial late direction',F('.875')*F('1.203')-1),
 ('final scalar convexity weakening',F('.979')-F('.67')),
 ('strict final reserve',F('.89777')-F(17953,20000))]:positive(name,value)

names=['WRONG_0011011_OPPOSITE_OUTER_EDGE2_QUARTER_HAND_PROOF.md','verify_wrong_0011011_opposite_outer_edge2_quarter_hand.py','wrong_0011011_opposite_outer_edge2_quarter_hand_arithmetic.json']
replay=json.loads((S/names[2]).read_text());assert replay['comparison_count']==106
out={'status':'PASS','scope':'Independent continuous review, label binding and fixed-table reconstruction; full edge2(-,+) and reflected edge6',
     'independent_comparisons':len(checks),'companion_comparisons':106,'checks':checks,
     'sha256':{n:sha256((S/n).read_bytes()).hexdigest() for n in names}}
(P/'wrong_0011011_opposite_outer_edge2_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','independent_comparisons':len(checks),'companion_comparisons':106}))
