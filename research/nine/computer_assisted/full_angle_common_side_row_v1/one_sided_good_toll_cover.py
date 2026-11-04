"""Rational interval discovery for the oriented good endpoint tilt toll.

The zero neighborhood is analytic and separately derived. Every other
closed scalar root is covered by exact positive interval leaves.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json,time
BITS=72;DEN=1<<BITS
class I:
 def __init__(self,a,b=None):self.a=F(a);self.b=F(a if b is None else b);assert self.a<=self.b
 def __add__(self,x):x=ci(x);return I(self.a+x.a,self.b+x.b)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a)
 def __sub__(self,x):return self+-ci(x)
 def __rsub__(self,x):return ci(x)+-self
 def __mul__(self,x):
  x=ci(x);v=[self.a*x.a,self.a*x.b,self.b*x.a,self.b*x.b];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(self,x):
  x=ci(x);assert x.a>0 or x.b<0;return self*I(1/x.b,1/x.a)
 def __rtruediv__(self,x):return ci(x)/self
 def square(self):return I(0 if self.a<=0<=self.b else min(self.a*self.a,self.b*self.b),max(self.a*self.a,self.b*self.b))
 def sqrt(self):
  assert self.a>=0
  lo=isqrt(self.a.numerator*DEN*DEN//self.a.denominator)
  hi=isqrt(self.b.numerator*DEN*DEN//self.b.denominator)
  if F(hi*hi,DEN*DEN)<self.b:hi+=1
  return I(F(lo,DEN),F(hi,DEN))
 def absolute(self):return I(0 if self.a<=0<=self.b else min(abs(self.a),abs(self.b)),max(abs(self.a),abs(self.b)))
 def positive(self):return I(max(0,self.a),max(0,self.b))
def ci(x):return x if isinstance(x,I)else I(x)
A=F(46);B=F(27,2);K=F(207,16);CAP=F(211,4);Q=F(1105,256)

def evaluate(kind,box):
 z=I(*box[-1]);zz=z.square();alpha=(1-zz)/(1+zz);beta=2*z/(1+zz)
 if kind=='B_owned':
  c=I(*box[0]);s=(1-c.square()).sqrt()
  pm=A*(alpha+beta)+K*((c*alpha-s*beta).positive()+(c*beta+s*alpha).positive())
 else:
  branch,candidate=kind.split('_')
  if branch=='Mv':c=beta;s=alpha;pm=A*(alpha+beta)+K
  else:assert branch=='Mu';c=-alpha;s=beta;pm=A*(alpha+beta)
 la=(A*A+K*K+2*A*K*c).sqrt();lb=(B*B+K*K-2*B*K*c).sqrt()
 H=I(Q).sqrt()*(la+lb)
 N=(B*c.absolute()+2*B*s+(K-B*c).absolute()+K)/2
 if kind=='B_owned' or candidate=='N':pb=N
 elif candidate=='E':pb=B+K*(s+(-c).positive())
 else:
  assert candidate=='D'
  # Reconstruct the side-length expression; lb^2 is the exact radicand.
  rad=B*B+K*K-2*B*K*c
  pb=(rad+B*B-B*K*c+2*B*K*s+K*(K-B*c).absolute())/(2*lb)
 toll=(A-K/2)*beta-(A+B)*(1-alpha)
 return CAP-H+pm+pb-toll
ROOTS=[('B_owned',((F(-1),F(-1,4)),(F(0),F(5,12)))),
       ('B_owned',((F(1,4),F(1)),(F(0),F(5,12)))),
       ('B_owned',((F(-1,4),F(1,4)),(F(1,20),F(5,12))))]
ROOTS +=[(name,((F(0),F(5,12)),))for name in('Mv_D','Mu_E','Mu_N','Mu_D')]

def build():
 start=time.monotonic();roots=[];count=0;least=None;maxdepth=0
 for kind,rootbox in ROOTS:
  root={'kind':kind,'box':[[str(a),str(b)]for a,b in rootbox]};stack=[(root,rootbox,0)]
  local=0
  while stack:
   node,box,depth=stack.pop();v=evaluate(kind,box);maxdepth=max(maxdepth,depth)
   if v.a>0:
    node['lower']=str(v.a);count+=1;local+=1
    least=v.a if least is None else min(least,v.a)
   else:
    assert depth<35,(kind,box,v.a,v.b)
    # Normalize the differently scaled root coordinates before subdivision.
    axis=max(range(len(box)),key=lambda i:(box[i][1]-box[i][0])/(rootbox[i][1]-rootbox[i][0]))
    a,b=box[axis];mid=(a+b)/2;node['split']=axis;node['children']=[{},{}]
    for side in(1,0):
     child=list(box);child[axis]=(a,mid)if side==0 else(mid,b);stack.append((node['children'][side],tuple(child),depth+1))
  roots.append(root);print(kind,root['box'],'leaves',local,'total',count,'seconds',round(time.monotonic()-start,2),flush=True)
 return dict(schema='oriented_good_endpoint_toll_interval_cover_v1',root_upper='5/12',
  toll_beta_coefficient='1265/32',toll_alpha_deficit_coefficient='119/2',
  analytic_neighborhood=dict(c=['-1/4','1/4'],z=['0','1/20']),
  roots=roots,leaves=count,frontier=0,least_reserve=str(least),maxdepth=maxdepth,seconds=time.monotonic()-start)
if __name__=='__main__':
 r=build();p=Path(__file__).with_name('ORIENTED_GOOD_ENDPOINT_TOLL_COVER.json');p.write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items()if k!='roots'})
