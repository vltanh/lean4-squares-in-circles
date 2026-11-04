"""Independent directed-integer replay of the oriented endpoint toll.

No producer, NumPy or numerical optimizer imports. All interval quantities
are integer multiples of2^-64, with rounding outward after every operation.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json,hashlib,time
if not __debug__:raise RuntimeError('Exact replay requires assertions; Python -O is unsupported')
D=1<<64
class J:
 def __init__(self,a,b=None,raw=False):
  if raw:self.lo=int(a);self.hi=int(a if b is None else b)
  else:
   x=F(a)*D;y=F(a if b is None else b)*D
   self.lo=x.numerator//x.denominator;self.hi=-((-y.numerator)//y.denominator)
  assert self.lo<=self.hi
 def __add__(self,t):t=j(t);return J(self.lo+t.lo,self.hi+t.hi,True)
 __radd__=__add__
 def __neg__(self):return J(-self.hi,-self.lo,True)
 def __sub__(self,t):return self+-j(t)
 def __rsub__(self,t):return j(t)+-self
 def __mul__(self,t):
  t=j(t);v=[self.lo*t.lo,self.lo*t.hi,self.hi*t.lo,self.hi*t.hi]
  return J(min(v)//D,-((-max(v))//D),True)
 __rmul__=__mul__
 def __truediv__(self,t):
  t=j(t);assert t.lo>0
  vals=[F(self.lo*D,t.lo),F(self.lo*D,t.hi),F(self.hi*D,t.lo),F(self.hi*D,t.hi)]
  low=min(vals);high=max(vals)
  return J(low.numerator//low.denominator,-((-high.numerator)//high.denominator),True)
 def __rtruediv__(self,t):return j(t)/self
 def sq(self):
  lo=0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi)
  hi=max(self.lo*self.lo,self.hi*self.hi)
  return J(lo//D,-((-hi)//D),True)
 def root(self):
  assert self.lo>=0
  low=isqrt(self.lo*D);high=isqrt(self.hi*D)
  if high*high<self.hi*D:high+=1
  return J(low,high,True)
 def abs(self):return J(0 if self.lo<=0<=self.hi else min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)),True)
 def pos(self):return J(max(0,self.lo),max(0,self.hi),True)
def j(x):return x if isinstance(x,J)else J(x)

def value(kind,box):
 z=J(*box[-1]);den=1+z.sq();al=(1-z.sq())/den;be=2*z/den
 a,b,k=F(46),F(27,2),F(207,16)
 if kind=='B_owned':
  c=J(*box[0]);s=(1-c.sq()).root()
  # Identity obtained by resolving the two main support coordinates.
  support=a*(al+be)+k*((c*al-s*be).pos()+(c*be+s*al).pos())
 elif kind.startswith('Mv_'):c,s=be,al;support=a*(al+be)+k
 else:assert kind.startswith('Mu_');c,s=-al,be;support=a*(al+be)
 length_main=(a*a+k*k+(2*a*k)*c).root()
 radicand_other=b*b+k*k-(2*b*k)*c
 length_other=radicand_other.root()
 circle=j(F(1105,256)).root()*(length_main+length_other)
 branch=kind[-1:]if kind!='B_owned'else'N'
 if branch=='E':other=b+k*(s+(-c).pos())
 elif branch=='N':other=(b*c.abs()+2*b*s+(k-b*c).abs()+k)/2
 else:
  assert branch=='D'
  other=(radicand_other+b*b-(b*k)*c+(2*b*k)*s+k*(k-b*c).abs())/(2*length_other)
 toll=F(1265,32)*be-F(119,2)*(1-al)
 return F(211,4)-circle+support+other-toll

def analytic_checks():
 r=F(24,23)
 assert F(399,401)>F(99,100)
 assert F(121,125)**2<F(15,16)
 assert -F(1,40)+F(121,125)*F(99,100)>0
 assert F(125,484)*(1+r)+F(1,10)-F(1,2)-r==F(-50969,55660)<0
 assert F(1,10)-F(1,2)==F(-2,5)<0
 assert F(99,100)*(F(1,4)+F(121,125)-r)-F(1,40)+r*F(121,125)-1-F(1,8)==F(37793,1150000)>0
 # Exact sharp tangent constants, not numerical square roots.
 a,b,k,Q=F(46),F(27,2),F(207,16),F(1105,256)
 assert a*a+k*k==23**2*Q and b*b+k*k==9**2*Q
 assert 32*Q==a+b+2*k+F(211,4)
 assert a/F(23)-b/F(9)==F(1,2)
 assert a-k/2==F(1265,32)and a+b==F(119,2)
 assert b>k and F(5,12)<F(1,2)
 return 13

def check(packet):
 started=time.monotonic();checks=analytic_checks()
 assert packet['schema']=='oriented_good_endpoint_toll_interval_cover_v1'
 assert packet['root_upper']=='5/12'and packet['toll_beta_coefficient']=='1265/32'and packet['toll_alpha_deficit_coefficient']=='119/2'
 assert packet['analytic_neighborhood']==dict(c=['-1/4','1/4'],z=['0','1/20'])
 expected=[('B_owned',((F(-1),F(-1,4)),(F(0),F(5,12)))),('B_owned',((F(1,4),F(1)),(F(0),F(5,12)))),('B_owned',((F(-1,4),F(1,4)),(F(1,20),F(5,12))))]
 expected +=[(name,((F(0),F(5,12)),))for name in('Mv_D','Mu_E','Mu_N','Mu_D')]
 assert len(packet['roots'])==len(expected)
 leaves=0;depth_max=0;minimum=None;reports=[]
 for root,(kind,initial)in zip(packet['roots'],expected):
  assert root['kind']==kind and tuple(tuple(map(F,v))for v in root['box'])==initial
  stack=[(root,initial,0)];local=0
  while stack:
   node,box,depth=stack.pop();depth_max=max(depth_max,depth)
   if 'split'in node:
    assert 'lower'not in node;axis=node['split'];assert type(axis)is int and 0<=axis<len(box)
    assert len(node['children'])==2;a,b=box[axis];mid=(a+b)/2
    for side in(0,1):
     child=list(box);child[axis]=(a,mid)if side==0 else(mid,b)
     stack.append((node['children'][side],tuple(child),depth+1))
   else:
    assert F(node['lower'])>0;enclosure=value(kind,box);assert enclosure.lo>0,(kind,box,enclosure.lo)
    reserve=F(enclosure.lo,D);minimum=reserve if minimum is None else min(minimum,reserve)
    leaves+=1;local+=1
  reports.append(dict(kind=kind,root=[[str(a),str(b)]for a,b in initial],leaves=local))
  print(kind,local,'PASS',flush=True)
 assert leaves==packet['leaves']and depth_max==packet['maxdepth']and packet['frontier']==0
 return dict(status='PASS_COMPLETE_ORIENTED_ENDPOINT_TOLL_COVER',leaves=leaves,frontier=0,
    maxdepth=depth_max,least_integer_replay_reserve=str(minimum),analytic_rational_checks=checks,roots=reports,seconds=time.monotonic()-started)
if __name__=='__main__':
 here=Path(__file__).resolve().parent;src=here/'ORIENTED_GOOD_ENDPOINT_TOLL_COVER.json'
 result=check(json.loads(src.read_text()));result['sources']={p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in(src,Path(__file__))}
 (here/'ORIENTED_GOOD_ENDPOINT_TOLL_EXACT_REPLAY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
