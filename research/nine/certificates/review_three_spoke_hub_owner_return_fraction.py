"""Independent exact Fraction enclosure of the coupled H3 return scalars.
No author checker or interval implementation is imported.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import hashlib,json
from argparse import ArgumentParser
class I:
 __slots__=('lo','hi')
 def __init__(self,a,b=None):self.lo=F(a);self.hi=F(a if b is None else b)
 def cv(self,o):return o if isinstance(o,I) else I(o)
 def __add__(self,o):
  o=self.cv(o);return I(self.lo+o.lo,self.hi+o.hi)
 __radd__=__add__
 def __neg__(self):return I(-self.hi,-self.lo)
 def __sub__(self,o):return self+-self.cv(o)
 def __rsub__(self,o):return self.cv(o)+-self
 def __mul__(self,o):
  o=self.cv(o);vs=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi];return I(min(vs),max(vs))
 __rmul__=__mul__
 def __truediv__(self,o):
  o=self.cv(o)
  if o.lo<=0<=o.hi:raise ZeroDivisionError
  return self*I(1/o.hi,1/o.lo)
 def __rtruediv__(self,o):return self.cv(o)/self
 def sq(self):
  if self.lo>=0:return I(self.lo*self.lo,self.hi*self.hi)
  if self.hi<=0:return I(self.hi*self.hi,self.lo*self.lo)
  return I(0,max(self.lo*self.lo,self.hi*self.hi))
 def sqrt(self):
  if self.lo<0:raise ValueError
  D=1<<64
  def bounds(x):
   k=isqrt((x.numerator*D*D)//x.denominator)
   return F(k,D),F(k+1,D)
  return I(bounds(self.lo)[0],bounds(self.hi)[1])

def evaluate(zz,pp):
 zl,zh=zz;z=I(zl,zh);p=I(*pp)
 a=I((1-zh*zh)/(1+zh*zh),(1-zl*zl)/(1+zl*zl))
 b=I(2*zl/(1+zl*zl),2*zh/(1+zh*zh))
 H=b+a*p;t=1-H;w=a-b*(1+p)
 guards=[a-b,b-a+p*(a+b),b-a*p,t,w]
 if any(q.hi<=0 for q in guards):return ('empty',None)
 den=1-p*H
 if den.lo<=0 or a.lo<=0:return ('split',None)
 v=t/den;x=w/a;y0=a-t
 E=(1+x.sq()).sqrt();L=(1+v.sq()).sqrt()
 A=(1+b+x*y0)/E;B=(x*(1+b)-y0)/E
 g=(x+v)/(E*L);h=(1-x*v)/(E*L)
 k1=1-A+g
 if k1.hi<=0:return ('empty',None)
 margins=[1-B-h-F(1,3),F(1,8)-k1,h-F(3,5),g.sq()-g+B*g+h*(A-1)]
 if all(q.lo>0 for q in margins):return ('positive',[q.lo for q in margins])
 return ('split',None)

def main():
 parser=ArgumentParser(description=__doc__);parser.add_argument("--output",type=Path);args=parser.parse_args()
 zinitial=(F(19,100),F(5,12));pinitial=(F(0),F(1));zw=zinitial[1]-zinitial[0]
 stack=[(zinitial,pinitial,0)];vis=pos=empty=depth=splits=0;mins=[None]*4
 while stack:
  zz,pp,dep=stack.pop();vis+=1;depth=max(depth,dep)
  status,data=evaluate(zz,pp)
  if status=='empty':empty+=1;continue
  if status=='positive':
   pos+=1
   for i,q in enumerate(data):mins[i]=q if mins[i] is None else min(mins[i],q)
   continue
  if dep>=60:raise RuntimeError(('unresolved',zz,pp,dep))
  splits+=1
  if (zz[1]-zz[0])/zw>=pp[1]-pp[0]:
   m=(zz[0]+zz[1])/2;stack.extend([((m,zz[1]),pp,dep+1),((zz[0],m),pp,dep+1)])
  else:
   m=(pp[0]+pp[1])/2;stack.extend([(zz,(m,pp[1]),dep+1),(zz,(pp[0],m),dep+1)])
  if vis%100000==0:print('progress',vis,pos,empty,depth,flush=True)
 assert pos+empty==splits+1 and vis==2*splits+1
 out={'domain':{'z':['19/100','5/12'],'p':['0','1']},'implementation':'independent Fraction arithmetic, exact monotone a,b endpoints; independent 2^-64 radical lattice','visits':vis,'positive_terminals':pos,'empty_terminals':empty,'max_depth':depth,'splits':splits,'minimum_lower_margins':list(map(str,mins))}
 if args.output is not None:args.output.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2),flush=True)
if __name__=='__main__':main()
