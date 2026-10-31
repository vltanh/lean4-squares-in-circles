#!/usr/bin/env python3
"""UNFINISHED exploratory interval search; unresolved cells are retained.

No proof or case closure is asserted. See RADIAL_VERTICAL_SOURCE_RESEARCH_HANDOFF.md.
"""

from fractions import Fraction as Q
class I:
 def __init__(self,a,b=None):self.a=Q(a);self.b=Q(a if b is None else b)
 def __add__(x,y):
  if not isinstance(y,I):y=I(y)
  return I(x.a+y.a,x.b+y.b)
 __radd__=__add__
 def __neg__(x):return I(-x.b,-x.a)
 def __sub__(x,y):return x+-I(y) if not isinstance(y,I) else x+-y
 def __rsub__(x,y):return I(y)+-x
 def __mul__(x,y):
  if not isinstance(y,I):y=I(y)
  a=[x.a*y.a,x.a*y.b,x.b*y.a,x.b*y.b];return I(min(a),max(a))
 __rmul__=__mul__
 def __truediv__(x,y):
  if not isinstance(y,I):y=I(y)
  assert y.a*y.b>0
  return x*I(1/y.b,1/y.a)
 def __rtruediv__(x,y):return I(y)/x
from collections import Counter
D=I(Q(140,99),Q(99,70))

def classify(x,y):
 if x.a>=y.b:return 'normal'
 a=(1-x*x)/(1+x*x);b=2*x/(1+x*x)
 s=(1-y*y)/(1+y*y);r=2*y/(1+y*y)
 if r.a>=s.b:return 'steep'
 al=r+a-D
 if al.b<0:return 'inset'
 U=1+D-r-a/2;W=2+b/2
 denA=2*(W*a+1-U*b)
 if denA.a<=0:return None
 LA=(U*U+W*W-Q(5,4))/denA
 if LA.b<Q(9,10) or LA.a>Q(17,16):return 'radius_A'
 LB=(2+2*(r+s)+a*(1+r)-b*(1+s))/(2*(1+b*(1+r)+a*(1+s)))
 if LB.b<Q(9,10) or LB.a>Q(17,16):return 'radius_B'
 G=LA-LB
 if G.a>0 or G.b<0:return 'circle'
 L=I(max(LA.a,LB.a,Q(9,10)),min(LA.b,LB.b,Q(17,16)))
 u=U+L*b;H=W-L*a;v=1+r+a/2-L*b;B=1+s-L*a-b/2;w=L*b+a/2
 if H.b<=Q(1,2) or B.b<=Q(1,2):return 'unique'
 if u.b<Q(4,3) or v.b<Q(4,3):return 'position'
 T=(u*B-H*w)*(v*s-B*r)-u*B*(s-r)
 if T.a>0:return 'torque'
 return None

stack=[(I(0,Q(5,12)),I(Q(1,5),Q(5,12)),0)];counts=Counter();maxdepth=0;unresolved=[];n=0
while stack:
 x,y,depth=stack.pop();n+=1
 result=classify(x,y)
 if result:counts[result]+=1;maxdepth=max(maxdepth,depth);continue
 if depth>=12:unresolved.append((x,y,depth));continue
 # bisect longer interval, retaining every closed boundary
 if x.b-x.a>=y.b-y.a:
  mid=(x.a+x.b)/2;stack.extend([(I(x.a,mid),y,depth+1),(I(mid,x.b),y,depth+1)])
 else:
  mid=(y.a+y.b)/2;stack.extend([(x,I(y.a,mid),depth+1),(x,I(mid,y.b),depth+1)])
print(n,counts,'maxdepth',maxdepth,'unresolved',len(unresolved))
for x,y,de in unresolved[:5]:print(float(x.a),float(x.b),float(y.a),float(y.b))
