"""Independent Fraction/pair-interval reconstruction of the visibility target.

This file is an audit calculation, not a new accepted mathematical input.
It normalizes corner endpoints directly, uses a 2^-64 radical lattice,
and verifies a complete prefix partition of the full initial rectangle.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from collections import Counter
import hashlib,json
S=1<<64
def C(x):
 q=F(x);return(q,q)
def add(A,B):return(A[0]+B[0],A[1]+B[1])
def neg(A):return(-A[1],-A[0])
def sub(A,B):return add(A,neg(B))
def mul(A,B):
 z=[a*b for a in A for b in B];return(min(z),max(z))
def sq(A):return((F(0) if A[0]<=0<=A[1] else min(a*a for a in A)),max(a*a for a in A))
def div(A,B):
 assert B[0]>0;return mul(A,(1/B[1],1/B[0]))
def cut(A,B):
 l=max(A[0],B[0]);h=min(A[1],B[1]);return None if l>h else(l,h)
def root(A):
 assert A[1]>=0
 lo=max(F(0),A[0]);hi=A[1]
 a=isqrt(lo.numerator*S*S//lo.denominator)
 b=isqrt(hi.numerator*S*S//hi.denominator)
 if F(b*b,S*S)<hi:b+=1
 assert F(a*a,S*S)<=lo and F(b*b,S*S)>=hi
 return(F(a,S),F(b,S))
ONE=C(1);HALF=C(F(1,2));Q=C(F(99,70))
initial=((F(14,15),F(1)),(F(29,50),F(2,3)),(F(2,25),F(1)))
width=[h-l for l,h in initial]
def normal(X,Y):
 # X/sqrt(X^2+Y^2) increases in X and decreases in Y, both positive.
 assert X[0]>0 and Y[0]>0
 lower=root(C(X[0]*X[0]+Y[1]*Y[1]))
 upper=root(C(X[1]*X[1]+Y[0]*Y[0]))
 return(X[0]/lower[1],X[1]/upper[0])
def prove(box):
 d,h,t=box;a=sub(ONE,d);g=sub(ONE,h);b=root(sub(ONE,sq(t)))
 R2=add(sq(add(d,ONE)),C(F(1,4)))
 if R2[1]<=4:return 'R>2',None
 Y=add(add(g,b),t);X2=sub(R2,sq(Y))
 if X2[1]<=0:return 'positive X',None
 X=root(X2);x=cut(add(sub(X,b),t),(max(F(3,10),t[0]),d[1]))
 if x is None:return 'actual x',None
 X=cut(X,sub(add(x,b),t))
 if X is None:return 'lower circle identity',None
 screen=sub(mul(sub(d,x),t),mul(sub(h,HALF),b))
 if screen[1]<0:return 'real leaf screen',None
 w=add(x,a)
 if w[0]<=0 or X[0]<=0:return None,None
 c=normal(w,h);s=normal(h,w)
 N=add(mul(a,c),mul(h,s));K=mul(x,s)
 W2=sub(R2,sq(add(N,ONE)))
 if W2[1]<0:return 'upper circle real',None
 W=root(W2);rho=cut(sub(W,K),(F(7,8),F(1)))
 if rho is None:return 'original rho',None
 if W[0]<=0:return None,None
 delta=sub(ONE,rho)
 lam=cut(div(sub(K,mul(N,rho)),W),(F(0),F(197,925)))
 if lam is None:return 'upper proper mean',None
 A=sub(add(a,x),t);L0=mul(delta,s);H0=sub(ONE,mul(delta,c))
 G0=sub(mul(add(A,L0),H0),mul(Q,L0))
 G0b=add(mul(A,H0),mul(L0,sub(H0,Q)))
 z0=max(G0[0],G0b[0])
 B=add(add(mul(s,A),mul(sub(ONE,Q),c)),mul(delta,sub(sq(s),sq(c))))
 cs=mul(c,s)[0]
 assert cs>0
 u=max(lam[0],min(lam[1],-B[0]/(2*cs)))
 z1=z0+B[0]*u+cs*u*u
 L1=add(mul(lam,c),L0);H1=add(H0,mul(lam,s))
 direct1=sub(mul(add(A,L1),H1),mul(Q,L1))
 direct2=add(mul(A,H1),mul(L1,sub(H1,Q)))
 lower=min(z0,max(z1,direct1[0],direct2[0]))
 return ('both visibility targets',lower) if lower>0 else(None,None)

todo=[('',initial)];leaves=[];nodes=0
while todo:
 path,box=todo.pop();nodes+=1
 reason,margin=prove(box)
 if reason:
  leaves.append({'path':path,'reason':reason,'margin':None if margin is None else str(margin)});continue
 assert len(path)<45 and nodes<500000,(path,box)
 axis=max(range(3),key=lambda i:(box[i][1]-box[i][0])/width[i])
 mid=sum(box[axis],F(0))/2
 left=list(box);right=list(box);left[axis]=(box[axis][0],mid);right[axis]=(mid,box[axis][1])
 todo.extend([(path+'1',tuple(right)),(path+'0',tuple(left))])
paths={r['path'] for r in leaves};assert len(paths)==len(leaves)
while paths!={''}:
 depth=max(map(len,paths))
 parents={p[:-1] for p in paths if len(p)==depth}
 for p in parents:
  assert p+'0' in paths and p+'1' in paths
  paths.remove(p+'0');paths.remove(p+'1');paths.add(p)
assert nodes==2*len(leaves)-1
pos=[F(r['margin']) for r in leaves if r['margin'] is not None]
assert pos and min(pos)>0
payload=json.dumps(leaves,sort_keys=True,separators=(',',':')).encode()
record={'initial':[[str(v) for v in row] for row in initial],'bits':64,'normal_enclosure':'direct monotone endpoint normalization','nodes':nodes,'leaves':len(leaves),'reasons':dict(Counter(r['reason'] for r in leaves)),'maxdepth':max(len(r['path']) for r in leaves),'minimum':str(min(pos)),'prefix_cover':True,'digest':hashlib.sha256(payload).hexdigest(),'terminal_paths':leaves}
out=Path('/tmp/rooted_blocks_lower_tac_upper_c_visibility_independent_2026_10_28.json')
out.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='terminal_paths'},indent=2))
