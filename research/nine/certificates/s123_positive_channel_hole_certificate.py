"""Exact complete positive-channel hole scalar certificate.
All operations are outward integer intervals on2**-40; no samples.
"""
from fractions import Fraction as F
from math import isqrt
from collections import Counter
N=1<<40
def dn(p,q=N):return p//q
def up(p,q=N):return -((-p)//q)
def I(p,q=1):return dn(p*N,q),up(p*N,q)
def add(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[1],-a[0]
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 z=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]]
 return dn(min(z)),up(max(z))
def div(a,b):
 assert b[0]>0
 return mul(a,(dn(N*N,b[1]),up(N*N,b[0])))
def square(a):
 z=[a[0]*a[0],a[1]*a[1]]
 return dn(0 if a[0]<=0<=a[1] else min(z)),up(max(z))
def root(a):
 assert a[0]>=0
 l=isqrt(a[0]*N);h=isqrt(a[1]*N)
 if h*h<a[1]*N:h+=1
 return l,h
one=I(1);two=I(2)
def check(box):
 eps,V,t=box;d=add(one,eps);F0=sub(one,V)
 x=root(sub(one,square(t)))
 r=div(sub(eps,mul(V,t)),x)
 if r[0]>eps[1] or r[1]<-eps[1]:return 'r',1
 R2=add(square(add(d,one)),I(1,4))
 rad=sub(R2,square(add(F0,one)))
 if rad[1]<0:return 'rad',1
 W=root((max(0,rad[0]),rad[1]))
 if W[0]>=N or W[1]<=N//2:return 'W',1
 u=sub(one,W)
 q=sub(mul(u,x),mul(F0,t))
 if q[1]<=eps[0]:return 'q',1
 p=add(mul(u,t),mul(F0,x))
 T=sub(mul(V,x),mul(r,t))
 if T[1]<=0:return 'T',1
 area=div(sub(sub(add(add(d,mul(add(d,one),T)),mul(u,F0)),mul(r,add(one,F0))),mul(q,sub(one,p))),two)
 gap=sub(I(3,4),area)
 if gap[0]>0:return 'pass',gap[0]
 return None
stack=[(((I(0)[0],I(1,60)[1]),(I(1,50)[0],I(13,50)[1]),(0,I(3,5)[1])),0)]
cnt=Counter();mn=N;depth=vis=0
while stack:
 row,dep=stack.pop();vis+=1;ans=check(row)
 if ans:
  k,m=ans;cnt[k]+=1;depth=max(depth,dep)
  if k=='pass':mn=min(mn,m)
  continue
 if dep>=70:print('FAILED',row,dict(cnt),vis,flush=True);raise SystemExit(2)
 ws=[(row[0][1]-row[0][0])*60,(row[1][1]-row[1][0])*25//6,(row[2][1]-row[2][0])*5//3]
 j=max(range(3),key=lambda k:ws[k]);lo,hi=row[j];md=(lo+hi)//2
 if md==lo:raise RuntimeError('precision')
 l=list(row);r=list(row);l[j]=(lo,md);r[j]=(md,hi)
 stack.append((tuple(r),dep+1));stack.append((tuple(l),dep+1));cnt['split']+=1
 if vis%200000==0:print('PROGRESS',vis,dict(cnt),dep,len(stack),flush=True)
assert cnt==Counter({'split':404,'pass':285,'r':74,'q':43,'W':3})
assert vis==809 and depth==15 and mn==19715476
assert mn>0
print('PASS',dict(cnt),'visited',vis,'depth',depth,'min',mn,'N',N,flush=True)

