#!/usr/bin/env python3
"""Exact outward-integer SAT cover for the three rectangles in
S123_ZERO_CHANNEL_AXIS_MIDDLE_NEAR_EXTRA_EXCLUSION.md.
No floating point, numerical optimizer, external library, or input data.
"""
from collections import Counter
N=1<<40

def down(p,q=N):return p//q
def up(p,q=N):return -((-p)//q)
def point(p,q=1):return (down(p*N,q),up(p*N,q))
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[1],-a[0])
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 x=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]]
 return(down(min(x)),up(max(x)))
def half(a):return(down(a[0],2),up(a[1],2))
def cs(z):
 lo,hi=z
 return ((down((N*N-hi*hi)*N,N*N+hi*hi),up((N*N-lo*lo)*N,N*N+lo*lo)),(down(2*lo*N*N,N*N+lo*lo),up(2*hi*N*N,N*N+hi*hi)))
rects=[tuple(point(p,q) for p,q in [(-99,100),(0,1),(-23,1000),(3,4)]),tuple(point(p,q) for p,q in [(1,7000),(1,1),(-1,2),(1,2)]),tuple(point(p,q) for p,q in [(-7,4),(-199,200),(-9,20),(-1,4)])]
hh=point(1,2)

def check(box):
 a,b,z=box;c,s=cs(z);X=sub(mul(a,c),mul(b,s));Y=add(mul(a,s),mul(b,c));rad=half(add(c,s))
 exlo=sub(X,rad);exhi=add(X,rad);eylo=sub(Y,rad);eyhi=add(Y,rad)
 au=sub(a,hh);bu=add(a,hh);av=sub(b,hh);bv=add(b,hh)
 for i,(xl,xh,yl,yh) in enumerate(rects):
  mg=[exhi[0]-xl[1],xh[0]-exlo[1],eyhi[0]-yl[1],yh[0]-eylo[1]]
  if min(mg)<=0:continue
  rumin=add(mul(xl,c),mul(yl,s));rumax=add(mul(xh,c),mul(yh,s));rvmin=sub(mul(yl,c),mul(xh,s));rvmax=sub(mul(yh,c),mul(xl,s))
  mg +=[bu[0]-rumin[1],rumax[0]-au[1],bv[0]-rvmin[1],rvmax[0]-av[1]]
  if min(mg)>0:return i,min(mg)
 return None
stack=[(((-5*N//8,5*N//8),(-5*N//8,5*N//8),(0,N)),0)]
cnt=Counter();minm=[N]*3;maxd=0;vis=0
while stack:
 box,dep=stack.pop();vis+=1;res=check(box)
 if res is not None:
  i,m=res;cnt[i]+=1;minm[i]=min(minm[i],m);maxd=max(maxd,dep);continue
 if dep>=70:print('FAILED',box,flush=True);raise SystemExit(1)
 widths=[box[0][1]-box[0][0],box[1][1]-box[1][0],(box[2][1]-box[2][0])*5//4]
 j=max(range(3),key=lambda j:widths[j]);lo,hi=box[j];mid=(lo+hi)//2
 if mid==lo:print('PRECISION FAILED');raise SystemExit(1)
 left=list(box);right=list(box);left[j]=(lo,mid);right[j]=(mid,hi);stack.append((tuple(right),dep+1));stack.append((tuple(left),dep+1));cnt['split']+=1
 if vis%200000==0:print('progress',vis,'stack',len(stack),'depth',dep,flush=True)
assert cnt == Counter({'split':876,0:92,1:388,2:397})
assert vis == 1753 and maxd == 27
assert minm == [575796686,45834217,261885178]
assert min(minm) > 0
print('PASS',dict(cnt),'visited',vis,'depth',maxd,'min_margins',minm,'N',N,flush=True)
