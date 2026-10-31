#!/usr/bin/env python3
"""Exact outward-integer near-extra cover for four fixed occupied rectangles.
The complete physical inclusions and actual distance guard are stated in
S123_POSITIVE_CHANNEL_RADIAL_MIDDLE_COMPLETE_EXCLUSION.md.
No floats, sampled poses, solver calls, or input data are used.
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
rects=[tuple(point(p,q) for p,q in [(-99,100),(-1,250),(-1,25),(3,4)]),tuple(point(p,q) for p,q in [(1,20),(9,10),(-1,4),(1,4)]),tuple(point(p,q) for p,q in [(-7,4),(-251,250),(-9,20),(-1,5)]),tuple(point(p,q) for p,q in [(-1,200),(9,10),(-3,8),(-1,8)])]
hh=point(1,2)

def check(box):
 a,b,z=box
 da=max(0,a[0]-N//2,-a[1]-N//2);db=max(0,b[0]-N//2,-b[1]-N//2)
 if 64*(da*da+db*db)>N*N:return 4,64*(da*da+db*db)-N*N
 c,s=cs(z);X=sub(mul(a,c),mul(b,s));Y=add(mul(a,s),mul(b,c));rad=half(add(c,s))
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
cnt=Counter();minm=[N]*len(rects);maxd=0;vis=0
while stack:
 box,dep=stack.pop();vis+=1;res=check(box)
 if res is not None:
  i,m=res;cnt[i]+=1
  if i<4:minm[i]=min(minm[i],m)
  maxd=max(maxd,dep);continue
 if dep>=70:print('FAILED',box,flush=True);raise SystemExit(1)
 widths=[box[0][1]-box[0][0],box[1][1]-box[1][0],(box[2][1]-box[2][0])*5//4]
 j=max(range(3),key=lambda j:widths[j]);lo,hi=box[j];mid=(lo+hi)//2
 if mid==lo:print('PRECISION FAILED');raise SystemExit(1)
 left=list(box);right=list(box);left[j]=(lo,mid);right[j]=(mid,hi);stack.append((tuple(right),dep+1));stack.append((tuple(left),dep+1));cnt['split']+=1
 if vis%200000==0:print('progress',vis,'stack',len(stack),'depth',dep,flush=True)
assert cnt == Counter({'split':2944,0:147,1:24,2:1657,3:1106,4:11})
assert vis==5889 and maxd==33
assert minm==[78686177,1882725389,281396,1268683]
assert min(minm)>0
print('PASS',dict(cnt),'visited',vis,'depth',maxd,'min_margins',minm,'N',N,flush=True)
