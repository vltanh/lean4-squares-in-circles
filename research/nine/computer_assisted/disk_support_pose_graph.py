"""Exact disk-support contraction of a complete square-pose graph.

Every original pose is retained in a state or excluded by a necessary physical
inequality. Closed triangles, closed orientation arcs and degenerate polygons
are retained. This module produces a necessary relaxation, not global optimality.
See DISK_SUPPORT_CERTIFICATES.md for the exact support-function proof.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt,gcd
from collections import Counter
from pathlib import Path
import numpy as np
D=2**20

def fl(x):return x.numerator//x.denominator

def ce(x):return -fl(-x)

def cross(o,a,b):return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])

def hull(points):
 ps=sorted(set(points))
 if len(ps)<=1:return ps
 lo=[];up=[]
 for p in ps:
  while len(lo)>=2 and cross(lo[-2],lo[-1],p)<=0:lo.pop()
  lo.append(p)
 for p in ps[::-1]:
  while len(up)>=2 and cross(up[-2],up[-1],p)<=0:up.pop()
  up.append(p)
 return lo[:-1]+up[:-1]

def clip(poly,n,bound):
 if not poly:return []
 X,Y=n;old=poly;out=[];p=old[-1];dp=bound-X*p[0]-Y*p[1]
 for q in old:
  dq=bound-X*q[0]-Y*q[1]
  if (dp>=0)!=(dq>=0):
   f=F(dp,dp-dq);out.append((p[0]+f*(q[0]-p[0]),p[1]+f*(q[1]-p[1])))
  if dq>=0:out.append(q)
  p,dp=q,dq
 # Remove duplicates, but keep degeneracies, including isolated points/segments.
 out=list(dict.fromkeys(out))
 return out

def contract(g):
 m=g['m'];k=g['k'];D=g['denominator']
 if m not in (6,8) or k not in (12,24) or D != 2**20:
  raise ValueError('unsupported exact geometry parameters')
 normals=[(x,y) for x in range(-4,5) for y in range(-4,5) if gcd(abs(x),abs(y))==1]
 endpoints=[(F(k*k-i*i,k*k+i*i),F(2*k*i,k*k+i*i)) for i in range(k+1)]
 rhs=[]
 for o in range(k):
  Bs=[]
  for x,y in normals:
   h=[(abs(x*a+y*b)+abs(-x*b+y*a))/2 for a,b in endpoints[o:o+2]]
   h0=min(fl(t*D) for t in h)
   X,Y=x,y
   for _ in range(4):
    if X>=0 and Y>=0:break
    X,Y=-Y,X
   a,b=endpoints[o];A,B=endpoints[o+1]
   if a*Y-b*X>=0 and X*B-Y*A>=0:h0=min(h0,isqrt((x*x+y*y)*(D//2)**2))
   z=1105*(x*x+y*y)*(D//16)**2;r=isqrt(z)+(isqrt(z)**2<z)
   # Exact support of the admissible-center body of a contained square.
   def ceil_root(z):
    n=isqrt(z.numerator//z.denominator)
    return n+(F(n*n)<z)
   candidates=[]
   for a,b in endpoints[o:o+2]:
    AA,BB=abs(x*a+y*b),abs(-x*b+y*a)
    large,small=max(AA,BB),min(AA,BB)
    if 1105*small*small<=64*(x*x+y*y):
     candidates.append(ceil_root(F(1041,256)*large*large*D*D)-fl(large*D/2))
    else:
     candidates.append(r-fl(D*(AA+BB)/2))
   a,b=endpoints[o];A,B=endpoints[o+1]
   if a*Y-b*X>=0 and X*B-Y*A>=0:
    candidates.append(ceil_root(F(1041,256)*(x*x+y*y)*D*D)-isqrt((x*x+y*y)*(D//2)**2))
   Bs.append(min(r-h0,max(candidates)))
  rhs.append(Bs)
 minrhs=[min(row[j] for row in rhs) for j in range(len(normals))]
 lo3,hi3=F(1732050807,10**9),F(1732050808,10**9)
 if not lo3*lo3 < 3 < hi3*hi3:raise ValueError('square-root enclosure')
 polys=[];relevant=[]
 for c,t in g['triangles']:
  points=[]
  for X,Y in t:
   x=F(49*X*D,200*m);yl=F(49*Y*D,200*m)*lo3;yu=F(49*Y*D,200*m)*hi3
   points.extend(product((fl(x),ce(x)),(fl(min(yl,yu)),ce(max(yl,yu)))))
  p=hull(points);polys.append(p)
  relevant.append([j for j,(x,y) in enumerate(normals) if max(x*a+y*b for a,b in p)>minrhs[j]])
 polyids={};rounded=[];mapping=[];removed=[];sizes=Counter()
 for v,(cell,t,o) in enumerate(g['states']):
  poly=polys[t]
  for j in relevant[t]:
   poly=clip(poly,normals[j],rhs[o][j])
   if not poly:break
  if not poly:removed.append(v);mapping.append(-1);continue
  rects=tuple(sorted(set((fl(x),ce(x),fl(y),ce(y)) for x,y in poly)))
  if rects not in polyids:polyids[rects]=len(rounded);rounded.append(rects)
  mapping.append(polyids[rects]);sizes[len(rects)]+=1
 metadata=dict(normals=normals,rhs=rhs,mapping=mapping,polygons=rounded,removed=removed)
 maxverts=max(map(len,rounded));verts=np.array([list(p)+[p[-1]]*(maxverts-len(p)) for p in rounded],dtype=np.int64)
 if int(np.max(np.abs(verts))) > 3*D:raise ValueError('coordinate overflow bound')
 if any(abs(c)>D for axis in g['axes'] for c in axis):raise ValueError('axis overflow bound')
 lows=[];highs=[]
 for al,au,bl,bu in g['axes']:
  ls=[];hs=[]
  for a,b in product((al,au),(bl,bu)):
   for A,B in ((a,b),(-b,a)):
    xl=A*verts[:,:,0 if A>=0 else 1];xh=A*verts[:,:,1 if A>=0 else 0]
    yl=B*verts[:,:,2 if B>=0 else 3];yh=B*verts[:,:,3 if B>=0 else 2]
    ls.append(np.min(xl+yl,axis=1));hs.append(np.max(xh+yh,axis=1))
  lows.append(ls);highs.append(hs)
 lo=np.array(lows);hi=np.array(highs);del verts
 st=np.array(g['states']);cell,pos,ori=st.T;pp=np.array(mapping);ok=pp>=0;safe=np.maximum(pp,0)
 bypoly=[[] for p in rounded]
 for v,p in enumerate(mapping):
  if p>=0:bypoly[p].append(v)
 adj=[0]*len(mapping);threshold=np.array(g['lower'])
 for p,vs in enumerate(bypoly):
  proj=np.maximum(np.max(hi-lo[:,:,p,None],axis=1),np.max(hi[:,:,p,None]-lo,axis=1))
  for v in vs:
   a=ok&(cell!=cell[v])&(2*np.maximum(proj[ori[v],safe],proj[ori,safe])>=threshold[ori[v],ori])
   adj[v]=int.from_bytes(np.packbits(a,bitorder='little').tobytes(),'little') & g['adjacency'][v]
 groups=[]
 valid=sum(1<<i for i,p in enumerate(mapping) if p>=0)
 for grp in g['groups']:groups.append(grp&valid)
 result={**g,'adjacency':adj,'groups':groups,'contraction':metadata}
 return result

