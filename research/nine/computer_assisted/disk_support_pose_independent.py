"""Separate exact reconstruction of the contracted square-pose graph.

Uses all feasible intersections of supporting lines, not polygon clipping;
uses midpoint/radius projections, not endpoint sign selection. Does not import
the producer. Python integers are unbounded; NumPy int64 projections are bounded.
"""
from fractions import Fraction as F
from math import gcd,isqrt
from itertools import product,combinations

import numpy as np
D=2**20

def need(c,m):
 if not c:raise ValueError(m)

def primitive_line(a,b,c):
 d=gcd(gcd(abs(a),abs(b)),abs(c));return a//d,b//d,c//d

def initial_lines(points):
 result=set()
 for p,q in combinations(points,2):
  if p==q:continue
  a,b=q[1]-p[1],p[0]-q[0];c=a*p[0]+b*p[1]
  dots=[a*x+b*y-c for x,y in points]
  if max(dots)<=0:result.add(primitive_line(a,b,c))
  if min(dots)>=0:result.add(primitive_line(-a,-b,-c))
 return sorted(result)

def intersections(lines):
 pts=set()
 for (a,b,c),(u,v,w) in combinations(lines,2):
  d=a*v-u*b
  if not d:continue
  x=c*v-w*b;y=a*w-u*c
  if d<0:d,x,y=-d,-x,-y
  if all(A*x+B*y<=C*d for A,B,C in lines):
   pts.add((x//d,-((-x)//d),y//d,-((-y)//d)))
 return tuple(sorted(pts))

def contract_independent(g):
 m=g['m'];k=g['k'];d=g['denominator'];need(d==D,'scale')
 need(m in (6,8) and k in (12,24),'unsupported exact geometry parameters')
 # Enumerate primitive normal vectors by positive quadrant and quarter turns.
 normals=set()
 for x in range(5):
  for y in range(5):
   if gcd(x,y)!=1:continue
   a,b=x,y
   for _ in range(4):normals.add((a,b));a,b=-b,a
 normals=sorted(normals);need(len(normals)==48,'normal count')
 ends=[(F(k*k-i*i,k*k+i*i),F(2*k*i,k*k+i*i)) for i in range(k+1)]
 rhs=[]
 for o in range(k):
  row=[]
  for nx,ny in normals:
   options=[]
   for a,b in ends[o:o+2]:
    t=d*(abs(nx*a+ny*b)+abs(ny*a-nx*b))/2
    options.append(t.numerator//t.denominator)
   x,y=nx,ny
   while x<0 or y<0:x,y=-y,x
   # Ratio comparisons without trigonometric functions.
   a,b=ends[o];A,B=ends[o+1]
   if b*x<=a*y and B*x>=A*y:
    options.append(isqrt((nx*nx+ny*ny)*d*d//4))
   h=min(options)
   N=F(1105,256)*(nx*nx+ny*ny)*d*d
   r=isqrt(N.numerator//N.denominator)
   if F(r*r)<N:r+=1
   need(F(r*r)>=N and (r==0 or F((r-1)**2)<N),'outward radius')
   # Independently derive the upper support at the two arc ends and
   # at an interior alignment. The formulas use shifted disk coordinates.
   def root_ceiling(z):
    h=isqrt(z.numerator//z.denominator)
    return h+int(F(h*h)<z)
   candidates=[]
   for ux,uy in ends[o:o+2]:
    A,B=abs(nx*ux+ny*uy),abs(ny*ux-nx*uy)
    A,B=max(A,B),min(A,B)
    if 4*F(1105,256)*B*B<=nx*nx+ny*ny:
     first=root_ceiling(F(1041,256)*(A*d)**2)
     second=A*d/2
     candidates.append(first-second.numerator//second.denominator)
    else:
     offset=(A+B)*d/2
     candidates.append(r-offset.numerator//offset.denominator)
   a,b=ends[o];A,B=ends[o+1]
   if b*x<=a*y and B*x>=A*y:
    candidates.append(root_ceiling(F(1041,256)*(nx*nx+ny*ny)*d*d)
                      -isqrt((nx*nx+ny*ny)*d*d//4))
   row.append(min(r-h,max(candidates)))
  rhs.append(row)
 lo=F(1732050807,10**9);hi=F(1732050808,10**9)
 need(lo*lo<3<hi*hi,'sqrt3')
 cells=[];constraints=[];relevant=[]
 for cell,tri in g['triangles']:
  pts=set()
  for x,y in tri:
   X=F(49*x*d,200*m);YY=[F(49*y*d,200*m)*lo,F(49*y*d,200*m)*hi]
   L=min(YY);U=max(YY)
   pts.update(product((X.numerator//X.denominator,-((-X.numerator)//X.denominator)),
                      (L.numerator//L.denominator,-((-U.numerator)//U.denominator))))
  pts=sorted(pts);cells.append(pts);constraints.append(initial_lines(pts))
  relevant.append([j for j,(a,b) in enumerate(normals) if max(a*x+b*y for x,y in pts)>min(row[j] for row in rhs)])
 polyid={};polys=[];mapping=[];removed=[]
 cache={}
 for v,(c,t,o) in enumerate(g['states']):
  lines=constraints[t]+[(*normals[j],rhs[o][j]) for j in relevant[t]]
  key=tuple(lines)
  if key not in cache:cache[key]=intersections(lines)
  p=cache[key]
  if not p:mapping.append(-1);removed.append(v);continue
  if p not in polyid:polyid[p]=len(polys);polys.append(p)
  mapping.append(polyid[p])
 # Independent midpoint/radius form of projections on the outward vertex rectangles.
 maxsize=max(map(len,polys));arr=np.array([list(p)+[p[-1]]*(maxsize-len(p)) for p in polys],dtype=np.int64)
 need(int(np.max(np.abs(arr)))<=3*d,'position bound')
 xm=arr[:,:,0]+arr[:,:,1];xr=arr[:,:,1]-arr[:,:,0]
 ym=arr[:,:,2]+arr[:,:,3];yr=arr[:,:,3]-arr[:,:,2]
 L=[];U=[]
 for al,au,bl,bu in g['axes']:
  ls=[];us=[]
  for a,b in product((al,au),(bl,bu)):
   for A,B in ((a,b),(-b,a)):
    mid=A*xm+B*ym;rad=abs(A)*xr+abs(B)*yr
    need(not np.any((mid-rad)%2) and not np.any((mid+rad)%2),'projection parity')
    ls.append(np.min((mid-rad)//2,axis=1));us.append(np.max((mid+rad)//2,axis=1))
  L.append(ls);U.append(us)
 L=np.array(L);U=np.array(U);del arr
 state=np.array(g['states']);angles=state[:,2];pindex=np.array(mapping);live=pindex>=0;safe=np.maximum(pindex,0)
 threshold=np.array(g['lower']);adj=[0]*len(mapping);groups=[0]*19
 bypoly=[[] for p in polys]
 for v,(c,t,o) in enumerate(g['states']):
  if mapping[v]>=0:bypoly[mapping[v]].append(v);groups[c]|=1<<v
 for pi in range(len(polys)-1,-1,-1):
  pos=np.max(U-L[:,:,pi,None],axis=1);neg=np.max(U[:,:,pi,None]-L,axis=1)
  for v in bypoly[pi]:
   o=angles[v];th=threshold[o,angles]
   cond=live&((2*pos[o,safe]>=th)|(2*neg[o,safe]>=th)|(2*pos[angles,safe]>=th)|(2*neg[angles,safe]>=th))
   adj[v]=g['adjacency'][v]&int.from_bytes(np.packbits(cond,bitorder='little').tobytes(),'little')
 result={**g,'adjacency':adj,'groups':groups,'contraction':dict(normals=normals,rhs=rhs,mapping=mapping,polygons=polys,removed=removed)}
 return result

