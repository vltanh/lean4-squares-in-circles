"""Exact interval/difference-constraint discovery of common vertical side.

Pure rational proof arithmetic. Seven unit-separated centers in radius
91/60; four horizontally ordered centers of total height variation <=23/100;
three other centers form actual horizontal gaps >=1 and center-cone edges.
"""
from fractions import Fraction as F
from math import isqrt
from itertools import combinations,product
from pathlib import Path
import json,time,hashlib
R=F(91,60);U=F(23,100);DEN=10**6
ROOT=((F(-91,60),F(-29,20)),(F(-11,20),F(-9,20)),(F(9,20),F(11,20)),(F(29,20),F(91,60)),(-R,R-2),(1-R,R-1),(2-R,R))
def lower_sqrt(x):
 assert x>=0
 n=isqrt(x.numerator*DEN*DEN//x.denominator)
 return F(n,DEN)
def upper_sqrt(x):
 q=lower_sqrt(x)
 return q if q*q==x else q+F(1,DEN)
def constraints(box,gsign):
 xs=list(ROOT[:4])+list(box);edges=[]
 # y_i is node i+1, node0 represents0.
 def edge(i,j,b,name):edges.append((i,j,b,name)) # y_j-y_i<=b
 for i,(lo,hi)in enumerate(xs):
  m=F(0)if lo<=0<=hi else min(abs(lo),abs(hi))
  top=upper_sqrt(R*R-m*m)
  edge(0,i+1,top,f'disk_y_upper_{i}');edge(i+1,0,top,f'disk_y_lower_{i}')
 for i,j in combinations(range(4),2):
  edge(i+1,j+1,U,f'row_span_{i}_{j}');edge(j+1,i+1,U,f'row_span_{j}_{i}')
 for p,sgn in((4,-1),(5,1),(6,gsign)):
  for i in range(4):
   dx=max(abs(xs[p][0]-xs[i][1]),abs(xs[p][1]-xs[i][0]))
   gap=lower_sqrt(1-dx*dx)if dx<1 else F(0)
   if sgn>0:edge(p+1,i+1,-gap,f'upper_pair_gap_{i}_{p}')
   else:edge(i+1,p+1,-gap,f'lower_pair_gap_{i}_{p}')
 for i,j in((4,5),(5,6)):
  dx=xs[j][1]-xs[i][0]
  edge(i+1,j+1,dx,f'cone_up_{i}_{j}');edge(j+1,i+1,dx,f'cone_down_{i}_{j}')
 return edges

def negative_cycle(edges):
 # Exact Floyd-Warshall with compositional path certificates.
 n=8;d=[[None]*n for _ in range(n)];path=[[None]*n for _ in range(n)]
 for i in range(n):d[i][i]=F(0);path[i][i]=[]
 for k,(i,j,b,_)in enumerate(edges):
  if d[i][j]is None or b<d[i][j]:d[i][j]=b;path[i][j]=[k]
 for k in range(n):
  for i in range(n):
   if d[i][k]is None:continue
   for j in range(n):
    if d[k][j]is None:continue
    v=d[i][k]+d[k][j]
    if d[i][j]is None or v<d[i][j]:d[i][j]=v;path[i][j]=path[i][k]+path[k][j]
    if i==j and d[i][j]<0:
     return path[i][j],d[i][j]
 return None

def tighten(box):
 xs=[list(z)for z in box]
 for _ in range(3):
  for i,j in((0,1),(1,2)):
   xs[j][0]=max(xs[j][0],xs[i][0]+1)
   xs[i][1]=min(xs[i][1],xs[j][1]-1)
 return tuple(map(tuple,xs))
def discovery(max_depth=18):
 start=time.monotonic();roots=[];counts={'leaves':0,'empty':0,'open':0,'max_depth':0};smallest=None
 for gsign in(-1,1):
  root={'G_side':gsign};stack=[(root,ROOT[4:],0)]
  while stack:
   node,raw,depth=stack.pop();box=tighten(raw);counts['max_depth']=max(counts['max_depth'],depth)
   if any(a>b for a,b in box):node['terminal']='empty_horizontal_chain';counts['empty']+=1;counts['leaves']+=1;continue
   es=constraints(box,gsign);cert=negative_cycle(es)
   if cert:
    ids,val=cert;node['terminal']='negative_cycle';node['edges']=ids;node['sum']=str(val);counts['leaves']+=1
    if smallest is None or -val<smallest:smallest=-val
   elif depth==max_depth:
    node['terminal']='OPEN';node['box']=[[str(a),str(b)]for a,b in box];counts['open']+=1;counts['leaves']+=1
   else:
    axis=max(range(3),key=lambda k:box[k][1]-box[k][0]);a,b=box[axis];mid=(a+b)/2
    node['split']=axis;node['at']=str(mid);node['children']=[{},{}]
    for side in(1,0):
     child=list(box);child[axis]=(a,mid)if side==0 else(mid,b)
     stack.append((node['children'][side],tuple(child),depth+1))
  roots.append(root)
  print('G',gsign,counts,'seconds',round(time.monotonic()-start,3),flush=True)
 return dict(schema='common_short_row_side_difference_cover_v1',radius=str(R),variation=str(U),
             root_x_intervals=[[str(a),str(b)]for a,b in ROOT],roots=roots,counts=counts,
             least_reserve=str(smallest),seconds=time.monotonic()-start)
if __name__=='__main__':
 packet=discovery();p=Path(__file__).with_name('SHORT_ROW_COMMON_SIDE_COVER.json');p.write_text(json.dumps(packet,indent=2)+'\n');print(packet['counts'],packet['least_reserve'])
