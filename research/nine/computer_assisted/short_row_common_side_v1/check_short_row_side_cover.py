"""Independent exact replay of the common-short-row-side cover.

No imports from its producer; roots, rounding, interval propagation and
all rational difference constraints are reconstructed here.
"""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json,hashlib
R=F(91,60);U=F(23,100);S=10**6
FIXED=((F(-91,60),F(-29,20)),(F(-11,20),F(-9,20)),(F(9,20),F(11,20)),(F(29,20),F(91,60)))
INITIAL=((F(-91,60),F(-29,60)),(F(-31,60),F(31,60)),(F(29,60),F(91,60)))
def root_bounds(q,up):
 # Independent bisection of integers; exact comparisons only.
 lo,hi=0,2*S
 while (F(hi,S))**2<q:hi*=2
 while hi-lo>1:
  m=(lo+hi)//2
  if F(m*m,S*S)<=q:lo=m
  else:hi=m
 z=F(lo,S)
 if z*z==q:return z
 return F(hi,S)if up else z

def forced_intervals(box):
 x=[list(v)for v in box]
 for iteration in range(3):
  for i in range(2):
   x[i+1][0]=max(x[i+1][0],x[i][0]+1)
   x[i][1]=min(x[i][1],x[i+1][1]-1)
 return tuple(map(tuple,x))
def edges_for(box,side):
 xs=FIXED+box;ans=[]
 for i,(a,b)in enumerate(xs):
  min_abs=F(0)if a<=0<=b else min(abs(a),abs(b))
  ycap=root_bounds(R*R-min_abs*min_abs,True)
  ans.extend([(0,i+1,ycap),(i+1,0,ycap)])
 for i,j in combinations(range(4),2):ans.extend([(i+1,j+1,U),(j+1,i+1,U)])
 for p,up in((4,False),(5,True),(6,side==1)):
  for i in range(4):
   d=max(abs(xs[p][0]-xs[i][1]),abs(xs[p][1]-xs[i][0]))
   margin=root_bounds(1-d*d,False)if d<1 else F(0)
   ans.append((p+1,i+1,-margin)if up else(i+1,p+1,-margin))
 for i,j in((4,5),(5,6)):
  cap=xs[j][1]-xs[i][0];ans.extend([(i+1,j+1,cap),(j+1,i+1,cap)])
 return ans

def verify(packet):
 assert packet['schema']=='common_short_row_side_difference_cover_v1'
 assert packet['radius']==str(R)and packet['variation']==str(U)
 assert tuple(tuple(map(F,v))for v in packet['root_x_intervals'])==FIXED+INITIAL
 assert [r['G_side']for r in packet['roots']]==[-1,1]
 stats=dict(leaves=0,empty=0,open=0,max_depth=0);least=None;checks=0
 for root in packet['roots']:
  stack=[(root,INITIAL,0)]
  while stack:
   node,raw,depth=stack.pop();box=forced_intervals(raw);stats['max_depth']=max(stats['max_depth'],depth)
   if 'split'in node:
    assert 'terminal'not in node;axis=node['split'];assert axis in(0,1,2)
    a,b=box[axis];at=F(node['at']);assert a<at<b and at==(a+b)/2
    assert len(node['children'])==2
    for side in(0,1):
     child=list(box);child[axis]=(a,at)if side==0 else(at,b)
     stack.append((node['children'][side],tuple(child),depth+1))
   elif node['terminal']=='empty_horizontal_chain':
    assert any(a>b for a,b in box);stats['empty']+=1;stats['leaves']+=1
   else:
    assert node['terminal']=='negative_cycle';es=edges_for(box,root['G_side']);ids=node['edges'];assert ids
    cycle=[es[i]for i in ids]
    for edge,next_edge in zip(cycle,cycle[1:]+cycle[:1]):assert edge[1]==next_edge[0]
    total=sum(edge[2]for edge in cycle);assert total<0 and total==F(node['sum'])
    least=-total if least is None else min(least,-total)
    checks+=len(cycle);stats['leaves']+=1
 assert stats==packet['counts']and str(least)==packet['least_reserve']
 return dict(status='PASS',**stats,exact_summed_edges=checks,least_reserve=str(least))
if __name__=='__main__':
 here=Path(__file__).resolve().parent;p=here/'SHORT_ROW_COMMON_SIDE_COVER.json'
 result=verify(json.loads(p.read_text()));result['sources']={q.name:hashlib.sha256(q.read_bytes()).hexdigest()for q in(p,Path(__file__))}
 (here/'SHORT_ROW_COMMON_SIDE_EXACT_REPLAY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
