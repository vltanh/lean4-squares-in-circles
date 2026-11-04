import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
from fractions import Fraction as F
from itertools import combinations
import random,json,hashlib
from pathlib import Path
import coupled_four_center_energy as G
import check_coupled_four_center_energy as C
rng=random.Random(183516)
cases=[]
# Dimensions zero, one, two, and three, plus an empty interval polytope.
cases.append(tuple((F(0),F(0))for _ in range(6)))
cases.append(tuple((F(0),F(1))if i in(2,4,5)else(F(0),F(0))for i in range(6)))
cases.append(tuple((F(a),F(b))for a,b in((0,1),(0,1),(0,0),(-1,1),(-1,0),(-1,0))))
cases.append(tuple((F(0),F(1))for _ in range(6)))
cases.append(tuple((F(-1),F(1))for _ in range(6)))
cases.append(tuple((F(a),F(b))for a,b in((0,0),(1,1),(2,2),(0,0),(0,0),(0,0))))
for _ in range(25):
 points=[tuple(F(rng.randrange(-10,11),8)for j in range(3))for k in range(12)]
 intervals=[]
 for n in G.NORMALS:
  vals=[G.dot(n,v)for v in points];intervals.append((min(vals),max(vals)))
 cases.append(tuple(intervals))
counts={'cases':len(cases),'vertices':0,'planes':0,'checks':0,'rows':0}
for intervals in cases:
 planes,verts=G.upper_planes(intervals)
 assert verts==C.vertices_from_intervals(intervals)
 for p in planes:
  for v in verts:assert G.dot(p[:3],v)+p[3]>=C.quadratic(v);counts['checks']+=1
 counts['vertices']+=len(verts);counts['planes']+=len(planes)
 # Every deterministic pair of vertex assignments defines four 2D centers.
 # The algebraic row conversion is checked without requiring nonoverlap.
 if not verts:continue
 dd={pair:(intervals[i],intervals[i])for i,pair in enumerate(G.PAIRS)}
 rs,ab,guards=G.lifted_rows(dd,18,original_count=4)
 assert (rs,ab)==C.reconstructed_rows(guards,lifted=True)
 dr,dg=G.rows(dd,original_count=4)
 assert dr==C.reconstructed_rows(dg)[0]
 for x,y in zip(verts,reversed(verts)):
  xx=(F(0),)+x;yy=(F(0),)+y
  point=[F(0)]*19
  for i in range(4):point[2*i]=xx[i];point[2*i+1]=yy[i]
  point[18]=C.quadratic(x)
  total=C.quadratic(x)+C.quadratic(y)
  for co,rhs,name in rs:
   lhs=sum(c*point[k]for k,c in co)
   # y-axis lower-bound rows use E4>=8; check the exact translated identity.
   if '_1_' in name and name.startswith('coupled_four_lifted_'):
    pass
   # Identify through the aux coefficient, independent of naming.
   auxcoef=dict(co).get(18,F(0))
   if auxcoef==-1 and name.startswith('coupled_four_lifted_'):assert lhs<=rhs+8-total
   else:assert lhs<=rhs
   counts['rows']+=1
counts['status']='PASS';counts['sources']={p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in(Path(G.__file__),Path(C.__file__),Path(__file__))}
Path(__file__).with_name('FOUR_COUPLED_FIXTURE_REPLAY.json').write_text(json.dumps(counts,indent=2)+'\n')
print(json.dumps(counts,indent=2))
