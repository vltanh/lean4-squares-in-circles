#!/usr/bin/env python3
"""Exact physical replay of one seven-square control; no optimizer imported."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
source=HERE/'selected_seven_exact_control.json'
raw=source.read_bytes();obj=json.loads(raw)
assert obj['schema']=='seven_original_01011_control_v1'
assert obj['mask']=='010/11'
assert [s['label']for s in obj['squares']]==['A','B','C','D','L','P','R']
Q=F(obj['Q']);q=F(obj['contained_radius_squared'])
assert Q==F(1105,256) and q<Q

def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def support(s,n):return (abs(dot(s['u'],n))+abs(dot(s['v'],n)))/2

squares=[];corners=[]
for entry in obj['squares']:
 t=F(entry['half_angle_parameter'])
 a=(1-t*t)/(1+t*t);b=2*t/(1+t*t)
 u=(a,b);v=(-b,a);c=(F(entry['x']),F(entry['y']))
 assert dot(u,u)==dot(v,v)==1 and dot(u,v)==0
 s={'label':entry['label'],'u':u,'v':v,'c':c,'h':(abs(a)+abs(b))/2}
 squares.append(s)
 for e in(-1,1):
  for f in(-1,1):
   p=tuple(c[k]+(e*u[k]+f*v[k])/2 for k in(0,1))
   corners.append(dot(p,p))
assert len(corners)==28 and max(corners)<q

pairs=[]
for i,s in enumerate(squares):
 for j in range(i+1,7):
  t=squares[j];d=tuple(t['c'][k]-s['c'][k]for k in(0,1))
  margins=[abs(dot(d,n))-support(s,n)-support(t,n)
           for n in(s['u'],s['v'],t['u'],t['v'])]
  m=max(margins);assert m>0,(i,j,m)
  pairs.append({'labels':[s['label'],t['label']],'separating_axis':margins.index(m),'margin':str(m)})
assert len(pairs)==21

edges=[]
for (i,j),bit in zip([(0,1),(1,2),(2,3),(4,5),(5,6)],'01011'):
 s,t=squares[i],squares[j]
 dx=t['c'][0]-s['c'][0];dy=t['c'][1]-s['c'][1]
 cone=dx-abs(dy);assert cone>0
 actual=dx-s['h']-t['h']
 if bit=='0':assert actual>0
 else:assert actual<0
 edges.append({'labels':[s['label'],t['label']],'bit':bit,'cone_margin':str(cone),'signed_actual_margin':str(actual)})

report={'result':'PASS','scope':'Seven original squares, 28 corners, 21 pairs, and all five exact 010/11 marked comparisons. The two remaining originals are absent.','certificate_sha256':hashlib.sha256(raw).hexdigest(),'contained_radius_squared':str(q),'Q_minus_q':str(Q-q),'max_corner_squared':str(max(corners)),'corner_margin':str(q-max(corners)),'min_pair_margin':str(min(F(x['margin'])for x in pairs)),'edges':edges,'pairs':pairs,'formal_kernel_check':False,'numeric_optimizer_used_by_checker':False}
(HERE/'selected_seven_exact_control_replay.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'result':'PASS','q':str(q),'Q_minus_q':str(Q-q),'min_pair_margin':float(F(report['min_pair_margin'])),'min_cone_margin':float(min(F(e['cone_margin'])for e in edges)),'certificate_sha256':report['certificate_sha256']},indent=2))
