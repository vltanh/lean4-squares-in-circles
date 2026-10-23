"""Replay a closed common-point cover without importing its generator."""
from fractions import Fraction as F
from pathlib import Path
import json
from sector_point135_bounds import U,R0,R,HALF,POINT,assess
if not __debug__:
 raise RuntimeError('Run without -O: certificate comparisons use assertions.')
ROOT=Path(__file__).resolve().parent

def check(path=None):
 data=json.loads((Path(path) if path else ROOT/'SECTOR_POINT135_COVER.json').read_text())
 assert set(data)=={'schema','disk_q','ring_radius','circle_radius','half_angle','point_radius','initial_box','tree','counts'}
 assert data['schema']=='ring-sector-common-point-v1'
 assert U==F(49013,10000) and R0==F(11,10) and R==F(5,4)
 assert HALF==F(27,40) and POINT==F(3,2)
 assert [F(data[k]) for k in ('disk_q','ring_radius','circle_radius','half_angle','point_radius')]==[U,R0,R,HALF,POINT]
 box=list(map(F,data['initial_box']))
 assert box==[F(0),F(7,4),F(0),F(7,4)]
 assert U<F(81,16) # own-frame centre coordinates are strictly below 7/4
 stats={'nodes':0,'leaves':{},'max_depth':0}
 def visit(node,box,depth):
  a,A,b,B=box
  assert 0<=a<=A and 0<=b<=B
  stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
  if set(node)=={'leaf'}:
   label=node['leaf'];assert type(label) is str
   assert label==assess(tuple(box))
   stats['leaves'][label]=stats['leaves'].get(label,0)+1
  else:
   assert set(node)=={'split','left','right'}
   axis=node['split'];assert type(axis) is int and axis in (0,1)
   k=2*axis;assert box[k]<box[k+1]
   m=(box[k]+box[k+1])/2
   left=box.copy();left[k+1]=m
   right=box.copy();right[k]=m
   visit(node['left'],left,depth+1);visit(node['right'],right,depth+1)
 visit(data['tree'],box,0)
 assert stats==data['counts']
 print('PASS: radius-3/2 common point in every admissible width-27/20 ring sector;',stats)
 return stats
if __name__=='__main__':
 import sys
 assert len(sys.argv)<=2
 check(sys.argv[1] if len(sys.argv)==2 else None)
