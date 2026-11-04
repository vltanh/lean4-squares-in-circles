"""Replay the exact cover establishing a 63/100 ring arc width."""
from fractions import Fraction as F
from pathlib import Path
import json
from exact_arcs import rectangle_arc_lower
if not __debug__:
 raise RuntimeError('Run without -O: certificate comparisons use assertions.')
ROOT=Path(__file__).resolve().parent
U=F(49013,10000);R0=F(41,40);R=F(5,4);TARGET=F(63,100)
def check(path=None):
 data=json.loads((Path(path) if path else ROOT/'RING_WIDTH_COVER.json').read_text())
 assert set(data)=={'schema','disk_q','core_radius','circle_radius','target','initial_box','tree','counts'}
 assert data['schema']=='single-ring-arc-width-v1'
 assert F(data['disk_q'])==U and F(data['core_radius'])==R0
 assert F(data['circle_radius'])==R and F(data['target'])==TARGET
 box=[tuple(map(F,entry)) for entry in data['initial_box']]
 assert box==[(F(0),F(7,4))]*2
 assert U<F(81,16)  # own-frame centre coordinates are each less than 7/4
 stats={'nodes':0,'arc_leaves':0,'discard_leaves':0,'max_depth':0}
 def visit(node,box,depth):
  stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
  (a,A),(b,B)=box
  assert 0<=a<=A and 0<=b<=B
  if set(node)=={'arc'}:
   assert node['arc'] is True
   rect=[(hi-F(1,2),lo+F(1,2)) for lo,hi in box]
   assert rectangle_arc_lower(rect,R)>=TARGET
   stats['arc_leaves']+=1
  elif set(node)=={'discard'}:
   reason=node['discard']
   if reason=='below-diagonal':assert A<b
   elif reason=='inside-core':assert A*A+B*B<R0*R0
   elif reason=='outside-disk':assert (a+F(1,2))**2+(b+F(1,2))**2>U
   else:raise AssertionError(('unknown discard',reason))
   stats['discard_leaves']+=1
  else:
   assert set(node)=={'split','left','right'}
   axis=node['split'];assert type(axis) is int and axis in (0,1)
   lo,hi=box[axis];assert lo<hi
   mid=(lo+hi)/2
   left=box.copy();left[axis]=(lo,mid)
   right=box.copy();right[axis]=(mid,hi)
   visit(node['left'],left,depth+1);visit(node['right'],right,depth+1)
 visit(data['tree'],box,0)
 assert stats==data['counts']
 print('PASS: ring arc width >= 63/100;',stats)
 return stats
if __name__=='__main__':
 import sys
 assert len(sys.argv)<=2
 check(sys.argv[1] if len(sys.argv)==2 else None)
