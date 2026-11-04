"""Exact rational generation of a uniform ring arc width certificate."""
from fractions import Fraction as F
from pathlib import Path
import json
from exact_arcs import rectangle_arc_lower
U=F(49013,10000);R0=F(41,40);R=F(5,4);TARGET=F(63,100)
def width_lower(box):
 return rectangle_arc_lower([(hi-F(1,2),lo+F(1,2)) for lo,hi in box],R)
def run():
 stats={'nodes':0,'arc_leaves':0,'discard_leaves':0,'max_depth':0}
 def visit(box,depth):
  stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
  (a,A),(b,B)=box
  reason=None
  if A<b:reason='below-diagonal'
  elif A*A+B*B<R0*R0:reason='inside-core'
  elif (a+F(1,2))**2+(b+F(1,2))**2>U:reason='outside-disk'
  if reason:
   stats['discard_leaves']+=1;return {'discard':reason}
  if width_lower(box)>=TARGET:
   stats['arc_leaves']+=1;return {'arc':True}
  assert depth<40,('UNRESOLVED',box,depth)
  axis=0 if box[0][1]-box[0][0]>=box[1][1]-box[1][0] else 1
  lo,hi=box[axis];mid=(lo+hi)/2
  left=box.copy();left[axis]=(lo,mid)
  right=box.copy();right[axis]=(mid,hi)
  return {'split':axis,'left':visit(left,depth+1),'right':visit(right,depth+1)}
 box=[(F(0),F(7,4))]*2
 data={'schema':'single-ring-arc-width-v1','disk_q':str(U),'core_radius':str(R0),'circle_radius':str(R),'target':str(TARGET),'initial_box':[[str(lo),str(hi)] for lo,hi in box]}
 data['tree']=visit(box,0);data['counts']=stats
 p=Path(__file__).with_name('RING_WIDTH_COVER.json');p.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
 print('CLOSED',stats,flush=True)
if __name__=='__main__':run()
