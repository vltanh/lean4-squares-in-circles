"""Generate the exact two-dimensional narrow-sector common-point cover."""
from native_sector_point_bounds import *
from pathlib import Path
import json

def run():
 stats={'nodes':0,'leaves':{},'max_depth':0}
 def visit(box,depth):
  stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
  label=assess(tuple(box))
  if label:
   stats['leaves'][label]=stats['leaves'].get(label,0)+1
   return {'leaf':label}
  assert depth<40,('UNRESOLVED',box,depth)
  axis=0 if box[1]-box[0]>=box[3]-box[2] else 1
  k=2*axis;m=(box[k]+box[k+1])/2
  left=box.copy();left[k+1]=m
  right=box.copy();right[k]=m
  return {'split':axis,'left':visit(left,depth+1),'right':visit(right,depth+1)}
 box=[F(0),F(7,4),F(0),F(7,4)]
 data={'schema':'ring-sector-common-point-v1','disk_q':str(U),'ring_radius':str(R0),'circle_radius':str(R),'half_angle':str(HALF),'point_radius':str(POINT),'initial_box':list(map(str,box))}
 data['tree']=visit(box,0);data['counts']=stats
 path=Path(__file__).with_name('NATIVE_SECTOR_POINT_COVER.json');path.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
 print('CLOSED',stats,flush=True)
if __name__=='__main__':run()
