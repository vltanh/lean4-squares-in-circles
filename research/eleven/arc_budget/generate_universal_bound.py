"""Exact universal eleven-square lower bound q > 9/2, via circle measures."""
from exact_arcs import F, rectangle_arc_lower
from pathlib import Path
import json

Q=F(9,2)
RADII=(F(3,10),F(9,10),F(6,5),F(13,10),F(7,5))
WEIGHTS=(F(41,200),F(63,1000),F(17,50),F(7,25),F(14,125))
TARGET=F(23,40)
assert sum(WEIGHTS)==1

def weighted(box):
    rect=[(hi-F(1,2),lo+F(1,2)) for lo,hi in box]
    return sum(w*rectangle_arc_lower(rect,r) for w,r in zip(WEIGHTS,RADII))

def run():
    stats={'nodes':0,'arc_leaves':0,'discard_leaves':0,'max_depth':0}
    def visit(box,depth):
        stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
        (a,A),(b,B)=box
        reason='below-diagonal' if A<b else ('outside-disk' if (a+F(1,2))**2+(b+F(1,2))**2>Q else None)
        if reason:
            stats['discard_leaves']+=1;return {'discard':reason}
        if weighted(box)>=TARGET:
            stats['arc_leaves']+=1;return {'arc':True}
        assert depth<38, ('UNRESOLVED',box,depth)
        axis=0 if A-a>=B-b else 1
        lo,hi=box[axis];mid=(lo+hi)/2
        left=box.copy();left[axis]=(lo,mid)
        right=box.copy();right[axis]=(mid,hi)
        return {'split':axis,'left':visit(left,depth+1),'right':visit(right,depth+1)}
    box=[(F(0),F(7,4)),(F(0),F(7,4))]
    tree=visit(box,0)
    data={'schema':'universal-weighted-circle-arcs-v1','disk_q':str(Q),'target':str(TARGET),
          'radii':[str(x) for x in RADII],'weights':[str(x) for x in WEIGHTS],
          'initial_box':[[str(a),str(b)] for a,b in box],'counts':stats,'tree':tree}
    dest=Path(__file__).with_name('UNIVERSAL_BOUND_COVER.json')
    dest.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
    print('CLOSED universal q <= 9/2',stats,'->',dest)

if __name__=='__main__':run()
