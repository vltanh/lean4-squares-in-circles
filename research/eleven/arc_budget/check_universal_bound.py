"""Exact replay: no eleven unit squares with disjoint interiors fit q <= 9/2."""
from fractions import Fraction as F
from pathlib import Path
import json
from exact_arcs import rectangle_arc_lower, PI_HI

if not __debug__:
    raise RuntimeError('Run without -O: certificate comparisons use assertions.')

Q=F(9,2)
RADII=(F(3,10),F(9,10),F(6,5),F(13,10),F(7,5))
WEIGHTS=(F(41,200),F(63,1000),F(17,50),F(7,25),F(14,125))
TARGET=F(23,40)

def check():
    data=json.loads(Path(__file__).with_name('UNIVERSAL_BOUND_COVER.json').read_text())
    assert data['schema']=='universal-weighted-circle-arcs-v1'
    assert F(data['disk_q'])==Q and F(data['target'])==TARGET
    assert tuple(map(F,data['radii']))==RADII
    assert tuple(map(F,data['weights']))==WEIGHTS and sum(WEIGHTS)==1
    initial=[tuple(map(F,p)) for p in data['initial_box']]
    assert initial==[(F(0),F(7,4)),(F(0),F(7,4))]
    assert Q<F(81,16)
    stats={'nodes':0,'arc_leaves':0,'discard_leaves':0,'max_depth':0}
    def visit(node,box,depth):
        stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
        (a,A),(b,B)=box
        assert 0<=a<=A and 0<=b<=B
        if set(node)=={'arc'}:
            assert node['arc'] is True
            rect=[(A-F(1,2),a+F(1,2)),(B-F(1,2),b+F(1,2))]
            assert sum(w*rectangle_arc_lower(rect,r) for w,r in zip(WEIGHTS,RADII))>=TARGET
            stats['arc_leaves']+=1
        elif set(node)=={'discard'}:
            reason=node['discard']
            if reason=='below-diagonal':assert A<b
            elif reason=='outside-disk':assert (a+F(1,2))**2+(b+F(1,2))**2>Q
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
    visit(data['tree'],initial,0)
    assert stats==data['counts']
    assert 11*TARGET==F(253,40)>F(44,7)>2*PI_HI
    print('PASS universal q > 9/2:',stats)
    return stats

if __name__=='__main__':check()
