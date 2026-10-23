"""Separate arithmetic replay of the universal eleven-square lower bound."""
import json
from pathlib import Path
from fractions import Fraction as F
from independent_arcs import rectangle_angle_lower,PI

if not __debug__:
    raise RuntimeError('Run without -O; proof checks use assertions.')

def replay(path):
    data=json.loads(Path(path).read_text())
    assert data['schema']=='universal-weighted-circle-arcs-v1'
    q=F(9,2);target=F(23,40)
    radii=[F(3,10),F(9,10),F(6,5),F(13,10),F(7,5)]
    weights=[F(41,200),F(63,1000),F(17,50),F(7,25),F(14,125)]
    assert list(map(F,data['radii']))==radii and list(map(F,data['weights']))==weights
    assert sum(weights)==1 and F(data['disk_q'])==q and F(data['target'])==target
    assert [[F(z) for z in row] for row in data['initial_box']]==[[0,F(7,4)],[0,F(7,4)]]
    assert q<F(81,16)
    stats={'nodes':0,'arc_leaves':0,'discard_leaves':0,'max_depth':0}
    def visit(node,box,depth):
        stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
        a,A,b,B=box
        if set(node)=={'split','left','right'}:
            axis=node['split'];assert type(axis) is int and axis in (0,1)
            k=2*axis;mid=(box[k]+box[k+1])/2
            assert box[k]<mid<box[k+1]
            left=list(box);left[k+1]=mid
            right=list(box);right[k]=mid
            visit(node['left'],left,depth+1);visit(node['right'],right,depth+1)
        elif node=={'arc':True}:
            lower=sum(w*rectangle_angle_lower(A-F(1,2),a+F(1,2),B-F(1,2),b+F(1,2),r)
                      for w,r in zip(weights,radii))
            assert lower>=target,box
            stats['arc_leaves']+=1
        else:
            assert set(node)=={'discard'}
            tests={'below-diagonal':A<b,'outside-disk':(a+F(1,2))**2+(b+F(1,2))**2>q}
            assert node['discard'] in tests and tests[node['discard']]
            stats['discard_leaves']+=1
    visit(data['tree'],[F(0),F(7,4),F(0),F(7,4)],0)
    assert stats==data['counts']=={'nodes':2385,'arc_leaves':980,'discard_leaves':213,'max_depth':21}
    assert 11*target==F(253,40)>F(44,7)>2*PI[1]
    print('PASS independent universal q > 9/2',stats,flush=True)

if __name__=='__main__':
    import sys
    replay(sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('UNIVERSAL_BOUND_COVER.json'))
