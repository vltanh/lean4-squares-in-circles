"""Replay every closed-cover leaf; does not import the cover generator."""
from fractions import Fraction as F
import json
from pathlib import Path
from exact_arcs import weighted_lower, PI_HI

if not __debug__:
    raise RuntimeError("Run without -O: certificate comparisons use assertions.")

ROOT=Path(__file__).resolve().parent
U=F(49013,10000)
R0=F(41,40)

def check(kind):
    data=json.loads((ROOT/(kind.upper()+'_ARC_COVER.json')).read_text())
    assert data['schema']=='weighted-circle-arcs-v1'
    assert data['kind']==kind
    assert F(data['disk_q'])==U and F(data['core_radius'])==R0
    assert list(map(F,data['radii']))==[F(3,10),F(3,5),F(5,4)]
    assert list(map(F,data['weights']))==[F(3,100),F(17,40),F(109,200)]
    target=F(43,50) if kind=='core' else F(17,50)
    assert F(data['target'])==target
    extent=R0 if kind=='core' else F(7,4)
    box=[tuple(map(F,entry)) for entry in data['initial_box']]
    assert box==[(F(0),extent),(F(0),extent)]
    assert U<F(81,16) # ring own-frame coordinates are strictly below 7/4
    stats={'nodes':0,'arc_leaves':0,'discard_leaves':0,'max_depth':0}
    def visit(node,box,depth):
        stats['nodes']+=1
        stats['max_depth']=max(stats['max_depth'],depth)
        (a,A),(b,B)=box
        assert 0<=a<=A and 0<=b<=B
        if set(node)=={'arc'}:
            assert node['arc'] is True
            assert weighted_lower(box)>=target
            stats['arc_leaves']+=1
        elif set(node)=={'discard'}:
            reason=node['discard']
            if reason=='below-diagonal':assert A<b
            elif reason=='outside-core':assert kind=='core' and a*a+b*b>R0*R0
            elif reason=='inside-core':assert kind=='ring' and A*A+B*B<R0*R0
            elif reason=='outside-disk':assert kind=='ring' and (a+F(1,2))**2+(b+F(1,2))**2>U
            else:raise AssertionError(('unknown discard',reason))
            stats['discard_leaves']+=1
        else:
            assert set(node)=={'split','left','right'}
            axis=node['split'];assert type(axis) is int and axis in (0,1)
            lo,hi=box[axis];assert lo<hi
            midpoint=(lo+hi)/2
            left=box.copy();left[axis]=(lo,midpoint)
            right=box.copy();right[axis]=(midpoint,hi)
            visit(node['left'],left,depth+1)
            visit(node['right'],right,depth+1)
    visit(data['tree'],box,0)
    assert stats==data['counts']
    print('PASS',kind,stats)
    return stats

if __name__=='__main__':
    for kind in ('core','ring'):check(kind)
    assert 5*F(43,50)+6*F(17,50)==F(317,50)>F(44,7)>2*PI_HI
    print('PASS: at most four centers can have radius <= 41/40 at q <= 49013/10000')
