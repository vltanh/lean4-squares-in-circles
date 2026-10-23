"""Exact replay of the conditional four-core empty radial shell up to 6/5."""
from fractions import Fraction as F
from pathlib import Path
import json
from exact_arcs import rectangle_arc_lower, PI_HI

if not __debug__:
    raise RuntimeError('Run without -O: certificate comparisons use assertions.')
Q=F(49013,10000);CORE=F(41,40);SHELL=F(6,5)
RADII=tuple(F(x,20) for x in [6, 8, 9, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28])
WEIGHTS=tuple(F(x,100000) for x in [4427, 2133, 1608, 11791, 194, 14736, 1004, 2536, 2824, 3126, 1987, 1643, 1603, 4453, 18670, 10064, 8320, 8881])
ARC_SCALE=10**12
TARGETS={"core":F(847,1000),"middle":F(133,200),"ring":F(187,500)}

def check(kind):
    data=json.loads(Path(__file__).with_name('WIDE_SHELL_'+kind.upper()+'_COVER.json').read_text())
    assert data['schema']=='four-core-wide-shell-circle-arcs-v1' and data['kind']==kind
    assert F(data['disk_q'])==Q and F(data['core_radius'])==CORE and F(data['shell_radius'])==SHELL
    assert F(data['target'])==TARGETS[kind]
    assert tuple(map(F,data['radii']))==RADII and tuple(map(F,data['weights']))==WEIGHTS
    assert sum(WEIGHTS)==1 and data["arc_rounding_scale"]==ARC_SCALE
    extent={'core':CORE,'middle':SHELL,'ring':F(7,4)}[kind]
    initial=[tuple(map(F,p)) for p in data['initial_box']]
    assert initial==[(F(0),extent),(F(0),extent)] and Q<F(81,16)
    stats={'nodes':0,'arc_leaves':0,'discard_leaves':0,'max_depth':0}
    def visit(node,box,depth):
        stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
        (a,A),(b,B)=box;assert 0<=a<=A and 0<=b<=B
        if set(node)=={'arc'}:
            assert node['arc'] is True
            rect=[(A-F(1,2),a+F(1,2)),(B-F(1,2),b+F(1,2))]
            assert sum(w*F((rectangle_arc_lower(rect,r)*ARC_SCALE).__floor__(),ARC_SCALE) for w,r in zip(WEIGHTS,RADII))>=TARGETS[kind]
            stats['arc_leaves']+=1
        elif set(node)=={'discard'}:
            reason=node['discard']
            if reason=='below-diagonal':assert A<b
            elif reason=='outside-core':assert kind=='core' and a*a+b*b>CORE*CORE
            elif reason=='inside-core':assert kind in ('middle','ring') and A*A+B*B<CORE*CORE
            elif reason=='outside-shell':assert kind=='middle' and a*a+b*b>SHELL*SHELL
            elif reason=='outside-disk':assert kind=='ring' and (a+F(1,2))**2+(b+F(1,2))**2>Q
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
    print('PASS shell',kind,stats)

if __name__=='__main__':
    for kind in TARGETS:check(kind)
    assert 4*TARGETS['core']+TARGETS['middle']+6*TARGETS['ring']==F(6297,1000)>F(44,7)>2*PI_HI
    print('PASS: four centers <= 41/40 force every other center > 6/5 at q <= 49013/10000')
