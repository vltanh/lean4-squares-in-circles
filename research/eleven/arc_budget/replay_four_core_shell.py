"""Independent arithmetic replay of the four-core empty-shell certificate."""
import json
from pathlib import Path
from fractions import Fraction as F
from independent_arcs import rectangle_angle_lower, PI

if not __debug__:
    raise RuntimeError('Run without -O; proof checks use assertions.')

Q, CORE, SHELL = F(49013,10000), F(41,40), F(11,10)
RADII = [F(2,5),F(13,20),F(9,10),F(6,5),F(5,4),F(7,5)]
WEIGHTS = [F(1,10),F(27,100),F(73,1000),F(199,1000),F(179,1000),F(179,1000)]
TARGETS = {'core':F(33,40),'middle':F(149,200),'ring':F(3,8)}

def replay(kind):
    data=json.loads(Path(__file__).with_name('SHELL_'+kind.upper()+'_COVER.json').read_text())
    assert data['schema']=='four-core-shell-circle-arcs-v1' and data['kind']==kind
    assert [F(data[k]) for k in ['disk_q','core_radius','shell_radius','target']]==[Q,CORE,SHELL,TARGETS[kind]]
    assert list(map(F,data['radii']))==RADII and list(map(F,data['weights']))==WEIGHTS
    extent={'core':CORE,'middle':SHELL,'ring':F(7,4)}[kind]
    assert [[F(z) for z in row] for row in data['initial_box']]==[[0,extent],[0,extent]]
    assert Q<F(81,16) and sum(WEIGHTS)==1
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
                      for w,r in zip(WEIGHTS,RADII))
            assert lower>=TARGETS[kind],box
            stats['arc_leaves']+=1
        else:
            assert set(node)=={'discard'}
            tests={'below-diagonal':A<b,
                   'outside-core':kind=='core' and a*a+b*b>CORE*CORE,
                   'inside-core':kind in ('middle','ring') and A*A+B*B<CORE*CORE,
                   'outside-shell':kind=='middle' and a*a+b*b>SHELL*SHELL,
                   'outside-disk':kind=='ring' and (a+F(1,2))**2+(b+F(1,2))**2>Q}
            assert node['discard'] in tests and tests[node['discard']]
            stats['discard_leaves']+=1
    visit(data['tree'],[F(0),extent,F(0),extent],0)
    assert stats==data['counts']
    print('PASS independent shell',kind,stats,flush=True)

if __name__=='__main__':
    for kind in TARGETS:replay(kind)
    assert 4*TARGETS['core']+TARGETS['middle']+6*TARGETS['ring']==F(1259,200)>F(44,7)>2*PI[1]
    print('PASS independent four-core empty shell, radius 11/10')
