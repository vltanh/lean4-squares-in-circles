"""Independent cover replay; no imports from the certificate generator."""
import json
from pathlib import Path
from fractions import Fraction as F
from independent_arcs import box_weight_lower, PI

if not __debug__:
    raise RuntimeError('Run without -O; proof checks use assertions.')

def replay(path):
    data=json.loads(Path(path).read_text())
    assert data['schema']=='weighted-circle-arcs-v1'
    kind=data['kind'];assert kind in ('core','ring')
    limit=F(41,40);q=F(49013,10000)
    target=F(43 if kind=='core' else 17,50)
    bound=limit if kind=='core' else F(7,4)
    assert F(data['core_radius'])==limit and F(data['disk_q'])==q
    assert list(map(F,data['radii']))==[F(3,10),F(3,5),F(5,4)]
    assert list(map(F,data['weights']))==[F(6,200),F(85,200),F(109,200)]
    assert F(data['target'])==target
    assert [[F(z) for z in row] for row in data['initial_box']]==[[0,bound],[0,bound]]
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
            assert box_weight_lower(a,A,b,B)>=target, (kind,box)
            stats['arc_leaves']+=1
        else:
            assert set(node)=={'discard'}
            reason=node['discard']
            tests={'below-diagonal':A<b,
                   'outside-core':kind=='core' and a*a+b*b>limit*limit,
                   'inside-core':kind=='ring' and A*A+B*B<limit*limit,
                   'outside-disk':kind=='ring' and (a+F(1,2))**2+(b+F(1,2))**2>q}
            assert reason in tests and tests[reason],(reason,box)
            stats['discard_leaves']+=1
    visit(data['tree'],[F(0),bound,F(0),bound],0)
    assert stats==data['counts'],(stats,data['counts'])
    assert stats==({'nodes':4367,'arc_leaves':1933,'discard_leaves':251,'max_depth':20}
                   if kind=='core' else
                   {'nodes':423,'arc_leaves':104,'discard_leaves':108,'max_depth':18})
    print('PASS independent replay',kind,stats,flush=True)

if __name__=='__main__':
    import sys
    paths=sys.argv[1:] or [Path(__file__).with_name(k+'_ARC_COVER.json') for k in ('CORE','RING')]
    for path in paths:replay(path)
    assert 5*F(43,50)+6*F(17,50)==F(317,50)>F(44,7)>2*PI[1]
    print('PASS: five or more cores exceed the weighted angular budget.')
