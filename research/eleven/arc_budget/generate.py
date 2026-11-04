"""Build exact weighted-arc cover certificates. All proof arithmetic is rational."""
from exact_arcs import *
import json
from pathlib import Path

Q=F(49013,10000)
CORE=F(41,40)

def discarded(box,kind):
    (a,A),(b,B)=box
    if A<b:return 'below-diagonal'
    if kind=='core':
        if a*a+b*b>CORE*CORE:return 'outside-core'
    else:
        if A*A+B*B<CORE*CORE:return 'inside-core'
        if (a+F(1,2))**2+(b+F(1,2))**2>Q:return 'outside-disk'
    return None

def run(kind):
    assert kind in ('core','ring')
    bound=CORE if kind=='core' else F(7,4)
    target=F(43,50) if kind=='core' else F(17,50)
    stats={'nodes':0,'arc_leaves':0,'discard_leaves':0,'max_depth':0}
    def visit(box,depth):
        stats['nodes']+=1
        stats['max_depth']=max(stats['max_depth'],depth)
        why=discarded(box,kind)
        if why:
            stats['discard_leaves']+=1
            return {'discard':why}
        if weighted_lower(box)>=target:
            stats['arc_leaves']+=1
            return {'arc':True}
        assert depth<36, ('UNRESOLVED',kind,box,depth)
        axis=0 if box[0][1]-box[0][0]>=box[1][1]-box[1][0] else 1
        lo,hi=box[axis]
        mid=(lo+hi)/2
        left=box.copy();left[axis]=(lo,mid)
        right=box.copy();right[axis]=(mid,hi)
        return {'split':axis,'left':visit(left,depth+1),'right':visit(right,depth+1)}
    initial=[(F(0),bound),(F(0),bound)]
    tree=visit(initial,0)
    data={'schema':'weighted-circle-arcs-v1','kind':kind,'disk_q':str(Q),'core_radius':str(CORE),
          'radii':[str(x) for x in RADII],'weights':[str(x) for x in WEIGHTS],
          'target':str(target),'initial_box':[[str(lo),str(hi)] for lo,hi in initial],
          'counts':stats,'tree':tree}
    dest=Path(__file__).with_name(kind.upper()+'_ARC_COVER.json')
    dest.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
    print('CLOSED',kind,stats,'->',dest)
    return data

if __name__=='__main__':
    import sys
    for kind in sys.argv[1:] or ['core','ring']:
        run(kind)
