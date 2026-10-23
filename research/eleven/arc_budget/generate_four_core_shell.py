"""Exact conditional empty shell: four cores force all other radii > 11/10."""
from exact_arcs import F, rectangle_arc_lower
from pathlib import Path
import json

Q=F(49013,10000);CORE=F(41,40);SHELL=F(11,10)
RADII=(F(2,5),F(13,20),F(9,10),F(6,5),F(5,4),F(7,5))
WEIGHTS=(F(1,10),F(27,100),F(73,1000),F(199,1000),F(179,1000),F(179,1000))
TARGETS={'core':F(33,40),'middle':F(149,200),'ring':F(3,8)}
assert sum(WEIGHTS)==1

def weighted(box):
    rect=[(hi-F(1,2),lo+F(1,2)) for lo,hi in box]
    return sum(w*rectangle_arc_lower(rect,r) for w,r in zip(WEIGHTS,RADII))

def run(kind):
    extent={'core':CORE,'middle':SHELL,'ring':F(7,4)}[kind]
    stats={'nodes':0,'arc_leaves':0,'discard_leaves':0,'max_depth':0}
    def visit(box,depth):
        stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
        (a,A),(b,B)=box;reason=None
        if A<b:reason='below-diagonal'
        elif kind=='core' and a*a+b*b>CORE*CORE:reason='outside-core'
        elif kind in ('middle','ring') and A*A+B*B<CORE*CORE:reason='inside-core'
        elif kind=='middle' and a*a+b*b>SHELL*SHELL:reason='outside-shell'
        elif kind=='ring' and (a+F(1,2))**2+(b+F(1,2))**2>Q:reason='outside-disk'
        if reason:
            stats['discard_leaves']+=1;return {'discard':reason}
        if weighted(box)>=TARGETS[kind]:
            stats['arc_leaves']+=1;return {'arc':True}
        assert depth<40, ('UNRESOLVED',kind,box,depth)
        axis=0 if A-a>=B-b else 1
        lo,hi=box[axis];mid=(lo+hi)/2
        left=box.copy();left[axis]=(lo,mid)
        right=box.copy();right[axis]=(mid,hi)
        return {'split':axis,'left':visit(left,depth+1),'right':visit(right,depth+1)}
    box=[(F(0),extent),(F(0),extent)]
    tree=visit(box,0)
    data={'schema':'four-core-shell-circle-arcs-v1','kind':kind,'disk_q':str(Q),'core_radius':str(CORE),'shell_radius':str(SHELL),'target':str(TARGETS[kind]),
          'radii':[str(x) for x in RADII],'weights':[str(x) for x in WEIGHTS],
          'initial_box':[[str(a),str(b)] for a,b in box],'counts':stats,'tree':tree}
    dest=Path(__file__).with_name('SHELL_'+kind.upper()+'_COVER.json')
    dest.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
    print('CLOSED four-core shell',kind,stats,'->',dest,flush=True)

if __name__=='__main__':
    import sys
    for kind in sys.argv[1:] or ['core','middle','ring']:run(kind)
