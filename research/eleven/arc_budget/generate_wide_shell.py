"""Exact conditional empty shell: four cores force all other radii > 6/5."""
from exact_arcs import F, rectangle_arc_lower
from pathlib import Path
import json

Q=F(49013,10000);CORE=F(41,40);SHELL=F(6,5)
RADII=tuple(F(x,20) for x in [6, 8, 9, 11, 13, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28])
WEIGHTS=tuple(F(x,100000) for x in [4427, 2133, 1608, 11791, 194, 14736, 1004, 2536, 2824, 3126, 1987, 1643, 1603, 4453, 18670, 10064, 8320, 8881])
ARC_SCALE=10**12
TARGETS={"core":F(847,1000),"middle":F(133,200),"ring":F(187,500)}
assert sum(WEIGHTS)==1

def weighted(box):
    rect=[(hi-F(1,2),lo+F(1,2)) for lo,hi in box]
    return sum(w*F((rectangle_arc_lower(rect,r)*ARC_SCALE).__floor__(),ARC_SCALE) for w,r in zip(WEIGHTS,RADII))

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
    data={'schema':'four-core-wide-shell-circle-arcs-v1','kind':kind,'disk_q':str(Q),'core_radius':str(CORE),'shell_radius':str(SHELL),'target':str(TARGETS[kind]),
          'arc_rounding_scale':ARC_SCALE,'radii':[str(x) for x in RADII],'weights':[str(x) for x in WEIGHTS],
          'initial_box':[[str(a),str(b)] for a,b in box],'counts':stats,'tree':tree}
    dest=Path(__file__).with_name('WIDE_SHELL_'+kind.upper()+'_COVER.json')
    dest.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
    print('CLOSED four-core shell',kind,stats,'->',dest,flush=True)

if __name__=='__main__':
    import sys
    for kind in sys.argv[1:] or ['core','middle','ring']:run(kind)
