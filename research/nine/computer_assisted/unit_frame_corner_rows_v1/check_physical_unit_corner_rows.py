#!/usr/bin/env python3
"""Exact physical corner and nonnegative rectangle residual controls."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib,json
import physical_unit_corner_rows as P
import independent_physical_unit_corner_rows as I
HERE=Path(__file__).resolve().parent

def main():
    rows=evaluations=contained=damaged=degenerate=0
    for i,e,t,center_p,aside,bside,collapsed in product(
            range(9),(-1,1),(-1,1),
            ((F(-3,2),F(-1,2)),(F(0),F(0)),(F(7,5),F(3,5))),
            (0,1),(0,1),(False,True)):
        bx,by=((F(-3,2),F(1,2)),(F(-1,2),F(3,2)))if not collapsed else((F(1,2),)*2,(F(-1,2),)*2)
        ab,bb=((F(7,10),F(1)),(F(-7,10),F(7,10)))if not collapsed else((F(1),)*2,(F(0),)*2)
        positions=[bx if k%2==0 else by for k in range(18)]
        scalar=[ab]*9+[bb]*9+[(F(0),F(1))]*18
        px,py=center_p;row=P.row(positions,scalar,i,e,t,px,py,aside,bside)
        I.verify_literal(row,positions,scalar);rows+=1;degenerate+=int(collapsed)
        rv=[e*x+t*y for x,y in product(bx,by)];sv=[e*y-t*x for x,y in product(bx,by)]
        a0,b0=ab[aside],bb[bside];r0=min(rv)if aside==0 else max(rv);s0=min(sv)if bside==0 else max(sv)
        xs,ys=sorted(set((bx[0],sum(bx)/2,bx[1]))),sorted(set((by[0],sum(by)/2,by[1])))
        slopes=(F(0),)if collapsed else(F(-3,8),F(0),F(3,8))
        for x,y,z in product(xs,ys,slopes):
            alpha,beta=(1-z*z)/(1+z*z),2*z/(1+z*z)
            assert ab[0]<=alpha<=ab[1]and bb[0]<=beta<=bb[1]
            assert alpha*alpha+beta*beta==1
            r,s=e*x+t*y,e*y-t*x
            zx,zy=x+(e*alpha-t*beta)/2,y+(e*beta+t*alpha)/2
            exact=x*x+y*y+alpha*r+beta*s
            assert zx*zx+zy*zy==exact+F(1,2)
            values={2*i:x,2*i+1:y,18+i:alpha,27+i:beta}
            lhs=sum(v*values[k]for k,v in row[0])
            residual=(x-px)**2+(y-py)**2+(alpha-a0)*(r-r0)+(beta-b0)*(s-s0)
            assert residual>=0
            assert row[1]-lhs==P.Q-F(1,2)-exact+residual
            if zx*zx+zy*zy<=P.Q:assert lhs<=row[1];contained+=1
            evaluations+=1
        altered=list(row[0]);k,v=altered[0];altered[0]=(k,v+1)
        for bad in((tuple(altered),row[1],row[2]),(row[0],row[1]-1,row[2])):
            try:I.verify_literal(bad,positions,scalar)
            except AssertionError:damaged+=1
            else:raise AssertionError('Damaged unit-corner row accepted')
    # This deliberately nonunit relaxed frame fits its displayed corners in Q,
    # but is cut off by a necessary row using the original unit-frame identity.
    x,y,alpha,beta=F(29,20),F(3,5),F(4,5),F(3,10)
    assert all((x+(e*alpha-t*beta)/2)**2+(y+(e*beta+t*alpha)/2)**2<=P.Q
               for e,t in product((-1,1),repeat=2))
    positions=[(F(0),F(0))]*18
    positions[0],positions[1]=(x-F(1,1000),x+F(1,1000)),(y-F(1,1000),y+F(1,1000))
    scalar=[(F(7,10),F(1))]*9+[(F(-7,10),F(7,10))]*9+[(F(0),F(1))]*18
    row=P.row(positions,scalar,0,1,1,x,y,0,0);I.verify_literal(row,positions,scalar)
    values={0:x,1:y,18:alpha,27:beta};violation=sum(v*values[k]for k,v in row[0])-row[1]
    assert violation>0
    files=(__file__,P.__file__,I.__file__,HERE/'UNIT_FRAME_CORNER_HAND_PROOF.md')
    report=dict(status='PASS_EXACT_UNIT_FRAME_CORNER_ROWS',independently_rebuilt_rows=rows,
        exact_physical_expansions=evaluations,contained_corner_evaluations=contained,
        zero_width_interval_rows=degenerate,damaged_literals_rejected=damaged,
        nonunit_relaxation_control_violation=str(violation),
        source_sha256={str(Path(p).resolve()):hashlib.sha256(Path(p).read_bytes()).hexdigest()for p in files},
        new_original_cells=0,new_masks=0)
    (HERE/'EXACT_CONTROLS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()if k!='source_sha256'}))

if __name__=='__main__':main()
