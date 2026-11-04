#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib,json
import physical_projection_squares as P
import independent_physical_projection_squares as I

def main():
    weights=[tuple(F((k+3)*(j+1)%17-8,2+(k+j)%7)for j in range(4))for k in range(23)]
    diff={(2,7):((F(-2,3),F(5,4)),(F(-3,2),F(7,6)))};rebuilt=identities=damaged=0
    for owner,axis,sign in product((2,7),(0,1),(-1,1)):
        choices=[((2,7),'sat',(owner,axis,sign))]
        for q in weights:
            row=P.row(choices,diff,0,q);I.verify_literal(row,choices,diff);rebuilt+=1
            for t,px,py in product((F(-3,8),F(0),F(1,3)),range(5),range(5)):
                aa,bb=(1-t*t)/(1+t*t),2*t/(1+t*t)
                nx,ny=(sign*aa,sign*bb)if axis==0 else(-sign*bb,sign*aa)
                (xl,xu),(yl,yu)=diff[2,7];dx=xl+(xu-xl)*px/4;dy=yl+(yu-yl)*py/4
                values={4:F(0),5:F(0),14:dx,15:dy,18+owner:aa,27+owner:bb,54:nx*dx,55:ny*dy}
                slack=row[1]-sum(v*values[k]for k,v in row[0]);x,y,a,b=q
                norm=(x+a*nx+b*dx)**2+(y+a*ny+b*dy)**2
                error=b*b*((dx-xl)*(xu-dx)+(dy-yl)*(yu-dy))
                assert slack==norm+error and slack>=0;identities+=1
        row=P.row(choices,diff,0,weights[0])
        try:I.verify_literal((row[0],row[1]-1,row[2]),choices,diff)
        except AssertionError:damaged+=1
        else:raise AssertionError('Damaged row accepted')
    sources={str(Path(p).resolve()):hashlib.sha256(Path(p).read_bytes()).hexdigest()for p in(__file__,P.__file__,I.__file__)}
    r=dict(status='PASS_EXACT_PHYSICAL_PROJECTION_SQUARE_IDENTITIES',independently_rebuilt_rows=rebuilt,
        exact_physical_evaluations=identities,damaged_rows_rejected=damaged,source_sha256=sources,new_original_cells=0,new_masks=0)
    Path(__file__).with_name('PHYSICAL_PROJECTION_SQUARES_EXACT_REPLAY.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
if __name__=='__main__':main()
