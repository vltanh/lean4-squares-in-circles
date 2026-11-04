#!/usr/bin/env python3
"""Exact source-bound identities and damaged-row controls."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib,json
import physical_pair_frame_squares as P
import independent_physical_pair_frame_squares as I

def unit(t):return (1-t*t)/(1+t*t),2*t/(1+t*t)
def main():
    parameters=[tuple(F((k+3)*(j+1)%17-8,2+(k+j)%7)for j in range(6))for k in range(47)]
    frame_t=tuple(F(k,8)for k in range(-3,4));identities=0;rebuilt=0;damaged=0
    for owner,axis,sign in product((2,7),(0,1),(-1,1)):
        choices=[((1,3),'proxy',(0,1)),((0,4),'sat',(4,0,-1)),((2,7),'sat',(owner,axis,sign))]
        for q in parameters:
            row=P.row(choices,1,q);I.verify_literal(row,choices);rebuilt+=1
            for ti,tj in product(frame_t,repeat=2):
                ai,bi=unit(ti);aj,bj=unit(tj)
                values={20:ai,29:bi,25:aj,34:bj,62:ai*aj,63:bi*bj,64:ai*bj,65:bi*aj}
                lhs=sum(v*values[k]for k,v in row[0]);slack=row[1]-lhs
                x,y,a,b,c,d=q
                norm=(x+a*ai-b*bi+c*aj-d*bj)**2+(y+a*bi+b*ai+c*bj+d*aj)**2
                assert slack==norm and slack>=0;identities+=1
        row=P.row(choices,1,parameters[0])
        try:I.verify_literal((row[0],row[1]+1,row[2]),choices)
        except AssertionError:damaged+=1
        else:raise AssertionError('Damaged right side accepted')
    sources={str(Path(p).resolve()):hashlib.sha256(Path(p).read_bytes()).hexdigest()for p in(__file__,P.__file__,I.__file__)}
    report=dict(status='PASS_EXACT_PHYSICAL_PAIR_FRAME_SQUARE_IDENTITIES',independently_rebuilt_rows=rebuilt,
        exact_physical_evaluations=identities,damaged_rows_rejected=damaged,source_sha256=sources,
        new_original_cells=0,new_masks=0)
    out=Path(__file__).with_name('PHYSICAL_PAIR_FRAME_SQUARES_EXACT_REPLAY.json');out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))
if __name__=='__main__':main()
