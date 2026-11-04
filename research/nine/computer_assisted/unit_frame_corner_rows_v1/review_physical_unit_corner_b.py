#!/usr/bin/env python3
"""Independent residual-identity and physical-substitution controls for B."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib,json
import physical_unit_corner_rows as P
import independent_physical_unit_corner_rows as I

def main():
    frames=((F(1),F(0)),(F(3,5),F(4,5)),(F(5,13),F(-12,13)),(F(4,5),F(-3,5)),(F(0),F(1)))
    count=contained=0
    for i,e,t,(alpha,beta),aside,bside in product(range(9),(-1,1),(-1,1),frames,(0,1),(0,1)):
        assert alpha*alpha+beta*beta==1
        x,y=F(i-4,8),F(e-t,7);px,py=x+F(1,7),y-F(1,11)
        positions=[(F(0),F(0))]*18;scalar=[(F(0),F(0))]*36
        bx=(x-F(1,4),x+F(1,4));by=(y-F(1,5),y+F(1,5))
        aa=(alpha-F(1,32),alpha+F(1,32));bb=(beta-F(1,16),beta+F(1,16))
        positions[2*i]=bx;positions[2*i+1]=by;scalar[i]=aa;scalar[9+i]=bb
        literal=P.row(positions,scalar,i,e,t,px,py,aside,bside);I.verify_literal(literal,positions,scalar)
        co,rhs,_=literal;values={2*i:x,2*i+1:y,18+i:alpha,27+i:beta}
        lhs=sum(v*values[k]for k,v in co)
        r=e*x+t*y;s=e*y-t*x
        rr=[e*xx+t*yy for xx,yy in product(bx,by)];ss=[e*yy-t*xx for xx,yy in product(bx,by)]
        a0=aa[aside];b0=bb[bside];r0=(min(rr),max(rr))[aside];s0=(min(ss),max(ss))[bside]
        residual=(x-px)**2+(y-py)**2+(alpha-a0)*(r-r0)+(beta-b0)*(s-s0)
        assert residual>=0
        assert x*x+y*y+alpha*r+beta*s-(lhs-px*px-py*py-a0*r0-b0*s0)==residual
        corner_x=x+(e*alpha-t*beta)/2;corner_y=y+(e*beta+t*alpha)/2
        assert corner_x*corner_x+corner_y*corner_y==x*x+y*y+F(1,2)+alpha*r+beta*s
        if corner_x*corner_x+corner_y*corner_y<=F(1105,256):assert lhs<=rhs;contained+=1
        count+=1
    here=Path(__file__).resolve().parent
    names=['physical_unit_corner_rows.py','independent_physical_unit_corner_rows.py','physical_unit_corner_separation.py','UNIT_FRAME_CORNER_HAND_PROOF.md',Path(__file__).name]
    report=dict(status='PASS_INDEPENDENT_B_UNIT_CORNER_REVIEW',exact_literal_and_residual_checks=count,
        physical_contained_corner_checks=contained,source_sha256={n:hashlib.sha256((here/n).read_bytes()).hexdigest()for n in names},
        original_cells_closed=0,masks_closed=0)
    (here/'UNIT_FRAME_CORNER_B_REVIEW.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)

if __name__=='__main__':main()
