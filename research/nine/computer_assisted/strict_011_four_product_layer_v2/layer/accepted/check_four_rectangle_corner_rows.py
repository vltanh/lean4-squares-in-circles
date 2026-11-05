"""Exact continuous-identity fixtures, literal controls, and old-family inclusion."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from copy import deepcopy
import argparse,json,time,hashlib,importlib.util
import physical_unit_four_corner_rows as P
import independent_physical_unit_four_corner_rows as V
import physical_unit_four_corner_separation as N
HERE=Path(__file__).resolve().parent;WORK=HERE.parent.parent
OLD_PATH=WORK/'d_work/unit_frame_corner/physical_unit_corner_rows.py'
OLD_SHA='cdfe8b1f48f6a84bb929f40de7e05cae35134acbd84cc1b4c95fda84d517d575'

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def old_module():
    assert sha(OLD_PATH)==OLD_SHA
    spec=importlib.util.spec_from_file_location('accepted_grouped_corner_control',OLD_PATH)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def fixture(i,variant):
    t=F(i-4,10)if variant==0 else F(4-i,11)
    alpha=(1-t*t)/(1+t*t);beta=2*t/(1+t*t)
    x=F(i%3-1,2);y=F(i//3-1,2)
    hx=F(i%3,5);hy=F((i+1)%3,5)
    ha=F(0)if i==0 else F(1,10);hb=F(0)if i==8 else F(1,7)
    positions=[(F(0),F(0))for k in range(18)]
    positions[2*i]=(x-hx,x+hx);positions[2*i+1]=(y-hy,y+hy)
    scalar=[(F(1),F(1))for k in range(9)]+[(F(0),F(0))for k in range(18)]+[(F(1,2),F(1,2))for k in range(9)]
    scalar[i]=(alpha-ha,alpha+ha);scalar[9+i]=(beta-hb,beta+hb)
    point=[F(0)for k in range(54)];point[2*i]=x;point[2*i+1]=y;point[18+i]=alpha;point[27+i]=beta
    assert alpha*alpha+beta*beta==1
    return positions,scalar,point

def rejected(row,positions,scalar):
    try:V.verify_literal(row,positions,scalar)
    except AssertionError:return True
    raise AssertionError('Damaged row or foreign caller accepted')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);a=ap.parse_args();start=time.monotonic()
    old=old_module();literal=identities=inclusions=damaged=0;corners=set();patterns=set();damage_example=None
    for i,variant in product(range(9),range(2)):
        positions,scalar,point=fixture(i,variant)
        x,y,alpha,beta=point[2*i],point[2*i+1],point[18+i],point[27+i]
        for e,t in product((-1,1),repeat=2):
            corners.add((i,e,t));corner_x=x+(e*alpha-t*beta)/2;corner_y=y+(e*beta+t*alpha)/2
            quadratic=x*x+y*y+e*alpha*x+t*alpha*y+e*beta*y-t*beta*x
            assert corner_x*corner_x+corner_y*corner_y==quadratic+F(1,2)<=P.Q
            for px,py in((F(0),F(0)),(x,y),(x+F(2,7),y-F(3,11))):
                for bits in product((0,1),repeat=4):
                    patterns.add(bits);row=P.row(positions,scalar,i,e,t,px,py,bits)
                    V.verify_literal(row,positions,scalar);literal+=1
                    lhs=sum(v*point[k]for k,v in row[0]);assert lhs<=row[1]
                    signed_values=[e*x,t*y,e*y,-t*x]
                    signed_bounds=[sorted(e*z for z in positions[2*i]),sorted(t*z for z in positions[2*i+1]),
                                   sorted(e*z for z in positions[2*i+1]),sorted(-t*z for z in positions[2*i])]
                    frame_values=[alpha,alpha,beta,beta];frame_bounds=[scalar[i],scalar[i],scalar[9+i],scalar[9+i]]
                    products=[(frame_values[j]-frame_bounds[j][bits[j]])*(signed_values[j]-signed_bounds[j][bits[j]])for j in range(4)]
                    assert min(products)>=0
                    residue=(x-px)**2+(y-py)**2+sum(products)
                    assert quadratic-lhs+row[1]-F(977,256)==residue>=0;identities+=1
                    if i==4 and variant==0 and e==1 and t==-1 and (px,py)==(x,y)and bits==(0,1,1,0):
                        damage_example=(row,positions,scalar)
                for aside,bside in product((0,1),repeat=2):
                    original=old.row(positions,scalar,i,e,t,px,py,aside,bside)
                    extended=P.row(positions,scalar,i,e,t,px,py,(aside,aside,bside,bside))
                    assert original[:2]==extended[:2];inclusions+=1
    row,positions,scalar=damage_example
    co,rhs,name=row
    bad=list(co);bad[0]=(bad[0][0],bad[0][1]+F(1,17));damaged+=rejected((tuple(bad),rhs,name),positions,scalar)
    damaged+=rejected((co,rhs-F(1,19),name),positions,scalar)
    damaged+=rejected((co,rhs,name.rsplit('_',1)[0]+'_2'),positions,scalar)
    wider=deepcopy(positions);wider[8]=(wider[8][0]-1,wider[8][1]+1)
    damaged+=rejected(row,wider,scalar)
    wider_frame=deepcopy(scalar);wider_frame[4]=(wider_frame[4][0]-1,wider_frame[4][1]+1)
    damaged+=rejected(row,positions,wider_frame)
    assert len(corners)==36 and len(patterns)==16
    result=dict(status='PASS_EXACT_FOUR_RECTANGLE_UNIT_CORNER_CONTROLS',literal_rows=literal,
        exact_physical_residual_identities=identities,accepted_two_rectangle_rows_reproduced=inclusions,
        original_signed_corners=len(corners),rectangle_choice_patterns=len(patterns),damaged_controls_rejected=damaged,
        continuous_physical_implication_in_hand_proof=True,optimizer_used=False,
        original_cells_closed=0,masks_closed=0,
        source_sha256={str(Path(p).resolve()):sha(p)for p in(__file__,P.__file__,V.__file__,N.__file__,HERE/'FOUR_RECTANGLE_UNIT_CORNER_HAND_PROOF.md')},
        accepted_parent_producer_sha256=OLD_SHA,seconds=time.monotonic()-start)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k]for k in('status','literal_rows','exact_physical_residual_identities','accepted_two_rectangle_rows_reproduced','damaged_controls_rejected','seconds')}),flush=True)
if __name__=='__main__':main()
