from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json,hashlib,sys
import physical_incircle_chords as P
import independent_incircle_chords as I
cases=negative=0
for axis,sign,L,U in product((0,1),(-1,1),(F(-1),F(-3,5),F(0)),(F(0),F(4,5),F(1))):
    if L>=U:continue
    box=[None,None];box[axis]=(F(0),F(2))if sign==1 else(F(-2),F(0));box[1-axis]=(L,U);ds={(2,8):box}
    r=P.row(2,8,axis,sign,L,U,P.sqrt_lower(1-L*L),P.sqrt_lower(1-U*U));I.verify_literal(r,ds)
    for n in range(-12,13):
        q=F(n,12);d=(1-q*q)/(1+q*q);t=2*q/(1+q*q)
        if not L<=t<=U:continue
        vals=[F(0)]*18;vals[16+axis]=sign*d;vals[17-axis]=t
        assert sum(c*vals[k]for k,c in r[0])<=r[1];cases+=1
    bad=(r[0],r[1]-1,r[2])
    try:I.verify_literal(bad,ds)
    except AssertionError:negative+=1
    else:raise AssertionError('bad rhs accepted')
    wrong={key:[tuple(x)for x in val]for key,val in ds.items()};wrong[(2,8)][axis]=(F(-1),F(1))
    try:I.verify_literal(r,wrong)
    except AssertionError:negative+=1
    else:raise AssertionError('unproved sign accepted')
    wrong={key:[tuple(x)for x in val]for key,val in ds.items()};wrong[(2,8)][1-axis]=(L-1,U)
    try:I.verify_literal(r,wrong)
    except AssertionError:negative+=1
    else:raise AssertionError('insufficient interval accepted')
report=dict(status='PASS_EXACT_INCIRCLE_CHORD_CONTROLS',exact_unit_distance_cases=cases,damaged_literals_rejected=negative,source_sha256={Path(m).name:hashlib.sha256(Path(m).read_bytes()).hexdigest()for m in(__file__,P.__file__,I.__file__)},new_original_cells=0,new_masks=0)
Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='source_sha256'}))
