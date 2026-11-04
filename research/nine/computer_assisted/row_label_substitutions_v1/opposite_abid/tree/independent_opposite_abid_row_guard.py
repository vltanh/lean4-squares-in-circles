"""Independent quantitative guard for the literal A,B,I,D row application."""
from fractions import Fraction as F
from itertools import product,permutations
from pathlib import Path
import hashlib
import independent_shared_sharp_terminal as SHARP

THEOREM_SOURCES={
 'opposite_tilt_theorem/HAND_PROOF.md':'db830ffbebdc807b0e05f78766e0a0509d11418be31b9a7ef0623b212328831a',
 'opposite_tilt_theorem/opposite_tilt_four_row_guard.py':'3d1a74e8108f9eb02e431e2e25f9f24aa7bffd55aac8f3a956d2f54a11886c0d',
 'opposite_tilt_theorem/verify_chiral_cover.py':'781d2cf9849aa3840cb5d6d2aa4f8b3467949bf64a0cb029b171c27241a40c48'}

def verify_binding(package):
    for name,digest in THEOREM_SOURCES.items():
        assert hashlib.sha256((Path(package)/name).read_bytes()).hexdigest()==digest
    return dict(status='PASS_LITERAL_OPPOSITE_ABID_SOURCE_BINDING',source_sha256=THEOREM_SOURCES,
        physical_originals=[0,1,8,3,4,5,6],seven_distinct_originals=True,
        actual_EF_FG_required=True,unchanged_original_nine_00100_required=True,
        strictly_weak_CD_required=True,closed_Q_equality_blocker='h_C+1/(4*h_C)>=1',
        scalar_complete_cover_replay_required=True,new_original_cells=0,new_masks=0)

def evaluate(state):
    p,s,a,ds=SHARP.inputs(state);row=(0,1,8,3)
    nonnegative=lambda i:a[i][0]>=0 or s[9+i][0]>=0
    nonpositive=lambda i:a[i][1]<=0 or s[9+i][1]<=0
    opposite=(nonnegative(0)and nonpositive(3))or(nonpositive(0)and nonnegative(3))
    orders=[SHARP.gap(p,ds,i,j,0)for i,j in zip(row,row[1:])]
    uppers=[]
    for signs in product((-1,1),repeat=3):
        co={i:0 for i in row}
        for i,j,sign in zip(row,row[1:],signs):co[i]-=sign;co[j]+=sign
        upper=sum(v*p[2*i+1][int(v>0)]for i,v in co.items())
        starts=[];ends=[]
        for i,v in co.items():(ends if v>0 else starts).extend([i]*abs(v))
        assert len(starts)==len(ends)<=3
        for order in set(permutations(ends)):
            value=sum(SHARP.gap(p,ds,i,j,1)[1]if i!=j else F(0)for i,j in zip(starts,order))
            upper=min(upper,value)
        uppers.append(upper)
    variation=max(uppers);passed=opposite and all(lo>=0 for lo,hi in orders)and variation<=F(23,100)
    return dict(status='PASS_OPPOSITE_TILT_ABID_TERMINAL'if passed else'GUARD_NOT_IMPLIED',
        opposite_endpoint_signs_proved=opposite,
        endpoint_angle_intervals=[[str(v)for v in a[i]]for i in(0,3)],
        endpoint_beta_intervals=[[str(v)for v in s[i]]for i in(9,12)],
        horizontal_order_intervals=[[str(v)for v in ab]for ab in orders],
        signed_height_upper_bounds=list(map(str,uppers)),certified_height_variation_upper=str(variation),
        variation_limit='23/100',maximum_proved_variation='23/100',
        theorem_version='opposite_endpoint_full_angle_AHID_row_23_100_v1',
        full_original_ancestry_required=True,whole_original_cover_checked=False,
        new_original_cells=0,new_masks=0,physical_row=list(row),literal_source_substitution={'H':'B'})

def verify_literal(guard,state):
    actual=evaluate(state);assert actual['status']=='PASS_OPPOSITE_TILT_ABID_TERMINAL'and actual==guard
    return actual
