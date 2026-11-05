"""Independent exact guard and rational criterion for accepted ABID/AHID rows.

The caller must reconstruct the unchanged original-nine strict-001/00 state.
This module certifies a conditional terminal only; it never grants cover credit.
It does not import the published guard or any numerical discovery code.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib

ROWS=((0,1,8,3),(0,7,8,3))
PARAMETERS=((F(1,30),F(11,30)),(F(1,50),F(9,20)),(F(1,200),F(53,100)))
GUARD_SHA='43a74c66c7c0b91da76e6577ce511e6ae8de7bda9ab6e0adbf81a1cc2b013d43'
PROOF_SHA={
 'ancestry/sharp_provenance/a4b923589a52be57_SHARED_ABID_STRICT_BOUNDARY_TERMINAL.md':
 'a4b923589a52be57fb84e484c92f4438c275dbc13e5b01a8e9add9d4dd40edcb',
 'ancestry/sharp_provenance/0d233bddea414938_ALL_SIGN_CORRELATED_CORNER_ROW_HAND_STRENGTHENING.md':
 '0d233bddea414938482cb312519da061a546d26c4ee5a5bb83a14b48c178ed02'}

def box(raw):
    answer=tuple(tuple(F(v)for v in p)for p in raw)
    assert all(len(p)==2 and p[0]<=p[1]for p in answer)
    return answer

def inputs(state):
    pos,scalar,angles=(box(state[k])for k in('positions','scalar','angles'))
    assert len(pos)==18 and len(scalar)==36 and len(angles)==9
    ds=state.get('differences',{})
    ds={tuple(p['pair']):box(p['intervals'])for p in ds}if isinstance(ds,list)else{tuple(k):box(v)for k,v in ds.items()}
    assert all(len(k)==2 and 0<=k[0]<k[1]<9 and len(v)==2 for k,v in ds.items())
    return pos,scalar,angles,ds

def gap(pos,ds,i,j,axis):
    lower=pos[2*j+axis][0]-pos[2*i+axis][1]
    upper=pos[2*j+axis][1]-pos[2*i+axis][0]
    pair=tuple(sorted((i,j)))
    if pair in ds:
        lo,hi=ds[pair][axis]
        if i>j:lo,hi=-hi,-lo
        lower,upper=max(lower,lo),min(upper,hi)
    assert lower<=upper
    return lower,upper

def evaluate_guard(state,row=ROWS[0]):
    row=tuple(row);assert row in ROWS
    pos,scalar,angles,ds=inputs(state)
    seven=sorted(set(row)|{4,5,6})
    order=[gap(pos,ds,i,j,0)for i,j in zip(row,row[1:])]
    shoulders=[gap(pos,ds,0,4,1),gap(pos,ds,3,6,1)]
    beta={str(i):min(abs(scalar[9+i][0])if abs(scalar[9+i][0])>=abs(scalar[9+i][1])else abs(scalar[9+i][1]),
        max(abs(angles[i][0]),abs(angles[i][1])),scalar[18+i][1])for i in seven}
    coordinate_upper=[]
    for signs in product((-1,1),repeat=3):
        coefficients={i:0 for i in row}
        for i,j,s in zip(row,row[1:],signs):coefficients[i]-=s;coefficients[j]+=s
        coordinate_upper.append(sum(v*pos[2*i+1][int(v>0)]for i,v in coefficients.items()))
    interval_upper=sum(max(abs(a),abs(b))for a,b in(gap(pos,ds,i,j,1)for i,j in zip(row,row[1:])))
    variation=min(max(coordinate_upper),interval_upper);assert variation>=0
    common=dict(row=list(row),seven_originals=seven,certified_beta_upper={k:str(v)for k,v in beta.items()},
        certified_variation_upper=str(variation),certified_horizontal_order=[list(map(str,v))for v in order],
        certified_shoulder_gaps=[list(map(str,v))for v in shoulders],
        whole_parent_cover_checked=False,new_original_cells=0,new_masks=0)
    for b,U in PARAMETERS:
        if all(a>=0 for a,_ in order)and all(a>0 for a,_ in shoulders)and max(beta.values())<=b and variation<=U:
            return dict(common,status='PASS_SHARP_PHYSICAL_ROW_GUARD',beta_bound=str(b),variation_bound=str(U),
                strict_radius_excluded=True,closed_Q_strict_weak_bit_excluded=True,ancestor_replay_required=True)
    return dict(common,status='GUARD_NOT_IMPLIED')

def evaluate_any_guard(state):
    results=[evaluate_guard(state,row)for row in ROWS]
    for result in results:
        if result['status']=='PASS_SHARP_PHYSICAL_ROW_GUARD':return result
    return dict(status='NO_SHARP_ROW_GUARD_IMPLIED',row_results=results,
        whole_parent_cover_checked=False,new_original_cells=0,new_masks=0)

def criterion(b,U):
    b,U=F(b),F(U);assert (b,U)in PARAMETERS
    a,B,k,T,rho,L=F(46),F(27,2),F(207,16),F(211,4),F(91,60),F(7,10)
    P,C,J=(a+k)/2,(a-k)/2,B+k/2
    z=1-b*b;delta=b/(2-b*b);c=(1-b-3*b*b-4*b**3)/2
    X0=3-b*U/z;C0=(T-a*(X0-rho-(1+b)/2))/B;lam=k*L/z
    ep,em=B-k/2-J*delta,k/2-J*delta
    p=C+P*delta-k*c;q=em+C-P*delta-lam
    A=a*c-a*U/(2*z**3)-a*b*(b+F(1,2))/z;K=a*a/(23*z*z)-a
    checks=(0<b<F(1,2),U>0,L>0,c>0,2*b*rho+U<1,L+2*b*rho<1,
        rho-F(3,2)+C0<L,C0+(1+b)/2<X0-rho,
        a*z>k*b,k*z>a*b,B*z>k*b,k*z>B*b,em<k*c<ep,k*c+em-lam>0,
        p>0,q>p,A>p,K>=0,min(A,q)-p-K*b>0)
    assert all(checks)
    return dict(beta_bound=str(b),variation_bound=str(U),endpoint_bound=str(L),
        rational_conditions=len(checks),epsilon=str(min(A,q)-p-K*b))

def verify_binding(package):
    root=Path(package);files={'shared_strict_row_terminal.py':GUARD_SHA,**PROOF_SHA}
    for name,digest in files.items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest
    criteria=[criterion(b,U)for b,U in PARAMETERS]
    assert criteria[-1]['epsilon']=='58049449601280546655747607/327651328921587200064000000'
    return dict(status='PASS_SHARED_SHARP_ROW_PHYSICAL_BINDING',files=files,criteria=criteria,
        original_mask='001/00',all_nine_originals_required=True,original_strict_CD_required=True,
        original_ancestry_required=True,new_original_cells=0,new_masks=0)

def verify_literal(guard,state):
    actual=evaluate_any_guard(state)
    assert actual['status']=='PASS_SHARP_PHYSICAL_ROW_GUARD'and actual==guard
    return actual
