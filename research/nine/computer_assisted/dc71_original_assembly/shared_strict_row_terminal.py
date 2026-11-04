#!/usr/bin/env python3
"""Exact guards for the accepted ABID/AHID;EFG sharp original-row theorem.

Caller prerequisite: an independently reconstructed original physical
strict-001/00 state. This helper proves guard implication only. It does not
replay an ancestor or check coverage of a whole original cell.
"""
from fractions import Fraction as F
from itertools import product

ROW=(0,1,8,3)
SEVEN=(0,1,3,4,5,6,8)
ROWS=(ROW,(0,7,8,3))
PARAMETERS=((F(1,30),F(11,30)),(F(1,50),F(9,20)),(F(1,200),F(53,100)))

def as_box(values):
    result=tuple(tuple(map(F,ab)) for ab in values)
    assert all(len(ab)==2 and ab[0]<=ab[1] for ab in result)
    return result

def unpack(state):
    positions=as_box(state['positions']);scalar=as_box(state['scalar']);angles=as_box(state['angles'])
    assert len(positions)==18 and len(scalar)==36 and len(angles)==9
    raw=state.get('differences',{})
    if isinstance(raw,list):differences={tuple(e['pair']):as_box(e['intervals'])for e in raw}
    else:differences={tuple(pair):as_box(ab)for pair,ab in raw.items()}
    assert all(0<=i<j<9 and len(ab)==2 for(i,j),ab in differences.items())
    return positions,scalar,angles,differences

def difference(positions,differences,i,j,axis):
    lo=positions[2*j+axis][0]-positions[2*i+axis][1]
    hi=positions[2*j+axis][1]-positions[2*i+axis][0]
    if i<j and (i,j)in differences:
        a,b=differences[i,j][axis];lo=max(lo,a);hi=min(hi,b)
    if i>j and (j,i)in differences:
        a,b=differences[j,i][axis];lo=max(lo,-b);hi=min(hi,-a)
    assert lo<=hi
    return lo,hi

def signed_height_rows(U,row=ROW):
    U=F(U);assert U>0
    assert row in ROWS
    a,b,c,d=(2*i+1 for i in row)
    label='ABID' if row==ROW else 'AHID'
    answer=[]
    for signs in product((-1,1),repeat=3):
        s,t,u=signs
        terms=tuple((k,F(v))for k,v in ((a,s),(b,t-s),(c,u-t),(d,-u))if v)
        answer.append((terms,-U,'sharp_'+label+'_height_escape_'+'_'.join(map(str,signs))))
    return answer

def complement_rows(b=F(1,30),U=F(11,30),row=ROW):
    b,U=F(b),F(U);assert(b,U)in PARAMETERS
    assert row in ROWS
    label='ABID' if row==ROW else 'AHID'
    left=row[1];seven=tuple(sorted(set(row)|{4,5,6}))
    rows=[(((16,F(1)),(2*left,F(-1))),F(0),f'sharp_{label}_I_left_escape'),
          (((6,F(1)),(16,F(-1))),F(0),f'sharp_{label}_I_right_escape')]
    # Original AB is actual, so the ABID caller already proves x_A<x_B.
    # The AHID caller must retain the additional order domain x_H<=x_A.
    if row!=ROW:
        rows.insert(0,(((2*left,F(1)),(0,F(-1))),F(0),f'sharp_{label}_H_left_escape'))
    for i in seven:
        rows.append((((36+i,F(-1)),),-b,f'sharp_{label}_abs_beta_escape_{i}'))
    rows+=signed_height_rows(U,row)
    expected=17 if row==ROW else 18
    assert len(rows)==expected and len({r[2]for r in rows})==expected
    return rows

def evaluate_guard(state,row=ROW):
    assert row in ROWS
    seven=tuple(sorted(set(row)|{4,5,6}));assert len(seven)==7
    pos,scalar,angles,diffs=unpack(state)
    order=[difference(pos,diffs,i,j,0)for i,j in zip(row,row[1:])]
    shoulders=[difference(pos,diffs,0,4,1),difference(pos,diffs,3,6,1)]
    beta={i:min(max(map(abs,scalar[9+i])),max(map(abs,angles[i])),scalar[18+i][1])for i in seven}
    # |beta| <= |tan(theta)| because the canonical alpha is positive and <=1.
    corner_upper=max(sum(-v*pos[k][0 if v>0 else 1]for k,v in terms)
                     for terms,rhs,name in signed_height_rows(F(1),row))
    pair_upper=sum(max(map(abs,difference(pos,diffs,i,j,1)))for i,j in zip(row,row[1:]))
    variation_upper=min(corner_upper,pair_upper)
    assert variation_upper>=0
    for b,U in PARAMETERS:
        if all(lo>=0 for lo,hi in order) and all(lo>0 for lo,hi in shoulders) and max(beta.values())<=b and variation_upper<=U:
            return dict(status='PASS_SHARP_PHYSICAL_ROW_GUARD',row=list(row),seven_originals=list(seven),
                beta_bound=str(b),variation_bound=str(U),certified_beta_upper={str(i):str(v)for i,v in beta.items()},
                certified_variation_upper=str(variation_upper),certified_horizontal_order=[list(map(str,x))for x in order],
                certified_shoulder_gaps=[list(map(str,x))for x in shoulders],
                strict_radius_excluded=True,closed_Q_strict_weak_bit_excluded=True,
                ancestor_replay_required=True,whole_parent_cover_checked=False,new_original_cells=0,new_masks=0)
    return dict(status='GUARD_NOT_IMPLIED',row=list(row),seven_originals=list(seven),
                certified_beta_upper={str(i):str(v)for i,v in beta.items()},certified_variation_upper=str(variation_upper),
                certified_horizontal_order=[list(map(str,x))for x in order],certified_shoulder_gaps=[list(map(str,x))for x in shoulders],
                whole_parent_cover_checked=False,new_original_cells=0,new_masks=0)

def evaluate_any_guard(state):
    results=[evaluate_guard(state,row)for row in ROWS]
    for result in results:
        if result['status']=='PASS_SHARP_PHYSICAL_ROW_GUARD':return result
    return dict(status='NO_SHARP_ROW_GUARD_IMPLIED',row_results=results,
                whole_parent_cover_checked=False,new_original_cells=0,new_masks=0)
