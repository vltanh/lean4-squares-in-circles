#!/usr/bin/env python3
"""Exact, optimizer-free replay of the deep-B angle-contraction table.

The physical nonlinear row bounds are proved in the accompanying hand
manuscript. This file independently reconstructs every rational row and
checks all eight sign/separator cases and all eighteen signed angles.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import time

VARIABLES = 36
RADIUS = F(1, 64)
CENTERS = ((F(-3,2),F(-1,16)),(F(-1,2),F(-17,16)),
 (F(1,2),F(-17,16)),(F(3,2),F(-1,16)),(F(-1),F(15,16)),
 (F(0),F(15,16)),(F(1),F(15,16)),(F(-1,2),F(-1,16)),
 (F(1,2),F(-1,16)))
CASES = tuple(product((-1,1),(-1,1),('horizontal','vertical')))

def physical_rows(sign_c, sign_d, direction):
    assert (sign_c,sign_d,direction) in CASES
    rows=[]
    def add(name, terms, error=F(0)):
        co=[F(0)]*VARIABLES
        for index,value in terms:co[index]+=F(value)
        rows.append((name,tuple(co),F(error)))
    # Variables: 18 original center shifts, 9 signed angles, 9 magnitudes.
    for i in range(9):
        add(f'abs_pos_{i}',[(18+i,1),(27+i,-1)])
        add(f'abs_neg_{i}',[(18+i,-1),(27+i,-1)])
    for i,sg in ((2,sign_c),(3,sign_d)):
        add(f'sign_{i}',[(18+i,-sg)])
        add(f'abs_equal_{i}',[(27+i,1),(18+i,-sg)])
    # The four exact active circle corners, including their angle terms.
    circle=(
      ('circle_0',((0,-4),(1,F(-9,8)),(18,F(-23,16)))),
      ('circle_3',((6,4),(7,F(-9,8)),(21,F(23,16)))),
      ('circle_4',((8,-3),(9,F(23,8)),(22,F(1,16)))),
      ('circle_6',((12,3),(13,F(23,8)),(24,F(-1,16)))))
    for name,terms in circle:add(name,terms,F(3,2))
    for i,j in ((0,1),(1,2),(4,5),(5,6)):
        add(f'actual_{i}_{j}',((2*i,1),(2*j,-1),
            (27+i,F(1,2)),(27+j,F(1,2))),F(25,48))
    for i,j in ((0,7),(7,8),(8,3)):
        for sg in (-1,1):
            add(f'row_{i}_{j}_{sg}',((2*i,1),(2*j,-1),
                (18+i,F(-sg,2)),(18+j,F(sg,2))),F(25,8))
    # The two-owner minimum at horizontal offset +/-1/2 is represented
    # by its two necessary linear inequalities. F's height stays free.
    for i,j in ((0,4),(7,4),(7,5),(8,5),(8,6),(3,6)):
        horizontal=CENTERS[j][0]-CENTERS[i][0]
        assert abs(horizontal)==F(1,2)
        for owner in (i,j):
            add(f'upper_{i}_{j}_{owner}',((2*i+1,1),(2*j+1,-1),
                (18+owner,horizontal)),F(25,8))
    for i,j in ((1,7),(2,8)):
        for sg in (-1,1):
            add(f'lower_{i}_{j}_{sg}',((2*i+1,1),(2*j+1,-1),
                (18+i,F(-sg,2)),(18+j,F(sg,2))),F(25,8))
    add('AB_cone',((0,1),(2,-1),(1,1),(3,-1)))
    add('CD_cone',((4,1),(6,-1),(7,1),(5,-1)))
    if direction=='horizontal':
        add('CD_physical_horizontal',((4,1),(6,-1),
            (20,F(-1,2)),(21,F(-1,2))),F(25,8))
    else:
        add('CD_physical_vertical',((5,1),(7,-1),
            (20,F(1,2)),(21,F(1,2))),F(25,8))
    add('closed_weak_tangent',((6,1),(4,-1),
        (29,F(-1,2)),(30,F(-1,2))))
    # These are exact homogeneous rows, not numerical box bounds.
    for i in range(9):add(f'abs_nonnegative_{i}',((27+i,-1),))
    assert len(rows)==65
    return tuple(rows)

def verify(data):
    assert data['schema']=='weak-outer-deep-boundary-angle-contraction-v1'
    assert F(data['radius'])==RADIUS
    assert tuple(tuple(F(v) for v in p) for p in data['centers'])==CENTERS
    assert data['unboxed_original_center']=='F'
    assert len(data['cases'])==8
    seen_cases=set();count=0;largest=F(0);by_case=[]
    for case in data['cases']:
        key=(case['sign_C'],case['sign_D'],case['separator'])
        assert key in CASES and key not in seen_cases
        seen_cases.add(key);rows=physical_rows(*key)
        assert len(case['proofs'])==18
        seen_targets=set();case_max=F(0)
        for proof in case['proofs']:
            i=proof['angle'];sg=proof['upper_sign']
            assert type(i)is int and 0<=i<9 and sg in (-1,1)
            assert (i,sg) not in seen_targets;seen_targets.add((i,sg))
            combined=[F(0)]*VARIABLES;cost=F(0);seen_rows=set()
            for index,value in proof['weights']:
                assert type(index)is int and 0<=index<len(rows)
                assert index not in seen_rows;seen_rows.add(index)
                weight=F(value);assert weight>0
                _,co,error=rows[index]
                cost+=weight*error
                for j in range(VARIABLES):combined[j]+=weight*co[j]
            target=[F(0)]*VARIABLES;target[18+i]=F(sg)
            assert combined==target,('wrong exact identity',key,i,sg)
            assert cost==F(proof['error_weight'])
            assert cost<1/RADIUS,('insufficient contraction',key,i,sg,cost)
            case_max=max(case_max,cost);count+=1
        assert seen_targets==set(product(range(9),(-1,1)))
        assert case_max==F(case['K'])
        largest=max(largest,case_max)
        by_case.append({'sign_C':key[0],'sign_D':key[1],
          'separator':key[2],'signed_angle_identities':18,'maximum_error_weight':str(case_max)})
    assert seen_cases==set(CASES)
    assert largest==F(data['maximum_K'])==F(4234,69)
    gap=1-RADIUS*largest;assert gap==F(91,2208)>0
    # Exact constants used by the nonlinear cylinder reduction.
    assert (F(1,2)+2*F(1,8))**2+(4*F(1,8))**2==F(13,16)<1
    assert F(91,60)+F(1,16)+F(1,8)<2
    assert F(149,48)<F(25,8)
    assert F(1105,512)<F(9,4)
    return {'status':'PASS','cases':len(seen_cases),'signed_angle_identities':count,
      'homogeneous_rows_per_case':65,'radius':str(RADIUS),'maximum_K':str(largest),
      'contraction_gap':str(gap),'unboxed_original_center':'F','by_case':by_case,
      'physical_scope':'Original strict001 caller in the stated8-center/all9-angle cylinder',
      'whole_mask_closed':False,'nonlinear_row_bounds_source':'WEAK_OUTER_LARGE_GAP_DEEP_BOUNDARY_NONLINEAR_LIFT.md'}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('certificate',type=Path)
    parser.add_argument('--report',type=Path);args=parser.parse_args();start=time.time()
    result=verify(json.loads(args.certificate.read_text()))
    result.update(seconds=time.time()-start,
      certificate_sha256=hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
      verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    if args.report:args.report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
