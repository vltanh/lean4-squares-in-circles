#!/usr/bin/env python3
"""Independent rational coefficient audit of square area/inertia rows.

The quadratic expected form uses the subset centroid expansion, not the
producer's pairwise expansion. Affine projection ranges are reconstructed
by all four rectangle vertices. This checks identities, not parent closure.
"""
import argparse
import hashlib
import importlib.util
import json
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--generator', type=Path, default=HERE/'square_area_moment_rows.py')
ap.add_argument('--fixture', type=Path, default=HERE/'four_original_planar_row_fixture.json')
ap.add_argument('--output', type=Path, default=HERE/'square_area_moment_rows_replay.json')
args = ap.parse_args()
spec = importlib.util.spec_from_file_location('area_generator_under_review', args.generator)
G = importlib.util.module_from_spec(spec)
spec.loader.exec_module(G)
source = json.loads(args.fixture.read_text())['final']
diffs = {tuple(v['pair']): tuple(tuple(F(x) for x in b) for b in v['intervals']) for v in source['differences']}

class Lift:
    def __init__(self):
        self.index = {(i,j): 54+t for t,(i,j) in enumerate(( (i,j) for i in range(54) for j in range(i,54) ))}
    def multiply(self,out,v,w,scale=1):
        for i,a in v.items():
            for j,b in w.items():
                k=self.index[tuple(sorted((i,j)))];out[k]=out.get(k,F(0))+scale*a*b
    @staticmethod
    def clean(co,rhs,name):
        return tuple((k,v)for k,v in sorted(co.items())if v),F(rhs),name

L = Lift()
def mon(i,j):
    i,j=sorted((i,j))
    return 54+54*i-i*(i-1)//2+j-i

def scalar_rhs(k,B):
    a,b=B[0];c,d=B[1]
    # Reconstruct the Gram matrix and determinant before evaluating the law.
    xx,xy,yy=a*a+c*c,a*b+c*d,b*b+d*d
    determinant=a*d-b*c
    return F(k*k,12)*(xx+yy)-F(7*k*k*k,44)*abs(determinant),(xx,xy,yy)

def expected_quadratic(S,B):
    rhs,(xx,xy,yy)=scalar_rhs(len(S),B);co={};k=len(S)
    def add(i,j,v):
        index=mon(i,j);co[index]=co.get(index,F(0))+v
    for i in S:
        add(2*i,2*i,-(k-1)*xx)
        add(2*i+1,2*i+1,-(k-1)*yy)
        add(2*i,2*i+1,-2*(k-1)*xy)
    for i,j in combinations(S,2):
        add(2*i,2*j,2*xx);add(2*i+1,2*j+1,2*yy)
        add(2*i,2*j+1,2*xy);add(2*i+1,2*j,2*xy)
    return tuple((n,v)for n,v in sorted(co.items())if v),rhs

def expected_linear(S,B):
    rhs,_=scalar_rhs(len(S),B);co=[F(0)]*18
    for i,j in combinations(S,2):
        vertices=list(product(*diffs[i,j]))
        for row in B:
            projections=[sum(a*b for a,b in zip(row,vertex))for vertex in vertices]
            lo,hi=min(projections),max(projections)
            rhs-=lo*hi
            for axis,weight in enumerate(row):
                co[2*i+axis]+=(lo+hi)*weight
                co[2*j+axis]-=(lo+hi)*weight
    return tuple((n,v)for n,v in enumerate(co)if v),rhs

matrices=tuple(tuple(tuple(map(F,row))for row in B)for B in (
    ((1,0),(0,1)), ((1,0),(0,2)), ((2,0),(0,1)),
    ((2,0),(0,3)), ((3,0),(0,2)), ((1,0),(0,3)), ((3,0),(0,1)),
    ((2,1),(0,1)), ((2,-1),(0,1)), ((1,0),(1,2)), ((1,0),(-1,2)),
    ((1,1),(-1,1)), ((0,1),(1,0)), ((1,2),(2,4)), ((0,0),(0,0)),
    ((F(2,3),F(-1,5)),(F(3,7),F(5,11))),
))
checked=0
for k in range(2,10):
    for S in combinations(range(9),k):
        for B in matrices:
            assert G.lower_bound(k,B)==-scalar_rhs(k,B)[0]
            assert G.quadratic_row(S,L,B)[:2]==expected_quadratic(S,B),(S,B,'quadratic')
            assert G.linear_row(S,diffs,B)[:2]==expected_linear(S,B),(S,B,'linear')
            checked+=2

# Check the exact constants in the hand proof and the polynomial/pi identity.
constants={k:-scalar_rhs(k,matrices[0])[0]for k in range(4,10)}
assert constants=={4:F(248,33),5:F(2075,132),6:F(312,11),7:F(6125,132),8:F(2336,33),9:F(4509,44)}
quotient={6:F(1),5:F(-4),4:F(5),2:F(-4),0:F(4)}
numerator={}
for power,value in quotient.items():
    for shift in (0,2):numerator[power+shift]=numerator.get(power+shift,F(0))+value
numerator[0]-=4
assert {p:v for p,v in numerator.items()if v}=={8:F(1),7:F(-4),6:F(6),5:F(-4),4:F(1)}
assert sum(c/F(p+1)for p,c in quotient.items())==F(22,7)

default_expected=[G.quadratic_row(S,L,B)for k in (5,6,7,8,9)for B in matrices[:7]if G.lower_bound(k,B)>0 for S in combinations(range(9),k)]
assert G.generate_quadratic(L)==default_expected
default_linear=[G.linear_row(S,diffs,B)for k in (5,6,7,8,9)for B in matrices[:7]if G.lower_bound(k,B)>0 for S in combinations(range(9),k)]
assert G.generate_linear(diffs)==default_linear
report={
    'status':'PASS_INDEPENDENT_EXACT_AREA_MOMENT_ROW_RECONSTRUCTION',
    'scope':'Theorem constants and coefficient identities only; no original-cell exclusion.',
    'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in (args.generator,args.fixture,Path(__file__))},
    'subset_sizes':list(range(2,10)),
    'rational_matrices_checked':len(matrices),
    'exact_affine_and_quadratic_identities_checked':checked,
    'default_generated_quadratic_rows':len(default_expected),
    'default_generated_linear_rows':len(default_linear),
    'isotropic_constants':{str(k):str(v)for k,v in constants.items()},
    'pi_integral_polynomial_identity':'PASS',
    'new_original_cell_closures':0,
    'new_whole_mask_closures':0,
}
args.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
