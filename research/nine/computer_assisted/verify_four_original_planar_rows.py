#!/usr/bin/env python3
"""Independent exact coefficient audit of the four-center row generator.

This is a row-identity audit, not a whole-cell infeasibility certificate.
The expected quadratic rows use the four-point centroid identity. The
expected affine rows use explicitly combined Cartesian or diagonal
secants, without calling the generator's algebra helpers.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--generator', type=Path, default=HERE/'four_original_planar_rows.py')
parser.add_argument('--lift', type=Path, default=None)
parser.add_argument('--state', type=Path, default=HERE/'four_original_planar_row_fixture.json')
parser.add_argument('--output', type=Path, default=HERE/'four_original_planar_rows_replay.json')
args = parser.parse_args()
GENERATOR, STATE = args.generator.resolve(), args.state.resolve()
LIFT = args.lift.resolve() if args.lift else None

def module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    obj = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj

FC = module(GENERATOR, 'four_center_rows_under_review')
class StandardQuadraticLayout:
    N = 54
    SIZE = 1539
    def __init__(self):
        self.index = {(i,j): 54+k for k,(i,j) in enumerate(( (i,j) for i in range(54) for j in range(i,54) ))}
    def mon(self,i,j):
        return self.index[tuple(sorted((i,j)))]
    @staticmethod
    def delta(i,j,axis):
        return {2*j+axis:Q(1),2*i+axis:Q(-1)}
    def multiply(self,out,v,w,scale=1):
        for i,a in v.items():
            for j,b in w.items():
                k=self.mon(i,j);out[k]=out.get(k,Q(0))+Q(scale)*a*b
    @staticmethod
    def clean(out,rhs,name):
        return tuple((k,v)for k,v in sorted(out.items())if v),Q(rhs),name
L = module(LIFT, 'moment_lift_under_review') if LIFT else StandardQuadraticLayout()
source = json.loads(STATE.read_text())['final']
differences = {tuple(r['pair']): tuple(tuple(map(Q, b)) for b in r['intervals'])
               for r in source['differences']}
diagonal = {tuple(r['pair']): tuple(tuple(map(Q, b)) for b in r['intervals'])
            for r in source['diagonal']}

def expected_linear(dd, gg, mixed):
    expected = []
    for quad in combinations(range(9), 4):
        pairs = tuple(combinations(quad, 2))
        options = [(0, 1) if mixed and pair in gg else (0,) for pair in pairs]
        for codes in product(*options):
            coeff = [Q(0) for _ in range(18)]
            constant = Q(-8)
            for (i, j), code in zip(pairs, codes):
                if code:
                    (a, b), (c, d) = gg[i, j]
                    x_weight = (a+b+c+d)/2
                    y_weight = (a+b-c-d)/2
                    constant -= (a*b+c*d)/2
                else:
                    (a, b), (c, d) = dd[i, j]
                    x_weight, y_weight = a+b, c+d
                    constant -= a*b+c*d
                coeff[2*i] += x_weight
                coeff[2*j] -= x_weight
                coeff[2*i+1] += y_weight
                coeff[2*j+1] -= y_weight
            name = 'four_center_energy_' + '_'.join(map(str, quad)) + '_' + ''.join(map(str, codes))
            expected.append((tuple((i, c) for i, c in enumerate(coeff) if c), constant, name))
    return expected

audit = []
for name, gg, mixed in (
    ('Cartesian only', {}, True),
    ('Full mixed Cartesian/diagonal', diagonal, True),
    ('Diagonal supplied, mixing disabled', diagonal, False),
    ('Partial diagonal dictionary', {p: b for k, (p, b) in enumerate(sorted(diagonal.items())) if k % 3 == 0}, True),
):
    actual = FC.linear_rows(differences, gg, all_combinations=mixed)
    expected = expected_linear(differences, gg, mixed)
    assert actual == expected, name
    audit.append({'kind': name, 'rows_checked': len(actual), 'status': 'PASS_EXACT_COEFFICIENT_IDENTITY'})

assert L.N == 54 and L.SIZE == 1539
def independent_monomial(i, j):
    a, b = sorted((i, j))
    return 54 + 54*a - a*(a-1)//2 + b-a

expected = []
for quad in combinations(range(9), 4):
    coeff = {}
    # -sum_{i<j}|p_i-p_j|^2 = -3 sum_i |p_i|^2 + 2 sum_{i<j} p_i dot p_j.
    for i in quad:
        for axis in (0, 1):
            k = 2*i+axis
            coeff[independent_monomial(k, k)] = Q(-3)
    for i, j in combinations(quad, 2):
        for axis in (0, 1):
            coeff[independent_monomial(2*i+axis, 2*j+axis)] = Q(2)
    expected.append((tuple(sorted(coeff.items())), Q(-8),
                     'four_center_energy_moment_' + '_'.join(map(str, quad))))
actual = FC.moment_rows(L)
assert actual == expected
audit.append({'kind': 'Quadratic centroid expansion with independent monomial indexing',
              'rows_checked': len(actual), 'status': 'PASS_EXACT_COEFFICIENT_IDENTITY'})

matching_counts = {'Cartesian matching rows': 0, 'Mixed Cartesian/diagonal matching rows': 0,
                   'Quadratic matching rows with independent monomial indexing': 0}
for quad in combinations(range(9), 4):
    # Every matching is uniquely determined by the partner of the first point.
    a, *remaining = quad
    independent_matchings = []
    for b in remaining:
        c, d = [x for x in remaining if x != b]
        independent_matchings.append(((a, b), (c, d)))
    assert tuple(independent_matchings) == FC.matchings(quad)
    for choice, pairs in enumerate(independent_matchings):
        for label, gg in (('Cartesian matching rows', {}), ('Mixed Cartesian/diagonal matching rows', diagonal)):
            expected = []
            options = [(0, 1) if pair in gg else (0,) for pair in pairs]
            for codes in product(*options):
                coeff = [Q(0) for _ in range(18)]
                constant = Q(-4)
                for (i, j), code in zip(pairs, codes):
                    if code:
                        (lo_s, hi_s), (lo_t, hi_t) = gg[i, j]
                        x_weight = (lo_s+hi_s+lo_t+hi_t)/2
                        y_weight = (lo_s+hi_s-lo_t-hi_t)/2
                        constant -= (lo_s*hi_s+lo_t*hi_t)/2
                    else:
                        (lo_x, hi_x), (lo_y, hi_y) = differences[i, j]
                        x_weight, y_weight = lo_x+hi_x, lo_y+hi_y
                        constant -= lo_x*hi_x+lo_y*hi_y
                    coeff[2*i] += x_weight
                    coeff[2*j] -= x_weight
                    coeff[2*i+1] += y_weight
                    coeff[2*j+1] -= y_weight
                name = 'four_center_matching_' + '_'.join(map(str, quad)) + '_' + str(choice) + '_' + ''.join(map(str, codes))
                expected.append((tuple((k, c) for k, c in enumerate(coeff) if c), constant, name))
            actual = FC.matching_linear_rows(quad, choice, differences, gg)
            assert actual == expected, (quad, choice, label)
            matching_counts[label] += len(actual)
        coeff = {}
        for i in quad:
            for axis in (0, 1):
                k = 2*i+axis
                coeff[independent_monomial(k, k)] = Q(-1)
        for i, j in pairs:
            for axis in (0, 1):
                coeff[independent_monomial(2*i+axis, 2*j+axis)] = Q(2)
        expected = (tuple(sorted(coeff.items())), Q(-4),
                    'four_center_matching_moment_' + '_'.join(map(str, quad)) + '_' + str(choice))
        assert FC.matching_moment_row(L, quad, choice) == expected
        matching_counts['Quadratic matching rows with independent monomial indexing'] += 1
audit.extend({'kind': name, 'rows_checked': count, 'status': 'PASS_EXACT_COEFFICIENT_IDENTITY'}
             for name, count in matching_counts.items())

report = {
    'status': 'PASS_INDEPENDENT_EXACT_ROW_RECONSTRUCTION',
    'scope': 'Four-center row expansions only; physical premises and whole-parent guard proofs remain caller obligations',
    'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in (GENERATOR, STATE, Path(__file__)) + ((LIFT,) if LIFT else ())},
    'cases': audit,
    'total_rows_checked': sum(r['rows_checked'] for r in audit),
    'new_original_cell_closures': 0,
}
args.output.write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
