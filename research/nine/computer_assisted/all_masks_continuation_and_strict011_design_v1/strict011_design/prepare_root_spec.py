#!/usr/bin/env python3
"""Prepare reviewable full strict-011 metadata; never installs an adapter."""
import argparse
import json
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

EDGES = ((0, 1, 0), (1, 2, 1), (2, 3, 1), (4, 5, 0), (5, 6, 0))

def root_spec():
    positions = [[F(-2), F(2)] for _ in range(18)]
    scalar = ([[F(7, 10), F(1)] for _ in range(9)]
              + [[F(-3, 4), F(3, 4)] for _ in range(9)]
              + [[F(0), F(3, 4)] for _ in range(9)]
              + [[F(1, 3), F(1, 2)] for _ in range(9)])
    rows = []

    def row(name, terms, rhs=F(0), source_relation='<='):
        coefficients = {}
        for index, value in terms:
            coefficients[index] = coefficients.get(index, F(0)) + F(value)
        rows.append(dict(name=name,
            coefficients=[[k, str(v)] for k, v in sorted(coefficients.items()) if v],
            rhs=str(F(rhs)), source_relation=source_relation,
            necessary_affine_relaxation_relation='<='))

    for k, (lo, hi) in enumerate(positions + scalar):
        row(f'prepared_strict011_bound_upper_{k}', [(k, 1)], hi)
        row(f'prepared_strict011_bound_lower_{k}', [(k, -1)], -lo)
    for i in range(9):
        alpha, beta, absolute = 18+i, 27+i, 36+i
        row(f'prepared_strict011_fold_{i}', [(absolute, 1), (alpha, -1)])
        row(f'prepared_strict011_abs_pos_{i}', [(beta, 1), (absolute, -1)])
        row(f'prepared_strict011_abs_neg_{i}', [(beta, -1), (absolute, -1)])
        row(f'prepared_strict011_width_floor_{i}', [(alpha, -1), (absolute, -1)], -1)
    for i, j, bit in EDGES:
        for sign in (-1, 1):
            row(f'prepared_strict011_cone_{i}_{j}_{sign}',
                [(2*i, 1), (2*j, -1), (2*j+1, sign), (2*i+1, -sign)])
        coefficients = [(2*i, F(1)), (2*j, F(-1))]
        coefficients += [(18+i, F(1, 2)), (36+i, F(1, 2)),
                         (18+j, F(1, 2)), (36+j, F(1, 2))]
        if bit:
            coefficients = [(k, -v) for k, v in coefficients]
        row(f'prepared_strict011_mask_{i}_{j}_{bit}', coefficients,
            source_relation='<' if bit else '<=')
    pairs = list(combinations(range(9), 2))
    return {
        'schema': 'prepared_full_strict_01100_root_spec_v1',
        'status': 'PREPARED_FOR_INDEPENDENT_CONTROLS_AND_PHYSICAL_REVIEW',
        'accepted_geometry_adapter': False,
        'proof_credit': 0,
        'mask': '011/00', 'radius_mode': 'strict', 'target_q': '1105/256',
        'physical_originals': list(range(9)),
        'original_corners': [[i, e, t] for i in range(9) for e, t in product((-1, 1), repeat=2)],
        'original_pairs': [list(p) for p in pairs],
        'owned_pair_cover': [dict(pair=list(p), alternatives=[list(c)
            for c in product(p, (0, 1), (-1, 1))]) for p in pairs],
        'exact_mask_edges': [dict(pair=[i,j], bit=bit,
            cone='xj-xi >= abs(yj-yi)',
            bit_relation='xj-xi < hi+hj' if bit else 'xj-xi >= hi+hj')
            for i,j,bit in EDGES],
        'exact_frame_relations': [
            'u=(alpha,beta), v=(-beta,alpha)',
            'alpha^2+beta^2=1', 'alpha>=abs(beta)', 'z=abs(beta)',
            'h=(alpha+z)/2', 'g=1/(2*(alpha+z))'],
        'corner_relation': 'Every original corner norm_squared < 1105/256',
        'pair_relation': 'Every original pair has disjoint open interiors; physical contact allowed',
        'initial': {
            'id': 'prepared-full-strict-01100-root-v1', 'path': [],
            'angles': [['-1','1'] for _ in range(9)],
            'positions': [[str(x) for x in ab] for ab in positions],
            'scalar': [[str(x) for x in ab] for ab in scalar],
            'choices': [], 'differences': [], 'diagonal': [],
        },
        'absolute_original_variable_bounds': [str(max(abs(a), abs(b))) for a,b in positions+scalar],
        'elementary_necessary_affine_rows': rows,
        'row_count': len(rows),
        'solver_called': False,
        'old_001_ancestry_imported': False,
        'strict_predicate_may_not_be_replaced_by_closed_relaxation': True,
    }

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    answer = root_spec()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as stream:
        json.dump(answer, stream, indent=2)
        stream.write('\n')
    print(json.dumps({'status': answer['status'], 'elementary_rows': answer['row_count'],
                      'accepted_geometry_adapter': False, 'solver_called': False}))

if __name__ == '__main__':
    main()
