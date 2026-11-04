#!/usr/bin/env python3
"""Check the n=11 rational upper-bound witness with Python integer arithmetic.

This checks one packing. It is neither an optimizer, an exhaustive search, nor
an optimality/equality proof. Run: python check_rational_witness.py [json_path]
"""
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json
import sys


def require(condition, description):
    if not condition:
        raise ValueError(description)


def dot(left, right):
    return sum(x * y for x, y in zip(left, right))


def check(path):
    data = json.loads(path.read_text())
    require(data['schema'] == 'eleven-rational-witness-v1', 'unknown schema')
    squares = data['squares']
    require([s['label'] for s in squares] == list(range(11)), 'eleven ordered labels required')
    coordinate_denominator = data['coordinate_denominator']
    half_angle_denominator = data['half_angle_denominator']
    require(coordinate_denominator > 0 and half_angle_denominator > 0, 'positive denominators required')
    q = Fraction(data['q_num'], data['q_den'])
    require(q == Fraction(49013, 10000), 'unexpected stated bound')
    centers = []
    frames = []
    for square in squares:
        centers.append(tuple(Fraction(square[k], coordinate_denominator) for k in ['x_num', 'y_num']))
        t = Fraction(square['half_angle_num'], half_angle_denominator)
        cosine, sine = (1 - t*t) / (1 + t*t), 2*t / (1 + t*t)
        u, v = (cosine, sine), (-sine, cosine)
        require(dot(u, u) == dot(v, v) == 1 and dot(u, v) == 0, 'invalid frame')
        frames.append((u, v))
    disk_margin = Fraction(data['claimed_vertex_slack_num'], data['claimed_vertex_slack_den'])
    require(disk_margin >= Fraction(1, 20000), 'insufficient advertised disk margin')
    for i, center in enumerate(centers):
        u, v = frames[i]
        for a, b in product([-1, 1], repeat=2):
            vertex = tuple(center[k] + (a*u[k] + b*v[k]) / 2 for k in range(2))
            require(dot(vertex, vertex) + disk_margin <= q, f'vertex containment failed: {i}, {a}, {b}')
    expected_pairs = set(combinations(range(11), 2))
    separators = data['separators']
    require(len(separators) == 55, '55 separator witnesses required')
    require({(s['i'], s['j']) for s in separators} == expected_pairs, 'pair cover mismatch')
    separation_margin = Fraction(data['claimed_pair_slack_num'], data['claimed_pair_slack_den'])
    require(separation_margin >= Fraction(1, 2000000), 'insufficient advertised separation margin')
    for separator in separators:
        i, j, owner, axis, sign = (separator[k] for k in ['i', 'j', 'owner', 'axis', 'sign'])
        require(owner in [i, j] and axis in ['u', 'v'] and sign in [-1, 1], 'invalid owner witness')
        direction = tuple(sign*x for x in frames[owner][0 if axis == 'u' else 1])
        displacement = tuple(centers[j][k] - centers[i][k] for k in range(2))
        support = sum(abs(dot(direction, vector)) for square in [i, j] for vector in frames[square]) / 2
        require(dot(direction, displacement) >= support + separation_margin, f'separation failed: {i}, {j}')
    print('PASS: 11 orthonormal frames; 44 vertex bounds; 55 distinct pair separators.')
    print('Certified q upper bound: 49013/10000; disk slack >= 1/20000; pair slack >= 1/2000000.')
    print('Scope: one feasible packing only; no global optimality or equality claim.')


if __name__ == '__main__':
    check(Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name('RATIONAL_WITNESS.json'))
