#!/usr/bin/env python3
"""Exact three-parameter family at the isolated n=8 candidate radius.

This is an upper-bound construction, not a global optimality proof.
All acceptance arithmetic is outward-rounded integer interval arithmetic.
The root is independently isolated by verify_candidate_stationary.py.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from verify_candidate_stationary import Interval as I, ROOTBOX, verify_root


def dot(a, b):
    return a[0]*b[0]+a[1]*b[1]


def absolute(a):
    if a.lo >= 0:
        return a
    if a.hi <= 0:
        return -a
    return I.raw(0, max(-a.lo, a.hi))


def perp(a):
    return -a[1], a[0]


def family():
    q, y, z = (I(*bounds) for bounds in ROOTBOX)
    x1 = (q-y*y).sqrt()
    x2 = (q-(y+2)**2).sqrt()
    x3 = x2-3
    y3 = (q-x3*x3).sqrt()
    y4 = y3-2
    w = (q-y4*y4).sqrt()
    c, s = (1-z*z)/(1+z*z), 2*z/(1+z*z)
    h1, h2 = c*x1+s*y-2-c, s*w+c*y4-1-s
    p5 = h1*c-h2*s, h1*s+h2*c
    central_height = I(Q(1, 3), Q(7, 20))
    top_height = I(Q(27, 20), Q(34, 25))
    slide = I(Q(-1, 10), Q(1, 10))
    # Order A,B,C,T,D,E,G,H.
    centers = [
        (x1-Q(1, 2), y+Q(1, 2)),
        (x2-Q(1, 2), y+Q(3, 2)),
        (x2-Q(3, 2), central_height),
        (x2-Q(3, 2), top_height),
        (x3+Q(1, 2), y3-Q(1, 2)),
        (-w+Q(1, 2), y4+Q(1, 2)),
        (p5[0]+Q(3, 2)*c-Q(1, 2)*s-slide*s,
         p5[1]+Q(3, 2)*s+Q(1, 2)*c+slide*c),
        (p5[0]+(c-s)/2, p5[1]+(s+c)/2)]
    return q, centers, [(I(1), I(0))]*6+[(c, s)]*2


BOUNDARY = {(0, 1, -1), (1, 1, 1), (4, -1, 1),
            (5, -1, -1), (7, -1, -1)}
SYMBOLIC = {(0, 1), (0, 6), (1, 2), (1, 3), (2, 3),
            (2, 4), (3, 4), (4, 5), (5, 7), (6, 7)}


def verify():
    verify_root()
    q, centers, axes = family()
    vertex_slacks, pair_slacks = [], []
    for i, (center, e) in enumerate(zip(centers, axes)):
        f = perp(e)
        for a, b in product((-1, 1), repeat=2):
            if (i, a, b) in BOUNDARY:
                continue
            p = tuple(center[k]+(a*e[k]+b*f[k])/2 for k in range(2))
            slack = (q-dot(p, p)).lower()
            if slack <= 0:
                raise AssertionError(('vertex', i, a, b, slack))
            vertex_slacks.append(slack)
    for i, j in combinations(range(8), 2):
        if (i, j) in SYMBOLIC:
            continue
        ei, ej = axes[i], axes[j]
        fi, fj = perp(ei), perp(ej)
        delta = tuple(centers[j][k]-centers[i][k] for k in range(2))
        slacks = []
        for n in (ei, fi, ej, fj):
            width = sum((absolute(dot(n, a)) for a in (ei, fi, ej, fj)), I(0))/2
            slacks.append((absolute(dot(n, delta))-width).lower())
        slack = max(slacks)
        if slack <= 0:
            raise AssertionError(('pair', i, j, slack))
        pair_slacks.append(slack)
    if len(vertex_slacks) != 27 or len(pair_slacks) != 18:
        raise AssertionError('Incomplete coverage')
    if min(vertex_slacks) <= Q(1, 1000) or min(pair_slacks) <= Q(1, 100):
        raise AssertionError('Coarse reported reserve not established')
    if not all(absolute(x).upper() < Q(5, 12) for x in centers[2]):
        raise AssertionError('Central core not retained')
    print('VERIFIED on the complete three-parameter box:')
    print('central height in [1/3,7/20], top height in [27/20,34/25],')
    print('inner tilted-square transverse displacement in [-1/10,1/10].')
    print('27 other vertices have squared containment slack >1/1000;')
    print('18 other pairs have separating projection slack >1/100.')
    print('Five boundary identities and nine persistent contacts are algebraic.')
    print('The tenth listed pair C,T has height separation >=1 by its domain.')
    print('The radius-1/12 central core remains in the open central square.')
    print('This proves a packing family at R*, not global optimality.')


if __name__ == '__main__':
    verify()
