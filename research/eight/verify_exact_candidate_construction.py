#!/usr/bin/env python3
"""Check all non-contact inequalities at the rigorously isolated candidate.

The ten contact identities and five boundary identities are proved in
FIVE_CORNER_REDUCTION.md; those equalities are not replaced by interval tests.
Every other corner/pair is checked uniformly over the entire root box.
This proves a construction, NOT an unrestricted lower bound.
"""
from itertools import product, combinations
from fractions import Fraction as Q
from verify_candidate_stationary import Interval as I, ROOTBOX, verify_root


def dot(a, b):
    return a[0]*b[0]+a[1]*b[1]


def perpendicular(a):
    return -a[1], a[0]


def absolute(a):
    if a.lo >= 0:
        return a
    if a.hi <= 0:
        return -a
    return I.raw(0, max(-a.lo, a.hi))


def geometry():
    q, y, z = (I(*b) for b in ROOTBOX)
    x1 = (q-y*y).sqrt()
    x2 = (q-(y+2)**2).sqrt()
    x3 = x2-3
    y3 = (q-x3*x3).sqrt()
    y4 = y3-2
    x4 = -(q-y4*y4).sqrt()
    c, s = (1-z*z)/(1+z*z), 2*z/(1+z*z)
    h1, h2 = c*x1+s*y-2-c, -s*x4+c*y4-1-s
    p5 = (h1*c-h2*s, h1*s+h2*c)
    centers = [
        (x1-Q(1, 2), y+Q(1, 2)),
        (x2-Q(1, 2), y+Q(3, 2)),
        (x2-Q(3, 2), I(Q(7, 20))),
        (x2-Q(3, 2), I(Q(27, 20))),
        (x3+Q(1, 2), y3-Q(1, 2)),
        (x4+Q(1, 2), y4+Q(1, 2)),
        (p5[0]+Q(3, 2)*c-Q(1, 2)*s, p5[1]+Q(3, 2)*s+Q(1, 2)*c),
        (p5[0]+(c-s)/2, p5[1]+(s+c)/2)]
    return q, centers, [(I(1), I(0))]*6+[(c, s)]*2


# Indices use the order A,B,C,T,D,E,G,H.
BOUNDARY = {(0, 1, -1), (1, 1, 1), (4, -1, 1), (5, -1, -1), (7, -1, -1)}
CONTACTS = {(0, 1), (0, 6), (1, 2), (1, 3), (2, 3),
            (2, 4), (3, 4), (4, 5), (5, 7), (6, 7)}


def verify():
    verify_root()
    q, centers, axes = geometry()
    corners, pairs = [], []
    for i, (center, e) in enumerate(zip(centers, axes)):
        f = perpendicular(e)
        for a, b in product((-1, 1), repeat=2):
            if (i, a, b) in BOUNDARY:
                continue
            p = tuple(center[k]+(a*e[k]+b*f[k])/2 for k in range(2))
            slack = q-dot(p, p)
            if slack.lo <= 0:
                raise AssertionError(('Non-contact vertex failed', i, a, b))
            corners.append(slack.lower())
    for i, j in combinations(range(8), 2):
        if (i, j) in CONTACTS:
            continue
        ei, ej = axes[i], axes[j]
        fi, fj = perpendicular(ei), perpendicular(ej)
        delta = tuple(centers[j][k]-centers[i][k] for k in range(2))
        slacks = []
        for n in (ei, fi, ej, fj):
            widths = sum((absolute(dot(n, e)) for e in (ei, fi, ej, fj)), I(0))/2
            slacks.append((absolute(dot(n, delta))-widths).lower())
        slack = max(slacks)
        if slack <= 0:
            raise AssertionError(('Non-contact pair failed', i, j))
        pairs.append(slack)
    if len(corners) != 27 or len(pairs) != 18:
        raise AssertionError('Incomplete construction coverage')
    if min(corners) <= Q(1, 1000) or min(pairs) <= Q(1, 100):
        raise AssertionError('Reported coarse reserve not established')
    print('VERIFIED: all 27 non-contact vertices and all 18 non-contact pairs.')
    print('Vertex squared-radius slack > 1/1000; pair projection slack > 1/100.')
    print('The 5 boundary identities and 10 contact identities follow algebraically')
    print('from the definitions and F=0, as proved in FIVE_CORNER_REDUCTION.md.')
    print('Thus this is an exact candidate packing, not merely decimal coordinates.')


if __name__ == '__main__':
    verify()
