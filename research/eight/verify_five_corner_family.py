#!/usr/bin/env python3
"""Full-domain certificate for the five-corner family, NOT all eight packings.

Run after placing verify_candidate_stationary.py in the same directory.
Only Python's standard library is used. Every accepted cell uses exact,
outward-rounded interval arithmetic; budget exhaustion means NO proof.
See FIVE_CORNER_OPTIMALITY.md for the mathematical coverage argument.
"""
from fractions import Fraction as Q
import time
from verify_candidate_stationary import Interval as I, jet, ROOTBOX, verify_root

QB = ROOTBOX[0]
CORE = ((Q('-1.1'), Q('-.8')), (Q(0), Q('.15')))


class EmptyDomain(Exception):
    pass


def feasible_sqrt(value):
    if value.hi < 0:
        raise EmptyDomain
    # A partially negative interval is not discarded. Its nonnegative part
    # encloses every real square root of a feasible point in this cell.
    return value.sqrt(clip=True)


def value(box):
    q = I(*QB)
    y, z = (I(*bounds) for bounds in box)
    x1 = feasible_sqrt(q-y*y)
    x2 = feasible_sqrt(q-(y+2)**2)
    y3 = feasible_sqrt(q-(x2-3)**2)
    y4 = y3-2
    x4 = -feasible_sqrt(q-y4*y4)
    c, s = (1-z*z)/(1+z*z), 2*z/(1+z*z)
    h1, h2 = c*x1+s*y-2-c, -s*x4+c*y4-1-s
    return h1**2+h2**2-q


def split(box):
    axis = max(range(2), key=lambda k: box[k][1]-box[k][0])
    lo, hi = box[axis]
    middle = (lo+hi)/2
    left, right = list(box), list(box)
    left[axis], right[axis] = (lo, middle), (middle, hi)
    return tuple(left), tuple(right)


def in_core(box):
    return all(CORE[j][0] <= box[j][0] and box[j][1] <= CORE[j][1]
               for j in range(2))


def verify_convexity(max_nodes=1000000):
    pending = [CORE]
    nodes = positive = 0
    start = time.monotonic()
    while pending:
        box = pending.pop()
        nodes += 1
        if nodes > max_nodes:
            raise RuntimeError('Convexity budget exhausted: NO certificate')
        f = jet([QB, *box])
        a = f.h[1][1].lower()
        b = max(f.h[1][2].absmax(), f.h[2][1].absmax())
        d = f.h[2][2].lower()
        if a > 0 and d > 0 and a*d-b*b > 0:
            positive += 1
        else:
            pending.extend(split(box))
    if nodes != 2*positive-1:
        raise AssertionError('Convexity partition accounting failed')
    print('CONVEXITY:', nodes, 'nodes;', positive, 'positive Hessian leaves.')
    print('Seconds:', round(time.monotonic()-start, 3))


def verify_domain(max_nodes=1000000):
    # Split at core endpoints so every cell may enter CORE exactly.
    ys = [Q(-2), CORE[0][0], CORE[0][1], Q(0)]
    zs = [Q(0), CORE[1][1], Q(5, 12)]
    initial = [((ys[i], ys[i+1]), (zs[j], zs[j+1]))
               for i in range(3) for j in range(2)]
    pending = initial[:]
    nodes = empty = positive = covered = 0
    start = time.monotonic()
    while pending:
        box = pending.pop()
        nodes += 1
        if nodes > max_nodes:
            raise RuntimeError('Domain budget exhausted: NO certificate')
        if in_core(box):
            covered += 1
            continue
        try:
            f = value(box)
        except EmptyDomain:
            empty += 1
            continue
        if f.lo > 0:
            positive += 1
            continue
        # Mean-value bound at fixed q. The derivative enclosure contains
        # every segment from the cell center to a point of the cell.
        try:
            fb = jet([QB, *box])
            middle = [(lo+hi)/2 for lo, hi in box]
            radius = [(hi-lo)/2 for lo, hi in box]
            fm = value([(x, x) for x in middle])
            lower = fm.lower()-sum(fb.g[i+1].absmax()*radius[i] for i in range(2))
            if lower > 0:
                positive += 1
                continue
        except (ValueError, EmptyDomain):
            pass  # Derivatives unavailable: subdivide, never accept.
        if max(hi-lo for lo, hi in box) < Q(1, 10**10):
            raise RuntimeError(('Unresolved tiny cell: NO certificate', box))
        pending.extend(split(box))
    if nodes != 2*(empty+positive+covered)-len(initial):
        raise AssertionError('Domain partition accounting failed')
    print('DOMAIN:', nodes, 'nodes;', empty, 'empty;', positive,
          'strictly positive;', covered, 'covered by convex core.')
    print('Seconds:', round(time.monotonic()-start, 3))


def verify():
    verify_root()
    if not (0 < QB[0] < QB[1] < 4 and in_core(ROOTBOX[1:])):
        raise AssertionError('Root/core geometry not established')
    verify_convexity()
    verify_domain()
    print('VERIFIED: F(q*,y,z)>=0 on every feasible radical domain')
    print('in [-2,0] x [0,5/12], with its only zero at the isolated candidate.')
    print('Thus the five-corner chain has minimum radius sqrt(q*).')
    print('This does NOT force that chain in arbitrary eight-square packings.')


if __name__ == '__main__':
    verify()
