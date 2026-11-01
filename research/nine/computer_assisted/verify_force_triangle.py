#!/usr/bin/env python3
"""Exact rational interval proof for an unloaded three-port triangle.

This module proves a *conditional force-screening theorem*, not a global
nine-square packing theorem. Its root box covers every configuration of
three nonzero planar vectors x,y,z with |x|+|y|+|z|=1 and
min(|x|,|y|,|z|)>=1/12, up to permutation, rotation, and reflection.

For every box, rational interval arithmetic upper-bounds
    |x-y|+|y-z|+|z-x| <= 60/31.

NO numerical floating point, external libraries, interval sampling,
Lean, or CI are used. The splitting strategy is not part of the trusted
mathematical kernel: any splitting is legal, provided every generated
leaf passes the exact upper-bound check.
"""
from collections import Counter
from fractions import Fraction as F
from math import isqrt

MIN = F(1, 12)
CUT = F(60, 31)
SQRT_DEN = 1 << 15
MAX_DEPTH = 48


def unit_chart(tlo, thi, sign):
    """Exact component intervals for sign*(1-t²,2t)/(1+t²), -1<=t<=1.

    The x-coordinate decreases with |t|; the y-coordinate increases
    with t on [-1,1]. Reflections and the opposite semicircle give
    complete directional coverage without transcendental constants.
    """
    assert -1 <= tlo <= thi <= 1 and sign in (-1, 1)
    amin = F(0) if tlo <= 0 <= thi else min(abs(tlo), abs(thi))
    amax = max(abs(tlo), abs(thi))
    def cosf(t):
        return (1 - t*t) / (1 + t*t)
    def sinf(t):
        return 2*t / (1 + t*t)
    xlo, xhi = cosf(amax), cosf(amin)
    ylo, yhi = sinf(tlo), sinf(thi)
    return ((xlo, xhi), (ylo, yhi)) if sign == 1 else ((-xhi, -xlo), (-yhi, -ylo))


def mul_positive(al, ah, bl, bh):
    """Positive scalar interval [al,ah] times arbitrary [bl,bh]."""
    assert 0 <= al <= ah and bl <= bh
    xs = (al*bl, al*bh, ah*bl, ah*bh)
    return min(xs), max(xs)


def difference(a, b):
    return a[0]-b[1], a[1]-b[0]


def sqrt_upper(q):
    """Return a proved rational upper bound of sqrt(q), using isqrt."""
    assert q >= 0
    n = (q.numerator * SQRT_DEN**2 + q.denominator - 1) // q.denominator
    r = isqrt(n)
    if r*r < n:
        r += 1
    # Exact integer inequalities: r^2>=n>=SQRT_DEN^2*q.
    assert F(r*r, SQRT_DEN**2) >= q
    return F(r, SQRT_DEN)


def distance_upper(v, w):
    dx = difference(v[0], w[0])
    dy = difference(v[1], w[1])
    ux = max(abs(dx[0]), abs(dx[1]))
    uy = max(abs(dy[0]), abs(dy[1]))
    return sqrt_upper(ux*ux + uy*uy)


def bound(box, sy, sz):
    """Verified upper bound on the force-triangle perimeter in a box.

    x has direction (1,0), and vectors y,z use rational unit charts.
    The magnitudes a,b,c satisfy a>=b>=c>=1/12 and a+b+c=1.
    Returns None if no valid normalized magnitudes can occur.
    """
    (al, ah), (bl, bh), (yl, yh), (zl, zh) = box
    cl = max(MIN, F(1)-ah-bh)
    ch = min(F(1)-al-bl, bh)
    if (cl > ch or ah < bl or ah + 2*bh < 1):
        return None
    x = ((al, ah), (F(0), F(0)))
    ux, uy = unit_chart(yl, yh, sy)
    vx, vy = unit_chart(zl, zh, sz)
    y = (mul_positive(bl, bh, *ux), mul_positive(bl, bh, *uy))
    z = (mul_positive(cl, ch, *vx), mul_positive(cl, ch, *vy))
    return distance_upper(x, y) + distance_upper(y, z) + distance_upper(z, x)


def divide(box, axis):
    lo, hi = box[axis]
    mid = (lo+hi)/2
    left, right = list(box), list(box)
    left[axis], right[axis] = (lo, mid), (mid, hi)
    return tuple(left), tuple(right)


def chart_root(sy):
    # a=max length, b=second, c=1-a-b=min length; thus
    # a in [1/3,1-2MIN] and b in [MIN,1/2].
    yrange = (F(0), F(1)) if sy == 1 else (F(-1), F(0))
    return ((F(1,3), 1-2*MIN), (MIN, F(1,2)), yrange, (F(-1), F(1)))


def prove_chart(sy, sz):
    assert sy in (-1,1) and sz in (-1,1)
    root = chart_root(sy)
    stack = [(root,0)]
    record = Counter()
    best_gap = None
    while stack:
        box, depth = stack.pop()
        record['nodes'] += 1
        record['max_depth'] = max(record['max_depth'], depth)
        upper = bound(box, sy, sz)
        if upper is None:
            record['empty'] += 1
            continue
        if upper <= CUT:
            record['proved_leaves'] += 1
            gap = CUT - upper
            if best_gap is None or gap < best_gap:
                best_gap = gap
            continue
        if depth >= MAX_DEPTH:
            raise AssertionError(f'Unproved box at depth {depth}: {box}; upper {upper}')
        # This rational heuristic only controls performance, never validity.
        strengths = [F(3), F(3), F(3,2), F(3,2)]
        widths = [strengths[i]*(box[i][1]-box[i][0]) for i in range(4)]
        axis = max(range(4), key=lambda j: widths[j])
        if not widths[axis]:
            raise AssertionError(f'Unproved zero-width box: {box}')
        left,right = divide(box, axis)
        record['split_'+str(axis)] += 1
        stack.extend([(right,depth+1),(left,depth+1)])
    record['min_gap_num'] = best_gap.numerator if best_gap is not None else -1
    record['min_gap_den'] = best_gap.denominator if best_gap is not None else 1
    return record


def main():
    total=Counter()
    print('Exact force-triangle interval proof; MIN=1/12, threshold=60/31')
    print('sy sz | nodes | bound-certified leaves | empty leaves | max depth | min rational margin')
    for sy in (1,-1):
        for sz in (-1,1):
            stats=prove_chart(sy,sz)
            gap=F(stats['min_gap_num'],stats['min_gap_den']) if stats['min_gap_num']>=0 else None
            assert gap is None or gap>=0
            print(f'{sy:+d} {sz:+d} | {stats["nodes"]} | {stats["proved_leaves"]} | '
                  f'{stats["empty"]} | {stats["max_depth"]} | {gap}')
            total.update({key:stats[key] for key in ('nodes','proved_leaves','empty')})
    print(f'ALL CHARTS CERTIFIED: nodes={total["nodes"]}; '
          f'proved leaves={total["proved_leaves"]}; empty leaves={total["empty"]}.')


if __name__ == '__main__':
    main()
