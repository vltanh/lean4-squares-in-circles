#!/usr/bin/env python3
"""Independent exact Fraction replay of the own-half upper-side forest.

This file imports no producer or producer arithmetic. The three rational
root intervals, all eight signed-frame families, every midpoint, and all
eight horizontal vertices are independently reconstructed. Printed leaf
bounds are ignored. Only strictly negative outward bounds are accepted.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import isqrt
from pathlib import Path
import hashlib
import json
import sys
import time

BITS = 90
DEN = 1 << BITS
ROOT = ((F(1, 2), F(13, 20)), (F(0), F(1)), (F(0), F(1)))
SIGNS = tuple(product((-1, 1), repeat=3))
DELTA = F(331, 20000)
EPS = F(1, 20)


class Interval:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        if isinstance(lo, Interval):
            assert hi is None
            self.lo, self.hi = lo.lo, lo.hi
        else:
            self.lo = F(lo)
            self.hi = F(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __add__(self, other):
        other = Interval(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __sub__(self, other):
        return self + -Interval(other)

    def __rsub__(self, other):
        return Interval(other) + -self

    def __mul__(self, other):
        other = Interval(other)
        vals = (self.lo * other.lo, self.lo * other.hi,
                self.hi * other.lo, self.hi * other.hi)
        return Interval(min(vals), max(vals))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Interval(other)
        assert other.lo > 0 or other.hi < 0
        vals = (self.lo / other.lo, self.lo / other.hi,
                self.hi / other.lo, self.hi / other.hi)
        return Interval(min(vals), max(vals))

    def __rtruediv__(self, other):
        return Interval(other) / self

    def square(self):
        lo = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        return Interval(lo, max(self.lo**2, self.hi**2))

    def absolute(self):
        lo = 0 if self.lo <= 0 <= self.hi else min(abs(self.lo), abs(self.hi))
        return Interval(lo, max(abs(self.lo), abs(self.hi)))

    def sqrt(self):
        assert self.lo >= 0
        low = isqrt(self.lo.numerator * DEN**2 // self.lo.denominator)
        high = isqrt(self.hi.numerator * DEN**2 // self.hi.denominator)
        if F(high**2, DEN**2) < self.hi:
            high += 1
        ans = Interval(F(low, DEN), F(high, DEN))
        assert ans.lo**2 <= self.lo and ans.hi**2 >= self.hi
        return ans


def minimum(vals):
    vals = tuple(vals)
    return Interval(min(v.lo for v in vals), min(v.hi for v in vals))


def maximum(vals):
    vals = tuple(vals)
    return Interval(max(v.lo for v in vals), max(v.hi for v in vals))


@lru_cache(maxsize=None)
def main_frame(pair):
    # a(h) decreases, b(h) increases on [1/2,13/20].
    ends = []
    for end in pair:
        h = Interval(end)
        k = (F(1, 2) - h.square()).sqrt()
        ends.append((h + k, h - k))
    return (Interval(ends[1][0].lo, ends[0][0].hi),
            Interval(ends[0][1].lo, ends[1][1].hi))


@lru_cache(maxsize=None)
def slope_frame(pair):
    # On [0,1], a decreases while b and the coordinate halfwidth increase.
    ends = []
    for end in pair:
        t = Interval(end)
        norm = (1 + t.square()).sqrt()
        ends.append((1 / norm, t / norm, (1 + t) / (2 * norm)))
    return (Interval(ends[1][0].lo, ends[0][0].hi),
            Interval(ends[0][1].lo, ends[1][1].hi),
            Interval(ends[0][2].lo, ends[1][2].hi))


@lru_cache(maxsize=None)
def main_height_lower(pair):
    # Y(h)=32h/9+41/(36h)-32/9-199/120, minimized at sqrt(41/128).
    lo, hi = pair
    if hi**2 <= F(41, 128):
        return F(32, 9) * hi + F(41, 36) / hi - F(32, 9) - F(199, 120)
    if lo**2 >= F(41, 128):
        return F(32, 9) * lo + F(41, 36) / lo - F(32, 9) - F(199, 120)
    return (4 * Interval(82).sqrt() / 9 - F(32, 9) - F(199, 120)).lo


def support(first, second, sf, ss):
    a, b = first
    c, d = second
    dot = a * c + sf * ss * b * d
    det = ss * a * d - sf * b * c
    return maximum((Interval(1), (1 + dot.absolute() + det.absolute()) / 2))


def upward_clearance(dx, first, second, sf, ss, sigma):
    axes = []
    for (a, b), sign in ((first, sf), (second, ss)):
        axes.append((sign * a, b))
        axes.append((-sign * b, a))
    return minimum((sigma - nx * dx) / maximum((ny, Interval(EPS)))
                   for nx, ny in axes)


def scalar_upper(box, signs):
    h = Interval(*box[0])
    g = 1 / (4 * h)
    fm = main_frame(box[0])
    ap, bp, hp = slope_frame(box[1])
    ass, bs, _ = slope_frame(box[2])
    fp, fs = (ap, bp), (ass, bs)
    sm, sp, ss = signs
    sig_ms = support(fm, fs, sm, ss)
    sig_sp = support(fs, fp, ss, sp)
    xm = (g - DELTA, 1 + DELTA - h)
    xp = (Interval(0), Interval(F(1129, 3000)))
    xs = (Interval(F(29, 60)), Interval(F(147, 250)))
    # Enumerate the eight original coordinate vertices directly. Local
    # caching avoids repeating the same pair arithmetic in several vertices;
    # no producer's grouping of minima or printed upper bound is used.
    first_edges, second_edges, totals = {}, {}, []
    for im, ip, iss in product((0, 1), repeat=3):
        if (im, iss) not in first_edges:
            first_edges[im, iss] = upward_clearance(
                xs[iss] - xm[im], fm, fs, sm, ss, sig_ms)
        if (iss, ip) not in second_edges:
            second_edges[iss, ip] = upward_clearance(
                xp[ip] - xs[iss], fs, fp, ss, sp, sig_sp)
        totals.append(first_edges[im, iss] + second_edges[iss, ip])
    return hp.hi + F(1, 10) - main_height_lower(box[0]) - minimum(totals).lo


def exact_int(value):
    return type(value) is int


def verify(data, progress=False):
    assert data['schema'] == 'ownhalf_above_side_v1'
    assert data['status'] == 'COMPLETE_PENDING_INDEPENDENT_REPLAY'
    assert data['root'] == [[str(lo), str(hi)] for lo, hi in ROOT]
    assert exact_int(data['remaining']) and data['remaining'] == 0 and data['pending'] == []
    roots = data['roots']
    assert type(roots) is list and len(roots) == 8
    assert all(set(root) == {'index', 'signs'} for root in roots)
    assert all(type(root['signs']) is list and len(root['signs']) == 3
               and all(exact_int(v) and v in (-1, 1) for v in root['signs'])
               for root in roots)
    assert {tuple(root['signs']) for root in roots} == set(SIGNS)
    assert all(exact_int(root['index']) for root in roots)
    assert len({root['index'] for root in roots}) == 8
    nodes = data['nodes']
    assert type(nodes) is list and len(nodes) >= 8
    assert exact_int(data['processed']) and data['processed'] == len(nodes)
    assert exact_int(data['leaves']) and len(nodes) == 2 * data['leaves'] - 8
    assert exact_int(data['maximum_depth']) and 0 <= data['maximum_depth'] <= 60
    seen, counts = set(), []
    leaves = maximum_depth = 0
    largest = None
    last = time.monotonic()

    def visit(index, box, signs, depth):
        nonlocal leaves, maximum_depth, largest, last
        assert exact_int(index) and 0 <= index < len(nodes) and index not in seen
        assert depth <= 60
        seen.add(index)
        maximum_depth = max(maximum_depth, depth)
        node = nodes[index]
        assert type(node) is dict
        if 'rule' in node:
            assert set(node) == {'rule', 'upper'}
            assert exact_int(node['rule']) and node['rule'] == 0
            # The printed upper bound is deliberately not a proof premise.
            assert type(node['upper']) is str
            upper = scalar_upper(box, signs)
            assert upper < 0, ('failed strict leaf', index, box, signs, upper)
            leaves += 1
            largest = upper if largest is None else max(largest, upper)
            if progress and time.monotonic() - last > 20:
                print('independent exact own-half replay:', leaves, 'leaves',
                      'root signs', signs, flush=True)
                last = time.monotonic()
            return
        assert set(node) == {'axis', 'children'}
        axis, children = node['axis'], node['children']
        assert exact_int(axis) and 0 <= axis < 3
        assert type(children) is list and len(children) == 2
        lo, hi = box[axis]
        mid = (lo + hi) / 2
        left, right = list(box), list(box)
        left[axis], right[axis] = (lo, mid), (mid, hi)
        visit(children[0], tuple(left), signs, depth + 1)
        visit(children[1], tuple(right), signs, depth + 1)

    for root in roots:
        before = leaves
        visit(root['index'], ROOT, tuple(root['signs']), 0)
        counts.append(leaves - before)
    assert len(seen) == len(nodes) == 2 * leaves - 8
    assert exact_int(data['processed']) and data['processed'] == len(nodes)
    assert exact_int(data['leaves']) and data['leaves'] == leaves
    assert exact_int(data['maximum_depth']) and data['maximum_depth'] == maximum_depth
    return {'result': 'PASS', 'complete': True, 'nodes': len(nodes),
            'strict_leaves': leaves, 'roots': 8, 'leaves_per_root': counts,
            'maximum_depth': maximum_depth,
            'largest_replayed_upper': str(largest),
            'arithmetic': 'standalone Fraction intervals with 90-bit outward radicals',
            'physical_evaluation': 'all eight signed families and eight explicit horizontal vertices',
            'producer_imports': False}


def main():
    start = time.monotonic()
    path = (Path(sys.argv[1]) if len(sys.argv) > 1
            else Path(__file__).with_name('ownhalf_above_side_cover.json'))
    raw = path.read_bytes()
    data = json.loads(raw)
    report = verify(data, progress=True)
    report.update(certificate_file=path.name,
                  certificate_sha256=hashlib.sha256(raw).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  seconds=time.monotonic() - start)
    output = path.with_name(path.stem + '_independent_replay.json')
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
