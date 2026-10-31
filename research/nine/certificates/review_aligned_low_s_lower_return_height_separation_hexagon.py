#!/usr/bin/env python3
"""Independent rational replay of every LTAC height-certificate leaf.

This file imports no author interval implementation. It reconstructs the
complete subdivision from a binary trie, computes every box independently,
and uses 96-bit radical endpoints through a different integer formula.
The scalar proof and all rejection guards are audited in the accompanying
full review. No floating-point arithmetic or sampled point is used.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
from math import isqrt
from collections import Counter
import hashlib
import json
import re

BASE = Path(__file__).resolve().parents[1]
SCALE = 1 << 96


@dataclass(frozen=True)
class Interval:
    low: F
    high: F

    def __post_init__(self):
        assert isinstance(self.low, F) and isinstance(self.high, F)
        assert self.low <= self.high

    @classmethod
    def constant(cls, value):
        return cls(F(value), F(value))

    def __add__(self, other):
        return Interval(self.low + other.low, self.high + other.high)

    def __neg__(self):
        return Interval(-self.high, -self.low)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        values = (self.low * other.low, self.low * other.high,
                  self.high * other.low, self.high * other.high)
        return Interval(min(values), max(values))

    def reciprocal(self):
        assert self.low > 0
        return Interval(F(1) / self.high, F(1) / self.low)

    def __truediv__(self, other):
        return self * other.reciprocal()

    def squared(self):
        if self.low >= 0:
            return Interval(self.low ** 2, self.high ** 2)
        if self.high <= 0:
            return Interval(self.high ** 2, self.low ** 2)
        return Interval(F(0), max(self.low ** 2, self.high ** 2))

    def meet(self, other):
        lo, hi = max(self.low, other.low), min(self.high, other.high)
        return None if lo > hi else Interval(lo, hi)

    def sqrt_nonnegative(self):
        assert self.high >= 0

        def bounds(q):
            assert q >= 0
            # floor(sqrt(n*d*S^2)/d) = floor(S*sqrt(n/d)).
            n, d = q.numerator, q.denominator
            k = isqrt(n * d * SCALE * SCALE) // d
            assert k * k * d <= n * SCALE * SCALE
            assert (k + 1) * (k + 1) * d > n * SCALE * SCALE
            exact = k * k * d == n * SCALE * SCALE
            return F(k, SCALE), F(k if exact else k + 1, SCALE)

        return Interval(bounds(max(F(0), self.low))[0],
                        bounds(self.high)[1])


C = Interval.constant
ONE, HALF = C(1), C(F(1, 2))
INITIAL = (Interval(F(14, 15), F(1)),
           Interval(F(29, 50), F(2, 3)),
           Interval(F(2, 25), F(5, 7)))
WIDTHS = tuple(q.high - q.low for q in INITIAL)
FLOOR = F(1, 25000)


def evaluate(box):
    d, h, t = box
    a, g = ONE - d, ONE - h
    b = (ONE - t.squared()).sqrt_nonnegative()
    b = b.meet(Interval(t.low, F(1)))
    if b is None:
        return "unit tilt", None
    radius2 = (d + ONE).squared() + C(F(1, 4))
    Y = g + b + t
    xradicand = radius2 - Y.squared()
    if xradicand.high <= 0:
        return "positive X", None
    X = xradicand.sqrt_nonnegative()
    x = (X - b + t).meet(Interval(max(F(3, 10), t.low), d.high))
    if x is None:
        return "original x", None
    X = X.meet(x + b - t)
    if X is None:
        return "original X identity", None
    screen = (d - x) * t - (h - HALF) * b
    if screen.high < 0:
        return "leaf screen", -screen.high
    w = x + a
    ell = (w.squared() + h.squared()).sqrt_nonnegative()
    if X.low <= 0 or ell.low <= 0:
        return "unresolved denominator", None
    c, s = w / ell, h / ell
    N, K = a * c + h * s, x * s
    wradicand = radius2 - (N + ONE).squared()
    if wradicand.high < 0:
        return "upper radius", None
    W = wradicand.sqrt_nonnegative()
    rho = (W - K).meet(Interval(F(7, 8), F(1)))
    if rho is None:
        return "upper side mean", None
    delta = ONE - rho
    tau = (b * (x * Y / X - g)).meet(Interval(F(0), F(1)))
    if tau is None:
        return "lower side mean", None
    value = tau * b - delta * c
    if value.low > FLOOR:
        return "positive separation", value.low
    return "unresolved target", value.low


def source_pins():
    expected = {
        "ALIGNED_LOW_S_LOWER_RETURN_HEIGHT_SEPARATION.md":
        "93bb8e2d6dc3f2965c1a1868ba4a7552f63c5326cbe05cab5381950f4db765be",
        "certificates/aligned_low_s_lower_return_height_separation.py":
        "bd92d1895f240805a78ea5160b0b7ed56f6948a4ec6ce88ff870bb55a6472f15",
    }
    for name, pin in expected.items():
        assert hashlib.sha256((BASE / name).read_bytes()).hexdigest() == pin
    return expected


def main():
    pins = source_pins()
    author_file = Path('/tmp/aligned_low_s_lower_return_height_separation_certificate.json')
    author = json.loads(author_file.read_text())
    leaves = author['leaves']
    payload = json.dumps(leaves, sort_keys=True, separators=(',', ':')).encode()
    assert hashlib.sha256(payload).hexdigest() == \
        '3e16224eccf7d9f4b93cd98f0b49901d15ac6ff1aa0decfff4620c6e282f9662'
    assert len(leaves) == 1568
    assert author['nodes'] == 3135 and author['max_depth'] == 15
    assert Counter(row['reason'] for row in leaves) == \
        Counter({'leaf screen': 374, 'positive separation': 1194})
    author_minimum = min(F(row['margin']) for row in leaves if row['margin'] is not None)
    assert author_minimum == F(author['smallest_margin']) > FLOOR
    manuscript = (BASE / 'ALIGNED_LOW_S_LOWER_RETURN_HEIGHT_SEPARATION.md').read_text()
    printed = re.search(r'Its smallest positive lower bound is exactly\s+(\d+)\s*/\s*(\d+)', manuscript)
    assert printed is not None
    assert F(int(printed[1]), int(printed[2])) == author_minimum

    # Build a new trie. Prefix leaves, duplicates, and absent siblings fail.
    trie = {}
    for row in leaves:
        path = row['path']
        assert set(path) <= {'0', '1'}
        branch = trie
        for digit in path:
            assert 'leaf' not in branch
            branch = branch.setdefault(digit, {})
        assert not branch
        branch['leaf'] = row

    replay, seen_nodes, deepest = [], 0, 0

    def visit(branch, box, path):
        nonlocal seen_nodes, deepest
        seen_nodes += 1
        deepest = max(deepest, len(path))
        if 'leaf' in branch:
            assert set(branch) == {'leaf'}
            row = branch['leaf']
            assert row['path'] == path
            reason, margin = evaluate(box)
            assert reason not in {'unresolved denominator', 'unresolved target'}, (path, reason, margin)
            # Finer radicals should reproduce or strengthen each literal guard.
            assert reason == row['reason'], (path, reason, row['reason'])
            if reason == 'positive separation':
                assert margin > FLOOR
                assert margin >= F(row['margin'])
            replay.append({'path': path, 'reason': reason,
                           'margin': None if margin is None else str(margin)})
            return
        assert set(branch) == {'0', '1'}
        normalized_widths = [(q.high - q.low) / w for q, w in zip(box, WIDTHS)]
        greatest = max(normalized_widths)
        axis = normalized_widths.index(greatest)
        mid = (box[axis].low + box[axis].high) / 2
        lower, upper = list(box), list(box)
        lower[axis] = Interval(box[axis].low, mid)
        upper[axis] = Interval(mid, box[axis].high)
        assert lower[axis].low == box[axis].low
        assert lower[axis].high == upper[axis].low
        assert upper[axis].high == box[axis].high
        visit(branch['0'], tuple(lower), path + '0')
        visit(branch['1'], tuple(upper), path + '1')

    visit(trie, INITIAL, '')
    assert seen_nodes == 3135 == 2 * len(replay) - 1
    assert deepest == 15
    margins = [F(row['margin']) for row in replay if row['reason'] == 'positive separation']
    screen_margins = [F(row['margin']) for row in replay if row['reason'] == 'leaf screen']
    assert min(margins) > FLOOR and min(screen_margins) > 0
    output = {
        'method': 'Independent Interval class, alternative 96-bit radical formula, exact trie reconstruction; no author code imported.',
        'source_pins': pins,
        'author_leaf_digest': hashlib.sha256(payload).hexdigest(),
        'printed_source_minimum_verified': True,
        'radical_bits': 96,
        'nodes': seen_nodes,
        'leaves': len(replay),
        'max_depth': deepest,
        'counts': dict(Counter(row['reason'] for row in replay)),
        'minimum_target_bound': str(min(margins)),
        'strict_margin_above_uniform_floor': str(min(margins) - FLOOR),
        'minimum_rejection_margin': str(min(screen_margins)),
        'complete_closed_box_cover': True,
        'every_positive_bound_at_least_author_bound': True,
        'replay': replay,
    }
    out = BASE / 'checkpoints' / 'hexagon_aligned_low_s_lower_return_height_independent_checks_2026_10_28.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({k: v for k, v in output.items() if k != 'replay'}, indent=2))
    print(json.dumps({'record': str(out), 'sha256': hashlib.sha256(out.read_bytes()).hexdigest()}))


if __name__ == '__main__':
    main()
