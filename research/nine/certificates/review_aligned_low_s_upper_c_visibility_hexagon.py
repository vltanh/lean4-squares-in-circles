#!/usr/bin/env python3
"""Independent complete rational audit of the upper-C visibility certificate.

No author code or interval helper is imported.  The author terminal paths
are untrusted certificate data: a new trie checks their complete closed
partition, then each box is reconstructed and every guard and both target
bounds are reevaluated using exact Fractions and a 112-bit radical lattice.
The accompanying full review separately audits the original geometry.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from collections import Counter
import hashlib
import json

BASE = Path(__file__).resolve().parents[1]
SCALE = 1 << 112


@dataclass(frozen=True)
class Interval:
    low: F
    high: F

    def __post_init__(self):
        assert isinstance(self.low, F) and isinstance(self.high, F)
        assert self.low <= self.high

    @classmethod
    def point(cls, value):
        return cls(F(value), F(value))

    def __add__(self, other):
        return Interval(self.low + other.low, self.high + other.high)

    def __neg__(self):
        return Interval(-self.high, -self.low)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        products = (self.low * other.low, self.low * other.high,
                    self.high * other.low, self.high * other.high)
        return Interval(min(products), max(products))

    def __truediv__(self, other):
        assert other.low > 0
        return self * Interval(F(1) / other.high, F(1) / other.low)

    def square(self):
        upper = max(self.low ** 2, self.high ** 2)
        lower = F(0) if self.low <= 0 <= self.high else min(self.low ** 2, self.high ** 2)
        return Interval(lower, upper)

    def meet(self, other):
        lo, hi = max(self.low, other.low), min(self.high, other.high)
        return None if lo > hi else Interval(lo, hi)

    def root(self):
        assert self.high >= 0

        def enclose(q):
            assert q >= 0
            numerator, denominator = q.numerator, q.denominator
            # A different exact integer formula from the author code.
            k = isqrt(numerator * denominator * SCALE * SCALE) // denominator
            assert k * k * denominator <= numerator * SCALE * SCALE
            assert (k + 1) ** 2 * denominator > numerator * SCALE * SCALE
            is_exact = k * k * denominator == numerator * SCALE * SCALE
            return F(k, SCALE), F(k if is_exact else k + 1, SCALE)

        return Interval(enclose(max(F(0), self.low))[0], enclose(self.high)[1])


C = Interval.point
ONE = C(1)
HALF = C(F(1, 2))
RADICAL_UPPER = C(F(99, 70))
INITIAL = (Interval(F(14, 15), F(1)),
           Interval(F(29, 50), F(2, 3)),
           Interval(F(2, 25), F(1)))
WIDTHS = tuple(q.high - q.low for q in INITIAL)
UNIFORM_FLOOR = F(1, 1000000)


def evaluate(box):
    d, h, t = box
    a, g = ONE - d, ONE - h
    b = (ONE - t.square()).root()
    radius2 = (d + ONE).square() + C(F(1, 4))
    if radius2.high <= 4:
        return 'R>2', None
    Y = g + b + t
    Xrad = radius2 - Y.square()
    if Xrad.high <= 0:
        return 'X>0', None
    X = Xrad.root()
    x = (X - b + t).meet(Interval(F(3, 10), d.high))
    if x is None:
        return 'x in (3/10,d)', None
    x = x.meet(Interval(t.low, d.high))
    if x is None:
        return 'x>t', None
    X = X.meet(x + b - t)
    if X is None:
        return 'lower point identity', None
    screen = (d - x) * t - (h - HALF) * b
    if screen.high < 0:
        return 'actual leaf screen', None
    w = x + a
    if w.low <= 0 or X.low <= 0:
        return 'unresolved denominator', None
    c = ONE / (ONE + (h / w).square()).root()
    s = ONE / (ONE + (w / h).square()).root()
    N, K = a * c + h * s, x * s
    Wrad = radius2 - (N + ONE).square()
    if Wrad.high < 0:
        return 'upper circle W real', None
    W = Wrad.root()
    rho = (W - K).meet(Interval(F(7, 8), F(1)))
    if rho is None:
        return 'upper actual mean rho', None
    delta = ONE - rho
    if W.low <= 0:
        return 'unresolved denominator', None
    lam = ((K - N * rho) / W).meet(Interval(F(0), F(197, 925)))
    if lam is None:
        return 'upper proper concurrence', None

    horizontal_gap = a + x - t
    L0, H0 = delta * s, ONE - delta * c
    L1, H1 = lam * c + delta * s, ONE + lam * s - delta * c
    direct0 = (horizontal_gap + L0) * H0 - RADICAL_UPPER * L0
    expanded0 = horizontal_gap * H0 + L0 * (H0 - RADICAL_UPPER)
    direct1 = (horizontal_gap + L1) * H1 - RADICAL_UPPER * L1
    expanded1 = horizontal_gap * H1 + L1 * (H1 - RADICAL_UPPER)
    lower0 = max(direct0.low, expanded0.low)

    linear = s * horizontal_gap + (ONE - RADICAL_UPPER) * c + delta * (s.square() - c.square())
    quadratic = (c * s).low
    assert quadratic > 0
    vertex = -linear.low / (2 * quadratic)
    minimizing_u = min(lam.high, max(lam.low, vertex))
    quadratic_bound = lower0 + linear.low * minimizing_u + quadratic * minimizing_u ** 2
    lower1 = max(direct1.low, expanded1.low, quadratic_bound)
    lower = min(lower0, lower1)
    if lower > UNIFORM_FLOOR:
        return 'strict target', lower
    return 'unresolved target', lower


def exact_hand_checks():
    margins = {
        'radius implies d>14/15': F(15, 4) - F(29, 15) ** 2,
        'sqrt2<99/70': F(99, 70) ** 2 - 2,
        'X positive corner reserve': 4 - (2 + F(297, 250) + F(441, 2500)),
        'x>t corner reserve': 4 - (F(21, 8) + F(297, 250) + F(441, 2500)),
        '21/8 quadratic matrix determinant': F(5, 8) * F(13, 8) - 1,
        'sqrt5<9/4': F(9, 4) ** 2 - 5,
        'b<7/10 alternative gives t>7/10': F(51, 100) - F(49, 100),
        'upper unique corner reserve': 4 - F(389, 100),
        'rho radical reserve': F(25711 ** 2 - 11413 * 240 ** 2),
        'lambda<1/4': F(1, 4) - F(197, 925),
        'far support>1': F(27, 25) - 1,
        'upper N>1/4': F(841, 3125) - F(1, 4),
    }
    assert margins['X positive corner reserve'] == F(1589, 2500)
    assert margins['x>t corner reserve'] == F(53, 5000)
    assert margins['rho radical reserve'] == 3666721
    assert F(1) - F(29, 50) * F(7, 8) == F(197, 400)
    assert F(197, 400) * F(2, 3) / (F(2, 3) + F(7, 8)) == F(197, 925)
    assert all(q > 0 for q in margins.values())

    # A small independent exact polynomial ring checks all coefficients.
    variables = ('A', 'c', 's', 'delta', 'u', 'r', 'K', 'N', 'rho')
    zero = (0,) * len(variables)

    def const(q):
        return {} if not q else {zero: F(q)}

    def var(name):
        exponent = list(zero); exponent[variables.index(name)] = 1
        return {tuple(exponent): F(1)}

    def add(*polynomials):
        result = {}
        for p in polynomials:
            for key, value in p.items():
                result[key] = result.get(key, F(0)) + value
        return {key: value for key, value in result.items() if value}

    def mul(p, q):
        result = {}
        for left, lv in p.items():
            for right, rv in q.items():
                key = tuple(a + b for a, b in zip(left, right))
                result[key] = result.get(key, F(0)) + lv * rv
        return {key: value for key, value in result.items() if value}

    def sub(p, q):
        return add(p, {key: -value for key, value in q.items()})

    A, c, s, delta, u, r, K, N, rho = map(var, variables)
    one = const(1)
    L = add(mul(u, c), mul(delta, s))
    H = add(one, mul(u, s), mul(const(-1), mul(delta, c)))
    G = sub(mul(add(A, L), H), mul(r, L))
    L0, H0 = mul(delta, s), sub(one, mul(delta, c))
    G0 = sub(mul(add(A, L0), H0), mul(r, L0))
    B0 = add(mul(s, A), mul(sub(one, r), c), mul(delta, sub(mul(s, s), mul(c, c))))
    assert sub(G, add(G0, mul(B0, u), mul(mul(c, s), mul(u, u)))) == {}
    assert sub(G, add(mul(A, H), mul(L, sub(H, r)))) == {}
    assert sub(sub(mul(K, add(N, one)), mul(N, add(K, rho))), sub(K, mul(N, rho))) == {}
    return {'positive_exact_reserves': {name: str(q) for name, q in margins.items()},
            'coefficientwise_identities': ['full G quadratic expansion', 'equivalent G evaluation', 'proper concurrence numerator'],
            'two_exact_lambda_rational_equalities': True}


def main():
    pins = {
        'HOUSE_LOWER_TAC_S_ALIGNED_UPPER_C_EXCLUSION.md':
        'b773da381ac721c0f3c06083c9da6258ea1142353fd4a6e000edaff1d8398125',
        'certificates/aligned_low_s_upper_c_visibility_separation.py':
        'd57e7506d4f6e1dd92c991c8579fcfcd03377703863b0d42d50f417267fe2c4c',
    }
    for name, pin in pins.items():
        assert hashlib.sha256((BASE / name).read_bytes()).hexdigest() == pin
    author_path = Path('/tmp/aligned_low_s_upper_c_visibility_certificate.json')
    author = json.loads(author_path.read_text())
    leaves = author['leaves']
    payload = json.dumps(leaves, sort_keys=True, separators=(',', ':')).encode()
    digest = hashlib.sha256(payload).hexdigest()
    assert digest == 'c8abdb83f97e69fd9445b3733df9fd2fcd77eaf357a69eea23fe63d3800397ad'
    expected_counts = Counter({'strict target': 17438, 'R>2': 234,
                               'upper proper concurrence': 226, 'actual leaf screen': 1024,
                               'x in (3/10,d)': 359, 'upper actual mean rho': 70})
    assert Counter(row['reason'] for row in leaves) == expected_counts
    assert len(leaves) == 19351
    assert min(F(row['reserve']) for row in leaves if row['reserve'] is not None) == F(author['smallest_margin']) > UNIFORM_FLOOR

    trie = {}
    for row in leaves:
        branch = trie
        assert set(row['path']) <= {'0', '1'}
        for digit in row['path']:
            assert 'leaf' not in branch
            branch = branch.setdefault(digit, {})
        assert not branch
        branch['leaf'] = row

    nodes, deepest, replay = 0, 0, []

    def walk(branch, box, path):
        nonlocal nodes, deepest
        nodes += 1
        deepest = max(deepest, len(path))
        if 'leaf' in branch:
            assert set(branch) == {'leaf'}
            row = branch['leaf']
            assert row['path'] == path
            reason, margin = evaluate(box)
            assert reason == row['reason'], (path, reason, row['reason'], margin)
            if reason == 'strict target':
                assert margin > UNIFORM_FLOOR
                assert margin >= F(row['reserve']), (path, margin, row['reserve'])
            replay.append({'path': path, 'reason': reason,
                           'reserve': None if margin is None else str(margin)})
            return
        assert set(branch) == {'0', '1'}
        widths = [(q.high - q.low) / w for q, w in zip(box, WIDTHS)]
        axis = widths.index(max(widths))
        midpoint = (box[axis].low + box[axis].high) / 2
        lower, upper = list(box), list(box)
        lower[axis] = Interval(box[axis].low, midpoint)
        upper[axis] = Interval(midpoint, box[axis].high)
        assert lower[axis].low == box[axis].low
        assert lower[axis].high == upper[axis].low
        assert upper[axis].high == box[axis].high
        walk(branch['0'], tuple(lower), path + '0')
        walk(branch['1'], tuple(upper), path + '1')

    walk(trie, INITIAL, '')
    assert nodes == 38701 == 2 * len(replay) - 1
    assert deepest == 18
    assert Counter(row['reason'] for row in replay) == expected_counts
    minimum = min(F(row['reserve']) for row in replay if row['reserve'] is not None)
    assert minimum > UNIFORM_FLOOR
    record = {
        'method': 'Independent immutable Fraction intervals; alternative 112-bit radical formula; complete binary trie and box reconstruction; no author code imported.',
        'pins': pins, 'author_complete_leaf_digest': digest,
        'author_record_sha256': hashlib.sha256(author_path.read_bytes()).hexdigest(),
        'nodes': nodes, 'leaves': len(replay), 'maximum_depth': deepest,
        'reason_counts': dict(Counter(row['reason'] for row in replay)),
        'complete_closed_box_cover': True, 'all_original_leaf_reasons_reproved': True,
        'every_positive_bound_at_least_author_bound': True,
        'uniform_strict_floor': str(UNIFORM_FLOOR),
        'minimum_independent_bound': str(minimum),
        'strict_floor_reserve': str(minimum - UNIFORM_FLOOR),
        'hand_checks': exact_hand_checks(), 'replay': replay,
    }
    output = BASE / 'checkpoints/hexagon_aligned_low_s_upper_c_visibility_independent_checks_2026_10_28.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({key: value for key, value in record.items() if key != 'replay'}, indent=2))
    print(json.dumps({'output': str(output), 'sha256': hashlib.sha256(output.read_bytes()).hexdigest()}))


if __name__ == '__main__':
    main()
