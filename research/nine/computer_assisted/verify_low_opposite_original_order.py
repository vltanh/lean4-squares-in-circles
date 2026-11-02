#!/usr/bin/env python3
"""Independent Fraction replay of the two-variable opposite-half order table.

Only the separately accepted independent Fraction arithmetic is reused.
No producer, producer kernel, or producer evaluator is imported. The
physical four rows, fixed roots, and exact midpoint coverage are rebuilt.
"""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import hashlib
import json
import sys
import time

from verify_ownhalf_above_side import Interval as I, minimum, maximum

ROOT = ((F(0), F(1)), (F(7, 10), F(13, 12)))
Q = F(1105, 256)
M = F(1129, 3000)
J = F(29927, 30000)
CONTAINED_HEIGHT = maximum((I(F(4421, 12000)),
                            1 - I(Q - (F(59, 60) + J)**2).sqrt()))


@lru_cache(maxsize=None)
def frame(pair):
    values = []
    for end in pair:
        t = I(end)
        norm = (1 + t.square()).sqrt()
        values.append((1 / norm, t / norm,
                       (1 + t) / (2 * norm), (1 - t) / (2 * norm)))
    left, right = values
    # a,k decrease; b,r increase on the closed folded-angle interval.
    return (I(right[0].lo, left[0].hi), I(left[1].lo, right[1].hi),
            I(left[2].lo, right[2].hi), I(right[3].lo, left[3].hi))


def toll(pair, b):
    def phi(t):
        aa, bb, _, _ = frame((t, t))
        return 6 * bb - F(27, 2) * (1 - aa)
    left, right = phi(pair[0]), phi(pair[1])
    low, high = min(left.lo, right.lo), max(left.hi, right.hi)
    # Phi'(t) has the sign of 6-(27/2)t, so this is the only maximum.
    if pair[0] <= F(4, 9) <= pair[1]:
        high = max(high, (I(F(873, 4)).sqrt() - F(27, 2)).hi)
    return maximum((2 * b, I(low, high)))


def expressions(box, sign):
    t, X = (I(*pair) for pair in box)
    a, b, r, k = frame(box[0])
    inward = F(503, 480) - X
    if sign > 0:
        loss = maximum((I(0), t * (k + inward)))
        offsets = ((k, r), (r, -k), (-k, -r), (-r, k))
    else:
        loss = maximum((I(0), (inward - k) / maximum((t, I(F(1, 4))))))
        offsets = ((r, k), (k, -r), (-r, -k), (-k, r))
    lower = maximum((I(F(3, 5)), CONTAINED_HEIGHT + r - loss))
    # Each of the four original corners supplies a necessary upper height.
    upper = minimum((Q - (X + dx).square()).sqrt() - dy for dx, dy in offsets)
    owned_span = minimum((1 / (2 * r), F(1, 2) + F(12, 17) * (1 - r)))
    needed_span = maximum((owned_span, F(707, 2000) + 1 / (4 * r), I(F(707, 1000))))
    xmax = minimum((I(M), X - needed_span))

    def bracket(x):
        return x + (1 - (x + F(147, 250)).square()).sqrt()

    endpoint_minimum = minimum((bracket(I(0)), bracket(xmax)))
    return (xmax, upper - lower,
            F(9, 16) - lower + X - endpoint_minimum,
            r + F(451, 810) - X - F(2, 27) * toll(box[0], b))


def integer(v):
    return type(v) is int


def verify(data):
    assert data['schema'] == 'low_opposite_original_order_v1'
    assert data['status'] == 'COMPLETE_PENDING_INDEPENDENT_REPLAY'
    assert data['root'] == [[str(a), str(b)] for a, b in ROOT]
    assert integer(data['remaining']) and data['remaining'] == 0 and data['pending'] == []
    roots, nodes = data['roots'], data['nodes']
    assert type(roots) is list and len(roots) == 2
    assert all(type(row) is dict and set(row) == {'index', 'sign'} for row in roots)
    assert all(integer(row['index']) and integer(row['sign']) for row in roots)
    assert {row['sign'] for row in roots} == {-1, 1}
    assert len({row['index'] for row in roots}) == 2
    assert type(nodes) is list
    assert integer(data['leaves']) and len(nodes) == 2 * data['leaves'] - 2
    assert integer(data['maximum_depth']) and 0 <= data['maximum_depth'] <= 60
    assert type(data['counts']) is list and len(data['counts']) == 4
    assert all(integer(v) and v >= 0 for v in data['counts'])
    assert sum(data['counts']) == data['leaves']
    seen, counts, per_root = set(), [0] * 4, []
    maximum_depth = 0
    largest = None

    def visit(index, box, sign, depth):
        nonlocal maximum_depth, largest
        assert integer(index) and 0 <= index < len(nodes) and index not in seen
        assert depth <= 60
        seen.add(index)
        maximum_depth = max(maximum_depth, depth)
        node = nodes[index]
        assert type(node) is dict
        if 'rule' in node:
            assert set(node) == {'rule', 'upper'}
            assert integer(node['rule']) and 0 <= node['rule'] < 4
            assert type(node['upper']) is str
            upper = expressions(box, sign)[node['rule']].hi
            assert upper < 0, ('failed exact leaf', index, box, sign, node['rule'], upper)
            largest = upper if largest is None else max(largest, upper)
            counts[node['rule']] += 1
            return
        assert set(node) == {'axis', 'children'}
        axis, children = node['axis'], node['children']
        assert integer(axis) and 0 <= axis < 2
        assert type(children) is list and len(children) == 2
        lo, hi = box[axis]
        midpoint = (lo + hi) / 2
        left, right = list(box), list(box)
        left[axis], right[axis] = (lo, midpoint), (midpoint, hi)
        visit(children[0], tuple(left), sign, depth + 1)
        visit(children[1], tuple(right), sign, depth + 1)

    for row in roots:
        before = sum(counts)
        visit(row['index'], ROOT, row['sign'], 0)
        per_root.append(sum(counts) - before)
    assert len(seen) == len(nodes) == 2 * sum(counts) - 2
    assert counts == data['counts'] and maximum_depth == data['maximum_depth']
    return {'result': 'PASS', 'complete': True, 'nodes': len(nodes),
            'strict_leaves': sum(counts), 'roots': 2, 'counts': counts,
            'leaves_per_root': per_root, 'maximum_depth': maximum_depth,
            'largest_replayed_upper': str(largest),
            'arithmetic': 'independent Fraction intervals with 90-bit outward radicals',
            'scope': 'opposite-half ordering; no selected-P floor premise and no mask closure'}


def main():
    path = (Path(sys.argv[1]) if len(sys.argv) > 1
            else Path(__file__).with_name('low_opposite_original_order_cover.json'))
    raw = path.read_bytes()
    start = time.monotonic()
    report = verify(json.loads(raw))
    kernel = Path(__file__).with_name('verify_ownhalf_above_side.py')
    report.update(certificate_file=path.name,
                  certificate_sha256=hashlib.sha256(raw).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  independent_fraction_kernel_file=kernel.name,
                  independent_fraction_kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
                  producer_imports=False, seconds=time.monotonic() - start)
    path.with_name(path.stem + '_independent_replay.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
