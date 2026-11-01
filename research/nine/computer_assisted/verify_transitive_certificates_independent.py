#!/usr/bin/env python3
"""Independently check both transitive triangle split-tree certificates.

No imports from either generator or their interval kernel. Uses exact Fraction
arithmetic and integer square roots. Run with assertions enabled. Physical
transfer and the perpendicular arc reduction are reviewed separately.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json

TARGET = F(625, 144)
SCALE = 1 << 18


def n(x):
    return x if isinstance(x, tuple) else (F(x), F(x))


def add(x, y):
    x, y = n(x), n(y)
    return x[0]+y[0], x[1]+y[1]


def sub(x, y):
    x, y = n(x), n(y)
    return x[0]-y[1], x[1]-y[0]


def mul(x, y):
    products = [a*b for a in n(x) for b in n(y)]
    return min(products), max(products)


def div(x, y):
    y = n(y)
    assert y[0] > 0
    return mul(x, (1/y[1], 1/y[0]))


def square(x):
    x = n(x)
    return (F(0) if x[0] <= 0 <= x[1] else min(a*a for a in x),
            max(a*a for a in x))


def clip(x, lo, hi):
    result = max(x[0], F(lo)), min(x[1], F(hi))
    return result if result[0] <= result[1] else None


def nonnegative(x):
    return (max(F(0), x[0]), x[1]) if x[1] >= 0 else None


def root(x):
    assert x[0] >= 0
    lo = isqrt(x[0].numerator*SCALE*SCALE//x[0].denominator)
    hi = isqrt(x[1].numerator*SCALE*SCALE//x[1].denominator)
    if F(hi*hi, SCALE*SCALE) < x[1]:
        hi += 1
    assert F(lo*lo, SCALE*SCALE) <= x[0] <= x[1] <= F(hi*hi, SCALE*SCALE)
    return F(lo, SCALE), F(hi, SCALE)


def sin_half(t):
    return 2*t/(1+t*t)


def cos_half(t):
    return (1-t*t)/(1+t*t)


def same_side(box, branch):
    c, ell = box
    if ell[1] < 2*c[0]:
        return "empty_geometry", None
    s = root(sub(1, square(c)))
    ss = clip(mul(ell, s), 0, 1)
    if ss is None:
        return "empty_geometry", None
    cc = root(sub(1, square(ss)))
    d = clip(add(mul(ell, c), cc), 0, 1)
    if d is None:
        return "empty_geometry", None
    k = add(mul(s, cc), mul(c, ss))
    raw_l = sub(mul(c, cc), mul(s, ss))
    if raw_l[0] > 0:
        return "empty_geometry", None
    l = raw_l[0], min(F(0), raw_l[1])
    a = div(sub(1, ell), sub(s, c))
    if branch == 0:
        numerator, denominator = nonnegative(add(k, l)), ss
        if numerator is None:
            return "empty_positive_force", None
        qb = add(d, ss), cc
    elif branch == 1:
        numerator, denominator = k, nonnegative(sub(ss, cc))
        if denominator is None:
            return "empty_support_branch", None
        qb = add(sub(d, cc), ss), add(ss, cc)
    elif branch == 2:
        numerator, denominator = k, ss
        eps = clip(mul(mul(-1, ell), l), 0, 1)
        if eps is None:
            return "empty_original_mean", None
        qb = sub(add(d, ss), mul(eps, cc)), add(cc, mul(eps, ss))
    else:
        raise AssertionError(branch)
    na = root(add(square(s), square(add(a, c))))
    wa = sub(sub(c, s), div(s, na)), add(add(s, c), div(add(a, c), na))
    bx, by = mul(s, denominator), sub(numerator, mul(c, denominator))
    nb = root(add(square(bx), square(by)))
    wb = add(qb[0], div(bx, nb)), add(qb[1], div(by, nb))
    mean = F(0), d[1]
    horizontal = add(mul(F(3, 2), square(sub(wa[0], wb[0]))),
                     mul(2, square(sub(mean, div(add(wa[0], wb[0]), 2)))))
    vertical = add(add(square(sub(wa[1], wb[1])), square(add(wb[1], 2))),
                   square(add(wa[1], 2)))
    return "variance", (horizontal[0]+vertical[0])/9


def perpendicular(box, mode):
    p, r, z = box
    if cos_half(p[0]) < sin_half(p[0]):
        return "empty_angle", None
    c = cos_half(p[1]), cos_half(p[0])
    s = sin_half(p[0]), sin_half(p[1])
    ss = mul(r, s)
    cc = root(sub(1, square(ss)))
    ell = (r[0]+(1-r[0])*z[0], r[1]+(1-r[1])*z[1])
    s0 = sub(1, mul(mul(sub(1, r), z), s))
    t0 = clip(add(sub(1, cc), mul(ell, c)), 0, 1)
    if t0 is None:
        return "empty_position", None
    eps = clip(mul(r, add(mul(c, cc), mul(s, ss))), 0, r[1])
    if eps is None:
        return "empty_original_mean", None
    qa = add(add(1, c), s), sub(add(s0, s), c)
    wa = (add(qa[0], 1), qa[1]) if mode == 0 else (add(qa[0], s), sub(qa[1], c))
    wb = (add(sub(t0, mul(2, ss)), mul(eps, cc)),
          add(add(1, mul(2, cc)), mul(eps, ss)))
    norm = root(add(square(t0), square(s0)))
    wc = div(mul(-1, t0), norm), div(mul(-1, s0), norm)
    lower = sum(square(sub(a[axis], b[axis]))[0]
                for a, b in ((wa, wb), (wb, wc), (wc, wa)) for axis in (0, 1))/9
    return "variance", lower


def decode(box):
    return tuple(tuple(map(F, interval)) for interval in box)


def verify(filename, evaluator, field, root_count, dimension, reserve, expected):
    certificate = json.loads(Path(__file__).with_name(filename).read_text())
    assert F(certificate["report"]["target_squared"]) == TARGET
    assert certificate["report"]["sqrt_scale"] == SCALE
    assert len(certificate["trees"]) == root_count
    counters = {"nodes": 0, "variance": 0, "empty": 0}
    empty_reasons = {}
    for index, tree in enumerate(certificate["trees"]):
        assert tree[field] == index
        initial = ((F(0), F(1, 2)),)+((F(0), F(1)),)*(dimension-1)
        assert decode(tree["root"]) == initial
        records = {entry["address"]: entry for entry in tree["nodes"]}
        assert len(records) == len(tree["nodes"])
        stack, seen = [("", initial)], set()
        while stack:
            address, box = stack.pop()
            assert address not in seen
            seen.add(address)
            entry = records[address]
            counters["nodes"] += 1
            if "split_axis" in entry:
                axis, midpoint = entry["split_axis"], F(entry["split_at"])
                assert 0 <= axis < dimension
                assert midpoint == sum(box[axis])/2
                assert box[axis][0] < midpoint < box[axis][1]
                left, right = list(box), list(box)
                left[axis] = box[axis][0], midpoint
                right[axis] = midpoint, box[axis][1]
                stack += [(address+"0", tuple(left)), (address+"1", tuple(right))]
            else:
                assert decode(entry["box"]) == box
                reason, bound = evaluator(box, index)
                assert reason == entry["reason"]
                if reason == "variance":
                    assert bound == F(entry["lower_bound"])
                    assert bound-TARGET > reserve
                    counters["variance"] += 1
                else:
                    assert reason.startswith("empty_")
                    counters["empty"] += 1
                    empty_reasons[reason] = empty_reasons.get(reason, 0)+1
        assert seen == set(records)
    assert counters == expected
    report = certificate["report"]
    assert report["total_nodes"] == counters["nodes"]
    assert report["total_variance_leaves"] == counters["variance"]
    assert report["total_empty_leaves"] == counters["empty"]
    print(filename, counters, empty_reasons)


if __name__ == "__main__":
    verify("transitive_same_side_triangle_certificate.json", same_side,
           "branch", 3, 2, F(1, 3000),
           {"nodes": 745, "variance": 320, "empty": 54})
    verify("transitive_perpendicular_triangle_certificate.json", perpendicular,
           "mode", 2, 3, F(1, 7000),
           {"nodes": 5696, "variance": 2730, "empty": 119})
    print("Independent exact verification passed: all splits, empty leaves, stored bounds, and strict reserves.")
