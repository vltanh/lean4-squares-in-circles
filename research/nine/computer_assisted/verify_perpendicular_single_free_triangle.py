#!/usr/bin/env python3
"""Exact interval proof for the perpendicular-owner, one-free-edge triangle.

No floating-point operations, numerical tolerances, third-party dependencies,
Lean, or CI.  Every leaf is proved empty or has a strict exact variance bound.
The two rectangular roots, together with the separately proved analytic corner
rectangle, cover the full closed half-angle triangle 0 <= p <= q <= 1.

Run from the repository root:
  python research/nine/computer_assisted/verify_perpendicular_single_free_triangle.py
An optional --certificate PATH emits the complete split tree with exact leaves.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
from pathlib import Path


TARGET = F(625, 144)  # Stronger than the research Q=1105/256.
SQRT_SCALE = 1 << 18


class Undecided(Exception):
    pass


@dataclass(frozen=True)
class I:
    lo: F
    hi: F

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError("reversed interval")

    @staticmethod
    def exact(x):
        return x if isinstance(x, I) else I(F(x), F(x))

    def __add__(self, other):
        b = I.exact(other)
        return I(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -I.exact(other)

    def __rsub__(self, other):
        return I.exact(other) + -self

    def __mul__(self, other):
        b = I.exact(other)
        vals = (self.lo*b.lo, self.lo*b.hi,
                self.hi*b.lo, self.hi*b.hi)
        return I(min(vals), max(vals))

    __rmul__ = __mul__

    def __truediv__(self, other):
        b = I.exact(other)
        if b.lo <= 0:
            raise Undecided("denominator not yet proved strictly positive")
        return self * I(1/b.hi, 1/b.lo)

    def square(self):
        upper = max(self.lo*self.lo, self.hi*self.hi)
        lower = 0 if self.lo <= 0 <= self.hi else min(
            self.lo*self.lo, self.hi*self.hi)
        return I(F(lower), upper)

    def intersect(self, lower, upper):
        a, b = max(self.lo, F(lower)), min(self.hi, F(upper))
        return None if a > b else I(a, b)


def sqrt_enclosure(value: I) -> I:
    """Outward rational square-root bounds, proved by integer comparisons."""
    if value.lo < 0:
        raise ValueError("negative radicand")
    scale2 = SQRT_SCALE * SQRT_SCALE
    k_lo = isqrt(value.lo.numerator * scale2 // value.lo.denominator)
    k_hi = isqrt(value.hi.numerator * scale2 // value.hi.denominator)
    lower = F(k_lo, SQRT_SCALE)
    upper = F(k_hi, SQRT_SCALE)
    if upper*upper < value.hi:
        upper += F(1, SQRT_SCALE)
    if not (lower*lower <= value.lo and upper*upper >= value.hi):
        raise ArithmeticError("integer square-root enclosure failed")
    return I(lower, upper)


def sin_half(t: F) -> F:
    return 2*t/(1+t*t)


def cos_half(t: F) -> F:
    return (1-t*t)/(1+t*t)


def orientation(t: I):
    # On 0<=t<=1, sin(2 atan t) is increasing; cosine is decreasing.
    return (I(cos_half(t.hi), cos_half(t.lo)),
            I(sin_half(t.lo), sin_half(t.hi)))


def sin_difference(p: F, q: F) -> F:
    # Exactly sin(2 atan q - 2 atan p), without evaluating atan.
    return 2*(q-p)*(1+p*q)/((1+p*p)*(1+q*q))


def difference_interval(p: I, q: I):
    # Actual chart points satisfy p<=q. Their angle difference lies in [0,pi/2],
    # where sine is increasing. These endpoint bounds are outward on that set.
    lower = F(0) if q.lo <= p.hi else sin_difference(p.hi, q.lo)
    upper = sin_difference(p.lo, q.hi)
    return I(lower, upper)


def variance_lower(box):
    p, q = box
    if p.lo > q.hi:
        return "empty_order", None
    ca, sa = orientation(p)
    cb, sb = orientation(q)
    delta = difference_interval(p, q)
    # The angle-ordered physical chart has 0<=s,t<=1. Clipping uses only that
    # exact geometric fact, and does not exclude any legal original contact.
    t = (1-ca+cb).intersect(0, 1)
    s = (1+sa-sb).intersect(0, 1)
    if t is None or s is None:
        return "empty_position", None
    den_a = t*ca+s*sa
    den_b = t*cb+s*sb
    # Cancel sin(beta-alpha) before evaluation; this includes p=q continuously.
    tau_a = (1-t*sb*delta/den_a).intersect(0, 1)
    tau_b = (1-s*ca*delta/den_b).intersect(0, 1)
    if tau_a is None or tau_b is None:
        return "empty_original_mean", None
    norm = sqrt_enclosure(t.square()+s.square())
    a = (1+2*sb+tau_a*cb, s-2*cb+tau_a*sb)
    b = (t-2*sa+tau_b*ca, 1+2*ca+tau_b*sa)
    c = (-t/norm, -s/norm)
    pairs = ((a, b), (b, c), (c, a))
    total = F(0)
    for first, second in pairs:
        for axis in (0, 1):
            total += (first[axis]-second[axis]).square().lo
    bound = total/9
    return ("variance" if bound > TARGET else "undecided"), bound


def frac(x):
    return str(x)


def encode_box(box):
    return [[frac(v.lo), frac(v.hi)] for v in box]


def verify_root(box, label, max_nodes, keep_tree):
    counters = {"label": label, "nodes": 0, "variance_leaves": 0,
                "empty_leaves": 0, "max_depth": 0}
    least = None
    stack = [(box, 0, "")]
    tree = []
    while stack:
        current, depth, address = stack.pop()
        counters["nodes"] += 1
        if counters["nodes"] > max_nodes or depth > 60:
            raise RuntimeError("UNRESOLVED: proof resource limit reached")
        counters["max_depth"] = max(counters["max_depth"], depth)
        try:
            reason, bound = variance_lower(current)
        except Undecided:
            reason, bound = "undecided", None
        if reason == "variance":
            counters["variance_leaves"] += 1
            margin = bound-TARGET
            least = margin if least is None else min(least, margin)
            if keep_tree:
                tree.append({"address": address, "box": encode_box(current),
                             "reason": reason, "lower_bound": frac(bound)})
            continue
        if reason.startswith("empty_"):
            counters["empty_leaves"] += 1
            if keep_tree:
                tree.append({"address": address, "box": encode_box(current),
                             "reason": reason})
            continue
        widths = [v.hi-v.lo for v in current]
        axis = 0 if widths[0] >= widths[1] else 1
        v = current[axis]
        middle = (v.lo+v.hi)/2
        left, right = list(current), list(current)
        left[axis], right[axis] = I(v.lo, middle), I(middle, v.hi)
        if keep_tree:
            tree.append({"address": address, "split_axis": axis,
                         "split_at": frac(middle)})
        # Both closed children are included; their common boundary is harmless.
        stack.append((tuple(right), depth+1, address+"1"))
        stack.append((tuple(left), depth+1, address+"0"))
    counters["least_margin"] = None if least is None else frac(least)
    counters["least_margin_gt_1_over_6000"] = bool(
        least is not None and least > F(1, 6000))
    return counters, tree


def verify_analytic_tail():
    # p<=1/20 implies sin(alpha)<=1/10; q>=10/11 implies cos(beta)<=1/10.
    if not (sin_half(F(1, 20)) <= F(1, 10)
            and cos_half(F(10, 11)) <= F(1, 10)):
        raise ArithmeticError("analytic-tail chart implication failed")
    coordinate = F(149, 50)
    center = coordinate-F(25, 12)
    # With both center coordinates >=center>0, a negative-quadrant unit point
    # has squared distance at least 2center^2+1+2center, strictly above TARGET.
    margin = 2*center*center+1+2*center-TARGET
    if center <= 0 or margin <= 0:
        raise ArithmeticError("analytic-tail strict contradiction failed")
    return {"root": [["0", "1/20"], ["10/11", "1"]],
            "reason": "two_coordinate_bounds_and_negative_unit_point",
            "center_coordinate_lower_bound": frac(center),
            "strict_margin": frac(margin)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path)
    parser.add_argument("--max-nodes", type=int, default=500000)
    args = parser.parse_args()
    tail = verify_analytic_tail()
    roots = [
        ((I(F(0), F(1, 20)), I(F(0), F(10, 11))), "low_p_below_tail"),
        ((I(F(1, 20), F(1)), I(F(0), F(1))), "remaining_p"),
    ]
    results, trees = [], []
    for root, label in roots:
        counts, tree = verify_root(root, label, args.max_nodes,
                                   args.certificate is not None)
        results.append(counts)
        trees.append({"label": label, "root": encode_box(root), "nodes": tree})
        print(json.dumps(counts, sort_keys=True), flush=True)
    report = {"theorem": "perpendicular_owner_one_free_triangle_radius_gt_25_over_12",
              "target_squared": frac(TARGET), "sqrt_scale": SQRT_SCALE,
              "analytic_tail": tail, "roots": results,
              "total_nodes": sum(x["nodes"] for x in results),
              "total_variance_leaves": sum(x["variance_leaves"] for x in results),
              "total_empty_leaves": sum(x["empty_leaves"] for x in results)}
    if args.certificate:
        args.certificate.parent.mkdir(parents=True, exist_ok=True)
        args.certificate.write_text(json.dumps({"report": report, "trees": trees},
                                               separators=(",", ":"))+"\n")
    print(json.dumps(report, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
