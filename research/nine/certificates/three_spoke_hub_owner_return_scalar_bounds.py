#!/usr/bin/env python3
"""Exact complete interval certificate for the H3 hub-owner return scalars.

All interval endpoints are integers divided by 2**48. Every operation
rounds outward using integer division or isqrt. No floating-point value
or sampled input is used. The optional leaf file records the entire
finite binary cover for a separate implementation to replay.
"""

from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path

SCALE = 1 << 48


def ceil_div(n, d):
    assert d > 0
    return -((-n) // d)


class Interval:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = lo
        self.hi = lo if hi is None else hi
        assert isinstance(self.lo, int) and isinstance(self.hi, int)
        assert self.lo <= self.hi

    @classmethod
    def rational(cls, n, d=1):
        return cls(n * SCALE // d, ceil_div(n * SCALE, d))

    def __add__(self, other):
        if not isinstance(other, Interval):
            other = Interval.rational(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if not isinstance(other, Interval):
            other = Interval.rational(other)
        products = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Interval(min(products) // SCALE,
                        ceil_div(max(products), SCALE))

    __rmul__ = __mul__

    def __truediv__(self, other):
        if not isinstance(other, Interval):
            other = Interval.rational(other)
        if other.lo <= 0:
            raise ZeroDivisionError("positive denominator not yet certified")
        quotients = [(x * SCALE, y)
                     for x in (self.lo, self.hi)
                     for y in (other.lo, other.hi)]
        return Interval(min(n // d for n, d in quotients),
                        max(ceil_div(n, d) for n, d in quotients))

    def square(self):
        low = (0 if self.lo <= 0 <= self.hi
               else min(self.lo * self.lo, self.hi * self.hi))
        high = max(self.lo * self.lo, self.hi * self.hi)
        return Interval(low // SCALE, ceil_div(high, SCALE))

    def sqrt(self):
        assert self.lo >= 0
        low = isqrt(self.lo * SCALE)
        high = isqrt(self.hi * SCALE)
        if high * high < self.hi * SCALE:
            high += 1
        return Interval(low, high)

    def intersect(self, other):
        return Interval(max(self.lo, other.lo), min(self.hi, other.hi))


# This closed integer box contains (19/100,5/12) x (0,1).
ROOT = (Interval.rational(19, 100).lo,
        Interval.rational(5, 12).hi,
        0, SCALE)
ROOT_Z_WIDTH = ROOT[1] - ROOT[0]
ROOT_P_WIDTH = SCALE
ONE_THIRD = Interval.rational(1, 3)
ONE_EIGHTH = Interval.rational(1, 8)
THREE_FIFTHS = Interval.rational(3, 5)


def evaluate(box):
    """Return a rigorous exclusion, all four positive margins, or split."""
    zl, zh, pl, ph = box
    z, p = Interval(zl, zh), Interval(pl, ph)
    z2 = z.square()
    denominator = 1 + z2
    a = (1 - z2) / denominator
    b = 2 * z / denominator

    if (a - b).hi <= 0:
        return "empty", "a_gt_b", None
    p0 = (a - b) / (a + b)
    if (p - p0).hi <= 0:
        return "empty", "p_gt_p0", None
    if (b / a - p).hi <= 0:
        return "empty", "p_lt_b_a", None

    H = b + a * p
    t = 1 - H
    if t.hi <= 0:
        return "empty", "t_positive", None
    x = 1 - (b / a) * (1 + p)
    if x.hi <= 0:
        return "empty", "x_positive", None
    denominator_v = 1 - p * H
    if denominator_v.hi <= 0:
        return "empty", "denv_positive", None
    if denominator_v.lo <= 0:
        return "split", "denominator", None

    # The strict actual guards t>0 and x>0 justify these intersections.
    # Retaining their zero endpoints enlarges the actual domain.
    t = Interval(max(t.lo, 0), t.hi)
    x = Interval(max(x.lo, 0), x.hi)
    v = t / denominator_v
    y0 = a - t
    E = (1 + x.square()).sqrt()
    L = (1 + v.square()).sqrt()
    g = (x + v) / (E * L)
    h = (1 - x * v) / (E * L)
    A0 = (1 + b + x * y0) / E
    B0 = (x * (1 + b) - y0) / E

    k1 = 1 - A0 + g
    if k1.hi <= 0:
        return "empty", "k1_positive", None
    d1 = 1 - B0 - h

    # These three expressions are algebraically identical. Their
    # intersection is an enclosure, not an independent parameter choice.
    F1 = g.square() - g + B0 * g + h * (A0 - 1)
    F2 = (1 + b - v * y0) / L - h - g + g.square()
    F3 = (1 + b - v * y0) / L - h - g + 1 - h.square()
    F = F1.intersect(F2).intersect(F3)
    margins = (d1 - ONE_THIRD, ONE_EIGHTH - k1,
               h - THREE_FIFTHS, F)
    if all(value.lo > 0 for value in margins):
        return "pass", "all", tuple(value.lo for value in margins)
    return "split", "bounds", None


def prove(record_leaves=False):
    stack = [(ROOT, "", 0)]
    counts = Counter()
    minimum_margins = [10**50] * 4
    maximum_depth = 0
    visits = 0
    digest = sha256()
    leaves = []
    while stack:
        box, path, depth = stack.pop()
        visits += 1
        maximum_depth = max(maximum_depth, depth)
        kind, reason, values = evaluate(box)
        if kind == "pass":
            counts["pass"] += 1
            minimum_margins = [min(x, y)
                               for x, y in zip(minimum_margins, values)]
            digest.update(f"{path}:pass:{values}\n".encode())
        elif kind == "empty":
            counts["empty_" + reason] += 1
            digest.update(f"{path}:empty:{reason}\n".encode())
        else:
            # This is a failure guard, never an acceptance criterion.
            if depth >= 45:
                raise RuntimeError(("unresolved box", box, path, reason))
            counts["split"] += 1
            zl, zh, pl, ph = box
            if (zh-zl)*ROOT_P_WIDTH >= (ph-pl)*ROOT_Z_WIDTH:
                middle = (zl+zh)//2
                assert zl < middle < zh
                lower = (zl, middle, pl, ph)
                upper = (middle, zh, pl, ph)
            else:
                middle = (pl+ph)//2
                assert pl < middle < ph
                lower = (zl, zh, pl, middle)
                upper = (zl, zh, middle, ph)
            stack.append((upper, path+"1", depth+1))
            stack.append((lower, path+"0", depth+1))
            continue
        if record_leaves:
            leaves.append({"path": path, "box": box, "kind": kind,
                           "reason": reason, "scaled_margins": values})

    terminal_count = sum(v for key, v in counts.items() if key != "split")
    assert terminal_count == counts["split"] + 1
    assert visits == 2*counts["split"] + 1
    result = {"scale": SCALE, "root": ROOT, "counts": dict(counts),
              "visits": visits, "terminal_boxes": terminal_count,
              "max_depth": maximum_depth,
              "minimum_scaled_margins": minimum_margins,
              "tree_digest": digest.hexdigest()}
    return result, leaves


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--leaf-output", type=Path)
    args = parser.parse_args()
    result, leaves = prove(args.leaf_output is not None)
    if args.leaf_output is not None:
        args.leaf_output.write_text(json.dumps(
            {"certificate": result, "leaves": leaves}, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
