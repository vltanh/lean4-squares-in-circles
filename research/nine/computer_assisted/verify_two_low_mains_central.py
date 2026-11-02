#!/usr/bin/env python3
"""Independent exact replay of the two-low-mains central exclusion cover.

Standard library only. The certificate producer uses Fraction intervals;
this verifier independently reconstructs each complete box and uses outward
64-bit integer dyadic arithmetic. No producer/evaluator is imported.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import hashlib
import json
import sys
import time

BITS = 64
SCALE = 1 << BITS
DIM = 4


def ceil_ratio(a, b):
    assert b > 0
    return -((-a) // b)


class I:
    """Closed interval; lo and hi are integer numerators over SCALE."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if isinstance(lo, I):
            assert hi is None
            self.lo, self.hi = lo.lo, lo.hi
        elif isinstance(lo, int) and (hi is None or isinstance(hi, int)):
            self.lo = lo * SCALE
            self.hi = (lo if hi is None else hi) * SCALE
        else:
            low = F(lo)
            high = low if hi is None else F(hi)
            self.lo = low.numerator * SCALE // low.denominator
            self.hi = ceil_ratio(high.numerator * SCALE, high.denominator)
        assert self.lo <= self.hi

    @classmethod
    def raw(cls, lo, hi):
        assert isinstance(lo, int) and isinstance(hi, int) and lo <= hi
        answer = object.__new__(cls)
        answer.lo, answer.hi = lo, hi
        return answer

    def __add__(self, other):
        if isinstance(other, int):
            n = other * SCALE
            return I.raw(self.lo + n, self.hi + n)
        other = other if isinstance(other, I) else I(other)
        return I.raw(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I.raw(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -(other if isinstance(other, I) else I(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if isinstance(other, int):
            a, b = self.lo * other, self.hi * other
            return I.raw(min(a, b), max(a, b))
        other = other if isinstance(other, I) else I(other)
        if self.lo == self.hi == 0 or other.lo == other.hi == 0:
            return I.raw(0, 0)
        candidates = (
            self.lo * other.lo, self.lo * other.hi,
            self.hi * other.lo, self.hi * other.hi,
        )
        return I.raw(min(candidates) // SCALE,
                     ceil_ratio(max(candidates), SCALE))

    __rmul__ = __mul__

    def __truediv__(self, other):
        if isinstance(other, int):
            assert other != 0
            if other < 0:
                return (-self) / (-other)
            return I.raw(self.lo // other, ceil_ratio(self.hi, other))
        other = other if isinstance(other, I) else I(other)
        assert other.lo > 0 or other.hi < 0
        if other.hi < 0:
            return (-self) / (-other)
        numerators = (self.lo * SCALE, self.hi * SCALE)
        low = min(a // b for a in numerators for b in (other.lo, other.hi))
        high = max(ceil_ratio(a, b) for a in numerators for b in (other.lo, other.hi))
        return I.raw(low, high)

    def __rtruediv__(self, other):
        return I(other) / self

    def sq(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        high = max(self.lo**2, self.hi**2)
        return I.raw(low // SCALE, ceil_ratio(high, SCALE))

    def abs(self):
        low = 0 if self.lo <= 0 <= self.hi else min(abs(self.lo), abs(self.hi))
        return I.raw(low, max(abs(self.lo), abs(self.hi)))

    def sqrt(self):
        assert self.lo >= 0
        low = isqrt(self.lo * SCALE)
        radicand = self.hi * SCALE
        high = isqrt(radicand)
        if high**2 < radicand:
            high += 1
        return I.raw(low, high)

    def fractions(self):
        return F(self.lo, SCALE), F(self.hi, SCALE)


ROOT = ((F(1, 3), F(29, 60)), (F(0), F(1)))


def lower_minimum(left, right):
    return I.raw(min(left.lo, right.lo), min(left.hi, right.hi))


def check_leaf(box, tag):
    x = I(*box[0])
    tau = I(*box[1])
    norm = (I(1) + tau * tau).sqrt()
    a, b = I(1)/norm, tau/norm
    h, k = (a+b)/2, (a-b)/2
    y_cap = lower_minimum(
        (I(F(1105, 256))-(x+h).sq()).sqrt()-k,
        (I(F(1105, 256))-(x-k).sq()).sqrt()-h)
    y_cap = lower_minimum(y_cap, I(F(91, 60)))
    g = I(F(15, 31))
    if tag == "right_circle":
        side_clearance = (I(F(1, 2)) + b*(g+x-F(31, 60)))/a
        y_min = I(F(119, 310)) + g + lower_minimum(h, side_clearance)
        reserve = y_min.lo-y_cap.hi
    elif tag == "left_axes":
        horizontal = x+F(31, 60)-g
        vertical = y_cap-F(3, 5)-g
        alternatives = (
            horizontal-h,
            vertical-h,
            horizontal*a+vertical*b-F(1, 2),
            horizontal*b+vertical*a-F(1, 2),
        )
        reserve = -max(v.hi for v in alternatives)
    else:
        raise AssertionError(("unknown leaf rule", tag))
    assert reserve > 0, (tag, box, F(reserve, SCALE))
    return F(reserve, SCALE)


def main():
    start = time.monotonic()
    path = Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name("two_low_mains_central_cover.json")
    raw = path.read_bytes()
    cert = json.loads(raw)
    assert cert["root"] == [[str(a), str(b)] for a, b in ROOT]
    assert cert["coordinates"] == ["x", "unsigned tangent"]
    nodes = cert["tree"]
    visited, counts, reserves = set(), {}, []
    maxdepth = 0
    def walk(index, box, depth):
        nonlocal maxdepth
        assert isinstance(index, int) and 0 <= index < len(nodes)
        assert index not in visited
        visited.add(index)
        maxdepth = max(maxdepth, depth)
        node = nodes[index]
        if "tag" in node:
            assert set(node) == {"tag", "reserve"}
            reserves.append(check_leaf(box, node["tag"]))
            counts[node["tag"]] = counts.get(node["tag"], 0)+1
            return
        assert set(node) == {"axis", "children"}
        axis, children = node["axis"], node["children"]
        assert axis in (0, 1) and len(children) == 2
        lo, hi = box[axis]
        mid = (lo+hi)/2
        left, right = list(box), list(box)
        left[axis], right[axis] = (lo, mid), (mid, hi)
        walk(children[0], tuple(left), depth+1)
        walk(children[1], tuple(right), depth+1)
    walk(0, ROOT, 0)
    assert len(visited) == len(nodes)
    assert len(nodes) == 2*len(reserves)-1
    assert counts == cert["counts"]
    print(json.dumps({
        "result": "PASS",
        "theorem": cert["theorem"],
        "certificate": path.name,
        "certificate_sha256": hashlib.sha256(raw).hexdigest(),
        "root": cert["root"],
        "nodes": len(nodes),
        "leaves": len(reserves),
        "max_depth": maxdepth,
        "counts": counts,
        "least_positive_reserve": str(min(reserves)),
        "arithmetic": "outward 64-bit integer dyadic intervals; no producer imports or floating point acceptance",
        "seconds": time.monotonic()-start,
    }, indent=2))


if __name__ == "__main__":
    main()
