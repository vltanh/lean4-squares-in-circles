#!/usr/bin/env python3
"""Exact finite certificate for the radial-C/vertical-endpoint exclusion.

The certificate is a complete closed-rectangle subdivision, not a root search.
No floating-point values or optimizer results are used.
"""
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import argparse
import json
import re

ROOT = Path(__file__).resolve().parent
CERT = ROOT / "radial_vertical_source_exclusion.json"
NOTE = ROOT / "RADIAL_VERTICAL_SOURCE_EXCLUSION.md"
SCALE = 10**9


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __init__(self, lo, hi=None):
        object.__setattr__(self, "lo", F(lo))
        object.__setattr__(self, "hi", F(lo if hi is None else hi))
        if self.lo > self.hi:
            raise ValueError("Empty interval")

    @staticmethod
    def cast(value):
        return value if isinstance(value, Interval) else Interval(value)

    def __add__(self, other):
        other = self.cast(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        other = self.cast(other)
        values = [a * b for a in (self.lo, self.hi)
                  for b in (other.lo, other.hi)]
        return Interval(min(values), max(values))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.cast(other)
        if other.lo <= 0:
            raise ValueError("Divisor must be strictly positive")
        return self * Interval(1 / other.hi, 1 / other.lo)

    def __rtruediv__(self, other):
        return self.cast(other) / self


D = Interval(F(140, 99), F(99, 70))
INITIAL_X = Interval(0, F(5, 12))
INITIAL_Y = Interval(F(1, 5), F(5, 12))


def split(x, y):
    """Bisect the longer interval, choosing x in a tie; retain both endpoints."""
    if x.hi - x.lo >= y.hi - y.lo:
        mid = (x.lo + x.hi) / 2
        return ((Interval(x.lo, mid), y), (Interval(mid, x.hi), y))
    mid = (y.lo + y.hi) / 2
    return ((x, Interval(y.lo, mid)), (x, Interval(mid, y.hi)))


def witness(x, y):
    if x.lo >= y.hi:
        return "N", x.lo - y.hi
    a = (1 - x*x) / (1 + x*x)
    b = 2*x / (1 + x*x)
    s = (1 - y*y) / (1 + y*y)
    r = 2*y / (1 + y*y)
    if r.lo >= s.hi:
        return "S", r.lo - s.hi
    alpha = r + a - D
    if alpha.hi < 0:
        return "A", -alpha.hi
    u0 = 1 + D - r - a/2
    w0 = 2 + b/2
    den_a = 2*(w0*a + 1 - u0*b)
    if den_a.lo <= 0:
        return None
    la = (u0*u0 + w0*w0 - F(5, 4)) / den_a
    if la.hi < F(9, 10):
        return "L-", F(9, 10) - la.hi
    if la.lo > F(17, 16):
        return "L+", la.lo - F(17, 16)
    lb = ((2 + 2*(r+s) + a*(1+r) - b*(1+s)) /
          (2*(1 + b*(1+r) + a*(1+s))))
    if lb.hi < F(9, 10):
        return "B-", F(9, 10) - lb.hi
    if lb.lo > F(17, 16):
        return "B+", lb.lo - F(17, 16)
    gap = la - lb
    if gap.lo > 0:
        return "G+", gap.lo
    if gap.hi < 0:
        return "G-", -gap.hi
    length = Interval(max(la.lo, lb.lo, F(9, 10)),
                      min(la.hi, lb.hi, F(17, 16)))
    u = u0 + length*b
    ha = w0 - length*a
    v = 1 + r + a/2 - length*b
    hb = 1 + s - length*a - b/2
    if ha.hi <= F(1, 2):
        return "H-A", F(1, 2) - ha.hi
    if hb.hi <= F(1, 2):
        return "H-B", F(1, 2) - hb.hi
    if u.hi < F(4, 3):
        return "U", F(4, 3) - u.hi
    if v.hi < F(4, 3):
        return "V", F(4, 3) - v.hi
    offset = length*b + a/2
    torque = (u*hb - ha*offset)*(v*s - hb*r) - u*hb*(s-r)
    if torque.lo > 0:
        return "T", torque.lo
    return None


def build():
    leaves = []
    stack = [("", INITIAL_X, INITIAL_Y)]
    while stack:
        path, x, y = stack.pop()
        result = witness(x, y)
        if result is not None:
            rule, margin = result
            lower = (margin*SCALE).__floor__()
            if rule not in ("N", "S", "H-A", "H-B") and lower <= 0:
                raise ValueError("Printed positive margin too coarse")
            leaves.append({"path": path, "rule": rule, "margin": lower})
            continue
        if len(path) >= 20:
            raise ValueError("Unresolved cell: " + path)
        left, right = split(x, y)
        stack.append((path + "1", *right))
        stack.append((path + "0", *left))
    return {"schema_version": 1, "scale": SCALE,
            "x": ["0", "5/12"], "y": ["1/5", "5/12"],
            "sqrt2": ["140/99", "99/70"],
            "split": "bisect longer interval; x in a tie; closed children",
            "leaves": leaves}


def validate(data):
    if {k: v for k, v in data.items() if k != "leaves"} != {
        k: v for k, v in build_header().items() if k != "leaves"
    }:
        raise ValueError("Unexpected certificate conventions")
    leaves = data["leaves"]
    paths = {row["path"]: row for row in leaves}
    if len(paths) != len(leaves):
        raise ValueError("Duplicate path")
    seen = set()

    def visit(path, x, y):
        if path in paths:
            seen.add(path)
            row = paths[path]
            result = witness(x, y)
            if result is None or row["rule"] != result[0]:
                raise ValueError("Invalid witness at " + path)
            if row["margin"] != (result[1]*SCALE).__floor__():
                raise ValueError("Incorrect printed margin at " + path)
            return
        if not any(p.startswith(path) for p in paths):
            raise ValueError("Uncovered cell: " + path)
        left, right = split(x, y)
        visit(path + "0", *left)
        visit(path + "1", *right)

    visit("", INITIAL_X, INITIAL_Y)
    if seen != set(paths):
        raise ValueError("Unreachable or prefix-overlapping leaf")
    assert F(140, 99)**2 < 2 < F(99, 70)**2
    assert sum((F(1, 2**len(p)) for p in paths), F(0)) == 1
    return Counter(row["rule"] for row in leaves)


def build_header():
    return {"schema_version": 1, "scale": SCALE,
            "x": ["0", "5/12"], "y": ["1/5", "5/12"],
            "sqrt2": ["140/99", "99/70"],
            "split": "bisect longer interval; x in a tie; closed children"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-certificate", action="store_true")
    parser.add_argument("--print-table", action="store_true")
    args = parser.parse_args()
    if args.write_certificate:
        data = build()
        validate(data)
        CERT.write_text(json.dumps(data, indent=2) + "\n")
    data = json.loads(CERT.read_text())
    counts = validate(data)
    rows = [(i, row["path"], row["rule"], row["margin"])
            for i, row in enumerate(data["leaves"])]
    if args.print_table:
        print("| Row | Closed-cell path | Rejection | Margin / 10^9 |")
        print("| ---: | --- | --- | ---: |")
        for i, path, rule, margin in rows:
            print(f"| {i} | `{path}` | {rule} | {margin} |")
        return
    pattern = re.compile(r"^\| (\d+) \| `([01]+)` \| ([A-Z+-]+) \| (\d+) \|$")
    actual = []
    for line in NOTE.read_text().splitlines():
        match = pattern.fullmatch(line)
        if match:
            i, path, rule, margin = match.groups()
            actual.append((int(i), path, rule, int(margin)))
    if actual != rows:
        raise ValueError("Printed certificate differs from the verified cells")
    print(f"PASS: {len(rows)} exact leaves, full closed-rectangle coverage, no unresolved cells.")
    print("Rejections:", dict(counts))
    print("Maximum depth:", max(len(row[1]) for row in rows))


if __name__ == "__main__":
    main()
