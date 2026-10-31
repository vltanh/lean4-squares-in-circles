#!/usr/bin/env python3
"""Exact upper-bound check for ten axis-parallel unit squares.

Uses only Python's standard library and Fraction arithmetic. Vertex containment
implies square containment by convexity of the disk. Two axis-parallel open unit
squares are disjoint exactly when a coordinate gap between their centers is at
least one. This checks a construction, not an unrestricted lower bound or a Lean
proof. Run with --self-test to also exercise rejection of corrupted witnesses.
"""

import argparse
import copy
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path
import re
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fields(value, expected, label):
    require(isinstance(value, dict), f"{label}: expected an object")
    require(set(value) == set(expected), f"{label}: unexpected or missing fields")


def rational(value):
    require(isinstance(value, str), "coordinates and lengths must be rational strings")
    require(re.fullmatch(r"-?\d+(?:/[1-9]\d*)?", value) is not None,
            f"invalid rational string: {value!r}")
    return Fraction(value)


def point(value):
    require(isinstance(value, list) and len(value) == 2, "expected two coordinates")
    return tuple(map(rational, value))


def check(data):
    fields(data, ("version", "unit_side", "orientation", "disk", "squares"), "witness")
    require(type(data["version"]) is int and data["version"] == 1,
            "unsupported witness version")
    require(rational(data["unit_side"]) == 1, "expected unit squares")
    require(data["orientation"] == "axis_parallel", "expected axis-parallel squares")
    fields(data["disk"], ("center", "radius_squared"), "disk")
    origin = point(data["disk"]["center"])
    q = rational(data["disk"]["radius_squared"])
    require(origin == (0, 0), "expected disk center at the origin")
    require(q == Fraction(9, 2), "expected squared radius 9/2")
    require(isinstance(data["squares"], list) and len(data["squares"]) == 10,
            "expected exactly ten squares")
    squares = []
    for square in data["squares"]:
        fields(square, ("id", "center"), "square")
        require(isinstance(square["id"], str) and square["id"], "expected a square ID")
        squares.append((square["id"], point(square["center"])))
    require(len({name for name, _ in squares}) == 10, "square IDs must be distinct")

    tight = []
    vertex_count = 0
    half = Fraction(1, 2)
    for name, (x, y) in squares:
        for dx, dy in product((-half, half), repeat=2):
            vx, vy = x + dx, y + dy
            norm_sq = (vx - origin[0]) ** 2 + (vy - origin[1]) ** 2
            require(norm_sq <= q, f"{name}: vertex ({vx}, {vy}) is outside the disk")
            vertex_count += 1
            if norm_sq == q:
                tight.append(f"{name}: ({vx}, {vy})")

    pair_count = 0
    for (name_a, (ax, ay)), (name_b, (bx, by)) in combinations(squares, 2):
        require(abs(ax - bx) >= 1 or abs(ay - by) >= 1,
                f"{name_a}, {name_b}: interiors overlap")
        pair_count += 1
    require(tight, "expected at least one vertex attaining the advertised radius")
    return vertex_count, pair_count, tight


def self_test(data):
    """Mutations test the failure paths; none are used as proof premises."""
    cases = []
    overlap = copy.deepcopy(data)
    overlap["squares"][1]["center"] = overlap["squares"][0]["center"][:]
    cases.append(("overlap", overlap, "interiors overlap"))
    outside = copy.deepcopy(data)
    outside["squares"][0]["center"] = ["-2", "-1"]
    cases.append(("outside vertex", outside, "outside the disk"))
    rounded = copy.deepcopy(data)
    rounded["squares"][0]["center"][0] = -1.0
    cases.append(("floating-point coordinate", rounded, "rational strings"))
    for label, mutated, expected in cases:
        try:
            check(mutated)
        except ValueError as error:
            require(expected in str(error), f"{label}: failed for an unexpected reason: {error}")
        else:
            raise ValueError(f"{label}: corrupted witness was accepted")
    return len(cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witness", nargs="?", type=Path,
                        default=Path(__file__).with_name("construction.json"))
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    try:
        data = json.loads(args.witness.read_text(encoding="utf-8"))
        vertices, pairs, tight = check(data)
        tests = self_test(data) if args.self_test else 0
    except (OSError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print("PASS: ten axis-parallel unit squares, disk center (0, 0), squared radius 9/2")
    print(f"Contained vertices: {vertices}/40; interior-disjoint pairs: {pairs}/45")
    print(f"Tight vertices: {len(tight)}")
    for vertex in tight:
        print(f"  {vertex}")
    if args.self_test:
        print(f"Rejection self-tests: {tests}/{tests}")
    print("Scope: construction upper bound only; no global optimality or Lean verification.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
