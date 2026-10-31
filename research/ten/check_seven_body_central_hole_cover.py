#!/usr/bin/env python3
"""Verify the rational seven-center localization cover, without optimization."""

from fractions import Fraction as F
import json
from pathlib import Path

from check_six_body_center_cover import clip

ROOT = Path(__file__).resolve().parent


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def main():
    data = json.loads((ROOT / "seven_body_central_hole_cover.json").read_text())
    radius = F(data["center_disk_radius"])
    assert radius == F(25, 16)
    regions = {k: [tuple(map(F, v)) for v in vs] for k, vs in data["regions"].items()}
    expected_boxes = {"A": (-155, -154, -16, -15), "B": (154, 155, -16, -15),
                      "C": (-1, 1, 140, 142), "U": (-50, -50, -100, -100),
                      "V": (50, 50, -100, -100), "S": (-75, -74, 74, 75),
                      "T": (74, 75, 74, 75)}
    assert regions == {k: [(F(x, 100), F(y, 100)) for x in (x0, x1) for y in (y0, y1)]
                       for k, (x0, x1, y0, y1) in expected_boxes.items()}
    midpoints = {k: tuple(map(F, v)) for k, v in data["midpoints"].items()}
    assert midpoints == {k: tuple(sum(v[j] for v in vs) / 4 for j in (0, 1))
                         for k, vs in regions.items()}
    halfplanes = [(tuple(v["normal"]), F(v["bound"])) for v in data["outer_halfplanes"]]
    assert len(halfplanes) == len(set(halfplanes)) == 32
    for normal, bound in halfplanes:
        assert bound > 0 and bound * bound >= radius * radius * dot(normal, normal)
    outside = [(tuple(v["normal"]), F(v["bound"])) for v in data["outside_box_halfplanes"]]
    assert outside == [((1, 0), F(1, 5)), ((-1, 0), F(1, 5)),
                       ((0, 1), F(1, 10)), ((0, -1), F(1, 5))]
    rows = data["cells"]
    assert len(rows) == 28
    assert [(r["region"], r["outside"]) for r in rows] == [(k, i) for k in regions for i in range(4)]
    markdown = (ROOT / "SEVEN_BODY_CENTRAL_HOLE_EXCLUSION.md").read_text()
    marker = "<!-- SEVEN_BODY_CENTRAL_HOLE_TABLE -->"
    assert markdown.count(marker) == 1
    printed = [s for s in markdown.split(marker)[1].splitlines() if s.startswith("| `")]
    labels = ["east", "west", "north", "south"]
    expected = ["| `" + r["region"] + "` | " + labels[r["outside"]] + " | "
                + ("`" + r["maximum_squared_distance"] + "`" if r["maximum_squared_distance"] else "EMPTY")
                + " |" for r in rows]
    assert printed == expected
    largest = F(0)
    empty = 0
    for row in rows:
        center = midpoints[row["region"]]
        poly = [(-radius, -radius), (radius, -radius), (radius, radius), (-radius, radius)]
        for normal, bound in halfplanes:
            poly = clip(poly, normal, bound)
        for other, point in midpoints.items():
            if other != row["region"]:
                normal = tuple(2 * (point[j] - center[j]) for j in (0, 1))
                poly = clip(poly, normal, dot(point, point) - dot(center, center))
        normal, bound = outside[row["outside"]]
        poly = clip(poly, tuple(-v for v in normal), -bound)
        if not poly:
            assert row["maximum_squared_distance"] is None
            empty += 1
            continue
        actual = max(sum((v[j] - c[j]) ** 2 for j in (0, 1))
                     for v in poly for c in regions[row["region"]])
        assert actual == F(row["maximum_squared_distance"]) < 1
        largest = max(largest, actual)
    assert largest == F(197, 200)
    print(f"PASS: 28 rational Voronoi/exterior cells; {empty} empty; maximum = {largest} < 1.")
    print("This localizes every possible eighth center inside (−1/5,1/5) × (−1/5,1/10).")
    print("The separate elementary orientation argument excludes that central hole.")
    print("Conditional geometric theorem only; no whole signature is closed.")


if __name__ == "__main__":
    main()
