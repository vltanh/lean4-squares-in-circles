#!/usr/bin/env python3
"""Render the checked rational witness as a deterministic SVG.

Floating point is used only for drawing. check_construction.py supplies the
separate exact arithmetic check; the picture is not a proof certificate.
"""

import argparse
from fractions import Fraction
from html import escape
import json
from math import sqrt
from pathlib import Path
import xml.etree.ElementTree as ET

from check_construction import check


def render(data):
    check(data)
    scale, cx, cy = 110, 320, 315
    q = Fraction(data["disk"]["radius_squared"])
    radius = scale * sqrt(float(q))
    parts = [
        '<svg xmlns="http://www.w3.org/2000/svg" width="640" height="650" '
        'viewBox="0 0 640 650" role="img" aria-labelledby="title description">',
        '<title id="title">Ten unit squares in a circle: a 3 + 4 + 3 construction</title>',
        '<desc id="description">Three axis-parallel unit squares in each outer column '
        'and four in the middle column fit in a disk of radius three divided by '
        'the square root of two. Four outer vertices touch the circle. This is an '
        'upper-bound construction, not an optimality claim.</desc>',
        '<rect width="640" height="650" fill="white"/>',
        '<g font-family="sans-serif" text-anchor="middle" fill="#18242e">',
        '<text x="320" y="35" font-size="23" font-weight="600">'
        'Ten unit squares: 3 + 4 + 3</text>',
        f'<circle cx="{cx}" cy="{cy}" r="{radius:.6f}" '
        'fill="#f4f8fa" stroke="#3e667d" stroke-width="2.5"/>',
    ]
    for square in data["squares"]:
        x, y = map(Fraction, square["center"])
        px = cx + scale * float(x)
        py = cy - scale * float(y)
        fill = "#d9e9df" if x == 0 else "#dce8f2"
        parts.append(
            f'<rect x="{px-scale/2:.6f}" y="{py-scale/2:.6f}" '
            f'width="{scale}" height="{scale}" fill="{fill}" '
            'stroke="#243c4a" stroke-width="1.5"/>'
        )
        parts.append(
            f'<text x="{px:.6f}" y="{py+6:.6f}" font-size="18">'
            f'{escape(square["id"])}</text>'
        )
    tight = set()
    half = Fraction(1, 2)
    for square in data["squares"]:
        x, y = map(Fraction, square["center"])
        for dx in (-half, half):
            for dy in (-half, half):
                vx, vy = x + dx, y + dy
                if vx * vx + vy * vy == q:
                    tight.add((vx, vy))
    for x, y in sorted(tight):
        parts.append(
            f'<circle cx="{cx+scale*float(x):.6f}" '
            f'cy="{cy-scale*float(y):.6f}" r="4" fill="#ad492c"/>'
        )
    parts.extend([
        '<text x="320" y="590" font-size="20">R = 3/√2 — construction upper bound</text>',
        '<text x="320" y="618" font-size="13">'
        'Exact witness: construction.json · Exact check: check_construction.py</text>',
        '</g>',
        '</svg>',
    ])
    svg = "\n".join(parts) + "\n"
    ET.fromstring(svg)
    return svg


def main():
    folder = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--witness", type=Path, default=folder / "construction.json")
    parser.add_argument("--output", type=Path, default=folder / "construction.svg")
    args = parser.parse_args()
    data = json.loads(args.witness.read_text(encoding="utf-8"))
    args.output.write_text(render(data), encoding="utf-8")
    print(f"Wrote {args.output.name}; floating point used only for rendering.")


if __name__ == "__main__":
    main()
