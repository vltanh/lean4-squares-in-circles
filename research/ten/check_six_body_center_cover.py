#!/usr/bin/env python3
"""Check the printed conditional six-center cover using rational arithmetic.

This verifies a fixed cover, not a search or a claim that every LSLSLD
component satisfies its center-region hypotheses.
"""
from fractions import Fraction as F
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def clip(poly, normal, bound):
    """Intersect a convex polygon with a closed rational half-plane."""
    out = []
    for a, b in zip(poly, poly[1:]+poly[:1]):
        da = bound-normal[0]*a[0]-normal[1]*a[1]
        db = bound-normal[0]*b[0]-normal[1]*b[1]
        if da >= 0:
            out.append(a)
        if (da < 0 < db) or (db < 0 < da):
            t = da/(da-db)
            out.append((a[0]+t*(b[0]-a[0]), a[1]+t*(b[1]-a[1])))
    return out


def cell_box(path, radius):
    x0, x1, y0, y1 = -radius, radius, -radius, radius
    for char in path:
        if char not in '0123':
            raise ValueError('Invalid quadrant path')
        xm, ym = (x0+x1)/2, (y0+y1)/2
        if char in '02':
            x1 = xm
        else:
            x0 = xm
        if char in '01':
            y1 = ym
        else:
            y0 = ym
    return x0, x1, y0, y1


def complete_tree(paths, prefix=''):
    """Verify that the listed leaves form a full four-way subdivision."""
    if prefix in paths:
        if any(p.startswith(prefix) and p != prefix for p in paths):
            raise ValueError('A leaf has a descendant')
        return
    if not any(p.startswith(prefix) for p in paths):
        raise ValueError('Uncovered quadrant: '+prefix)
    for char in '0123':
        complete_tree(paths, prefix+char)


def main():
    data = json.loads((ROOT/'six_body_center_cover.json').read_text())
    radius = F(data['center_disk_radius'])
    assert radius == F(3, 2)
    assert F(data['containing_squared_radius_upper_bound']) == F(17, 4)
    regions = {r['name']: [tuple(map(F, p)) for p in r['vertices']]
               for r in data['center_regions']}
    assert len(regions) == len(data['center_regions']) == 6
    halfplanes = [(tuple(row['normal']), F(row['bound']))
                  for row in data['outer_halfplanes']]
    assert len(halfplanes) == len(set(halfplanes)) == 32
    for normal, bound in halfplanes:
        assert any(normal) and bound > 0
        assert bound**2 >= radius**2*sum(t*t for t in normal)
    paths = {row['path'] for row in data['cells']}
    assert len(paths) == len(data['cells']) == 64
    markdown = (ROOT/'SIX_BODY_CENTER_COVER.md').read_text()
    marker = '<!-- SIX_BODY_CENTER_COVER_TABLE -->'
    assert markdown.count(marker) == 1
    printed_rows = [line for line in markdown.split(marker)[1].splitlines()
                    if line.startswith('| `')]
    expected_rows = [
        '| `'+row['path']+'` | '+(row['region'] or 'EMPTY')+' | '
        +('`'+row['maximum_squared_distance']+'`' if row['maximum_squared_distance'] else '—')+' |'
        for row in data['cells']
    ]
    assert printed_rows == expected_rows
    complete_tree(paths)
    largest = F(0)
    empty = 0
    for row in data['cells']:
        x0, x1, y0, y1 = cell_box(row['path'], radius)
        poly = [(x0,y0),(x1,y0),(x1,y1),(x0,y1)]
        for normal, bound in halfplanes:
            poly = clip(poly, normal, bound)
            if not poly:
                break
        if row['region'] is None:
            assert not poly and row['maximum_squared_distance'] is None
            empty += 1
            continue
        assert poly
        region = regions[row['region']]
        actual = max(sum((p[j]-c[j])**2 for j in range(2))
                     for p in poly for c in region)
        printed = F(row['maximum_squared_distance'])
        assert actual == printed < 1, row['path']
        largest = max(largest, printed)
    assert empty == 4
    assert largest == F(10193149, 10240000)
    print('PASS: 64 cells form a complete rational cover; four are empty.')
    print(f'All printed distance bounds agree exactly; largest = {largest} < 1.')
    print('Conditional six-center obstruction only; no whole cycle entry is closed.')


if __name__ == '__main__':
    main()
