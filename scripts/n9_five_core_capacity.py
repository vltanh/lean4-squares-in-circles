#!/usr/bin/env python3
"""Exact finite center-cover checker for a five-square capacity theorem.

This checks rational data, not arbitrary nine-square packings.  Its geometric
soundness and explicit vertex-neighborhood premise are proved in
research/nine/FIVE_CORE_ROBUST_CENTER_COVER_CAPACITY_EIGHT_2026_10_30.md.

No floating-point operations, numerical geometry library, external solver,
or sampled pose is used by the checker.  --regenerate constructs a new cover
using the same exact predicates, and then independently replays it.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import json
from math import lcm
from pathlib import Path

DEFAULT = (Path(__file__).resolve().parents[1] / "research/nine/certificates/"
           "d02_type_ii_a_only_five_core_capacity.json")
M = F(91, 60)
EPS = F(1, 25)
EAST = (F(13, 10), M, -F(1, 5), F(7, 10))
SOUTH = (-F(1), F(1, 4), -M, -F(3, 4))
GRID = 8
_PREPARED_COVER_CACHE = {}
_DYADIC_COVER_CACHE = {}


def profile(data):
    if data["version"] == 1:
        return EPS, GRID, {"east": EAST, "south": SOUTH}
    if data["version"] == 2:
        return F(2, 25), 16, {
            "east": (F(13, 10), M, F(0), F(3, 4)),
            "south_left": (-F(49, 50), -F(17, 50), -F(297, 200), -F(18, 25)),
            "south_right": (-F(7, 20), F(23, 100), -M, -F(18, 25)),
        }
    if data["version"] == 3:
        centers = ((F(10, 7), F(9, 25)),
                   (-F(29, 50), -F(21, 20)),
                   (-F(3, 25), -F(31, 25)))
        return F(3, 25), 16, {
            "ball" + str(i): {"center": center, "radius": F(12, 25)}
            for i, center in enumerate(centers)
        }
    if data["version"] == 4:
        epsilon = F(*map(int, data["vertex_error_bound"]))
        grid = data["witness_grid"]
        require(0 < epsilon < F(1, 2), "invalid rational perturbation bound")
        require(isinstance(grid, int) and 1 <= grid <= 64, "invalid witness grid")
        disks = data["capacity_disks"]
        require(isinstance(disks, list) and len(disks) == 3, "need exactly three capacity disks")
        caps = {}
        for i, disk in enumerate(disks):
            require(len(disk["center"]) == 2, "disk center needs two coordinates")
            center = tuple(F(*map(int, coordinate)) for coordinate in disk["center"])
            radius = F(*map(int, disk["radius"]))
            require(0 < radius < F(1, 2), "capacity disk must have diameter strictly below one")
            caps["ball" + str(i)] = {"center": center, "radius": radius}
        return epsilon, grid, caps
    raise ValueError("unknown certificate version")


def require(test: bool, description: str) -> None:
    if not test:
        raise ValueError(description)


def inside(box, cap) -> bool:
    return cap[0] <= box[0] <= box[1] <= cap[1] and cap[2] <= box[2] <= box[3] <= cap[3]


def cap_contains_box(box, cap) -> bool:
    if isinstance(cap, dict):
        return maximum_distance_squared(box, cap["center"]) <= cap["radius"] ** 2
    return inside(box, cap)


def cap_diameter_squared(cap):
    if isinstance(cap, dict):
        return 4 * cap["radius"] ** 2
    return (cap[1] - cap[0]) ** 2 + (cap[3] - cap[2]) ** 2


def split(box):
    xl, xh, yl, yh = box
    xm, ym = (xl + xh) / 2, (yl + yh) / 2
    return ((xl, xm, yl, ym), (xm, xh, yl, ym),
            (xl, xm, ym, yh), (xm, xh, ym, yh))


def minimum_norm_squared(box):
    xl, xh, yl, yh = box
    x, y = max(xl, F(0), -xh), max(yl, F(0), -yh)
    return x * x + y * y


def maximum_distance_squared(box, point):
    xl, xh, yl, yh = box
    px, py = point
    return max(abs(xl - px), abs(xh - px)) ** 2 + max(abs(yl - py), abs(yh - py)) ** 2


def references(data):
    epsilon, _, _ = profile(data)
    require(data["kind"] == "five_core_center_cover", "unknown certificate format")
    require(F(*map(int, data["center_bound"])) == M, "wrong center bound")
    require(F(*map(int, data["vertex_error_bound"])) == epsilon, "wrong vertex error bound")
    require(data["reference_names"] == ["V", "A", "D", "B", "C"], "wrong five-core labels")
    denominator = data["reference_denominator"]
    require(isinstance(denominator, int) and denominator > 0, "bad reference denominator")
    rows = data["reference_vertices"]
    require(len(rows) == 5 and all(len(row) == 4 for row in rows), "need four reference vertices per square")
    require(all(len(p) == 2 and all(isinstance(v, int) for v in p) for row in rows for p in row), "bad reference point")
    return [[tuple(F(v, denominator) for v in p) for p in row] for row in rows]


def witnesses(rows, grid=GRID):
    answer = {}
    for k, row in enumerate(rows):
        for i in range(grid + 1):
            for j in range(grid + 1):
                u, v = F(i, grid), F(j, grid)
                weights = ((1 - u) * (1 - v), u * (1 - v), u * v, (1 - u) * v)
                require(sum(weights) == 1 and min(weights) >= 0, "invalid convex weights")
                answer[k, i, j] = tuple(sum(w * p[d] for w, p in zip(weights, row)) for d in (0, 1))
    return answer


def verify(data):
    epsilon, grid, caps = profile(data)
    points = witnesses(references(data), grid)
    nodes = data["nodes"]
    require(isinstance(nodes, list) and nodes, "empty certificate")
    require(data["root"] == 0, "root must have index zero")
    seen, counts = set(), Counter()
    max_depth = 0
    min_core_reserve = None

    def walk(index, box, depth):
        nonlocal max_depth, min_core_reserve
        require(isinstance(index, int) and 0 <= index < len(nodes), "bad node index")
        require(index not in seen, "node reused or cycle in cover")
        seen.add(index)
        max_depth = max(max_depth, depth)
        node = nodes[index]
        require(isinstance(node, list) and node, "bad node")
        tag = node[0]
        counts[tag] += 1
        if tag == "split":
            require(len(node) == 5, "split must retain all four children")
            for child, child_box in zip(node[1:], split(box)):
                walk(child, child_box, depth + 1)
        elif tag == "outside":
            require(len(node) == 1 and minimum_norm_squared(box) >= M * M, "unproved disk exclusion")
        elif tag in caps:
            require(len(node) == 1 and cap_contains_box(box, caps[tag]), "unproved cap containment: " + tag)
        elif tag == "core":
            require(len(node) == 4 and tuple(node[1:]) in points, "bad convex witness")
            reserve = (F(1, 2) - epsilon) ** 2 - maximum_distance_squared(box, points[tuple(node[1:])])
            require(reserve > 0, "unproved core exclusion")
            min_core_reserve = reserve if min_core_reserve is None else min(min_core_reserve, reserve)
        else:
            raise ValueError("unknown node tag: " + str(tag))

    walk(0, (-M, M, -M, M), 0)
    require(len(seen) == len(nodes), "unvisited nodes in certificate")
    if data["version"] == 1:
        capacity_boxes = {"east": EAST,
                          "south_left": (-F(1), -F(3, 8), -M, -F(3, 4)),
                          "south_right": (-F(3, 8), F(1, 4), -M, -F(3, 4))}
    else:
        capacity_boxes = caps
    diagonals = {tag: cap_diameter_squared(cap) for tag, cap in capacity_boxes.items()}
    require(len(diagonals) == 3 and all(d < 1 for d in diagonals.values()), "three-cap capacity comparison failed")
    require(M * M + M + F(1, 2) - F(1105, 256) == F(31, 57600) > 0, "center-radius comparison failed")
    return {"status": "EXACT CONDITIONAL COVER VERIFIED", "nodes": len(nodes),
            "leaves": len(nodes) - counts["split"], "max_depth": max_depth,
            "node_counts": dict(sorted(counts.items())),
            "minimum_core_squared_reserve": str(min_core_reserve),
            "vertex_error_bound": str(epsilon),
            "capacity_region_diameters_squared": {k: str(v) for k, v in diagonals.items()},
            "maximum_other_units": 3, "maximum_total_units": 8,
            "original_D02_row_closed": False, "Lean_verification_claimed": False}


def regenerate(data, max_depth=14):
    """Discover a cover by rational predicates; success is replayed by verify."""
    epsilon, grid, caps = profile(data)
    points = witnesses(references(data), grid)
    nodes = []

    def visit(box, depth):
        index = len(nodes)
        nodes.append(None)
        cap = next((tag for tag, cap in caps.items() if cap_contains_box(box, cap)), None)
        if cap is not None:
            nodes[index] = [cap]
        elif minimum_norm_squared(box) >= M * M:
            nodes[index] = ["outside"]
        else:
            key = min(points, key=lambda k: maximum_distance_squared(box, points[k]))
            if maximum_distance_squared(box, points[key]) < (F(1, 2) - epsilon) ** 2:
                nodes[index] = ["core", *key]
            else:
                require(depth < max_depth, "unresolved rational cell at depth limit")
                nodes[index] = ["split", *(visit(child, depth + 1) for child in split(box))]
        return index

    visit((-M, M, -M, M), 0)
    answer = dict(data, nodes=nodes, root=0)
    verify(answer)
    return answer


def prepare_actual_vertex_box_check(data):
    """Replay once and retain spatial core leaves for many algebraic boxes.

    The resulting object is an implementation cache, not an external oracle.
    The direct interval check below needs the real physical vertex coordinates
    to belong to the supplied intervals, but needs no nominal vertex-error ball.
    """
    key = json.dumps(data, sort_keys=True, separators=(",", ":"))
    if key in _PREPARED_COVER_CACHE:
        return _PREPARED_COVER_CACHE[key]
    verify(data)
    _, grid, _ = profile(data)
    leaves = []

    def walk(index, box):
        node = data["nodes"][index]
        if node[0] == "split":
            for child, child_box in zip(node[1:], split(box)):
                walk(child, child_box)
        elif node[0] == "core":
            k, i, j = node[1:]
            u, v = F(i, grid), F(j, grid)
            weights = ((1 - u) * (1 - v), u * (1 - v), u * v, (1 - u) * v)
            leaves.append((index, box, k, i, j, weights))

    walk(data["root"], (-M, M, -M, M))
    answer = tuple(leaves)
    _PREPARED_COVER_CACHE[key] = answer
    return answer


def verify_actual_vertex_boxes(data, vertex_boxes, *, prepared=None):
    """Check one rational algebraic enclosure against the physical cover.

    Input shape is [5][4][2][2]: core, vertex, coordinate, lower/upper.
    Endpoints are Fraction, int, or exact rational strings, never floats.
    A successful result is conditional on the twenty ACTUAL vertices belonging
    to these forty closed coordinate intervals. It asserts no algebraic entry,
    solution uniqueness, stress reduction, or original-case closure.

    Pass prepare_actual_vertex_box_check(data) as prepared when checking many
    interval boxes against one previously replayed spatial certificate.
    """
    leaves = prepare_actual_vertex_box_check(data)
    require(prepared is None or prepared == leaves, "supplied spatial cache does not match the replayed certificate")
    require(len(vertex_boxes) == 5 and all(len(row) == 4 for row in vertex_boxes), "need 5 x 4 vertex boxes")
    boxes = []
    for row in vertex_boxes:
        out_row = []
        for vertex in row:
            require(len(vertex) == 2 and all(len(axis) == 2 for axis in vertex), "each vertex needs x/y closed intervals")
            out_vertex = []
            for low, high in vertex:
                require(not isinstance(low, float) and not isinstance(high, float), "floating input is not a rational enclosure")
                low, high = F(low), F(high)
                require(low <= high, "reversed interval")
                out_vertex.append((low, high))
            out_row.append(tuple(out_vertex))
        boxes.append(tuple(out_row))
    cache = {}
    min_reserve = None
    for index, cell, k, i, j, weights in leaves:
        key = k, i, j
        if key not in cache:
            cache[key] = tuple(
                (sum(w * vertex[d][0] for w, vertex in zip(weights, boxes[k])),
                 sum(w * vertex[d][1] for w, vertex in zip(weights, boxes[k])))
                for d in (0, 1))
        qx, qy = cache[key]
        # This is the exact maximum over BOTH independent closed rectangles.
        dx = max(abs(cell[0] - qx[1]), abs(cell[1] - qx[0]))
        dy = max(abs(cell[2] - qy[1]), abs(cell[3] - qy[0]))
        reserve = F(1, 4) - dx * dx - dy * dy
        if reserve <= 0:
            return {"verified": False, "first_unproved_core_leaf": index,
                    "squared_reserve": str(reserve), "original_D02_row_closed": False}
        min_reserve = reserve if min_reserve is None else min(min_reserve, reserve)
    return {"verified": True, "checked_core_leaves": len(leaves),
            "minimum_squared_reserve": str(min_reserve),
            "maximum_other_units": 3, "maximum_total_units": 8,
            "original_D02_row_closed": False}


def verify_actual_vertex_dyadic_boxes(data, vertex_boxes, *, precision_bits=44):
    """The same physical interval-entry check using only integers per leaf.

    Each supplied interval endpoint z denotes z / 2**precision_bits. The shape
    and physical conditional scope are exactly those of verify_actual_vertex_boxes.
    Clearing the common positive denominator is exact, not a rounding operation.
    """
    require(isinstance(precision_bits, int) and 1 <= precision_bits <= 256, "invalid dyadic precision")
    key = (json.dumps(data, sort_keys=True, separators=(",", ":")), precision_bits)
    if key not in _DYADIC_COVER_CACHE:
        leaves = prepare_actual_vertex_box_check(data)
        _, grid, _ = profile(data)
        witness_denominator = grid * grid * (1 << precision_bits)
        denominator = witness_denominator
        for _, box, *_ in leaves:
            for coordinate in box:
                denominator = lcm(denominator, coordinate.denominator)
        prepared = []
        for index, box, k, i, j, weights in leaves:
            cell = tuple(int(coordinate * denominator) for coordinate in box)
            integer_weights = tuple(int(weight * grid * grid) for weight in weights)
            require(sum(integer_weights) == grid * grid and min(integer_weights) >= 0, "bad integer convex weights")
            require(all(F(value, denominator) == coordinate for value, coordinate in zip(cell, box)), "inexact spatial denominator")
            prepared.append((index, cell, k, i, j, integer_weights))
        _DYADIC_COVER_CACHE[key] = (denominator, denominator // witness_denominator, tuple(prepared))
    denominator, multiplier, leaves = _DYADIC_COVER_CACHE[key]
    require(len(vertex_boxes) == 5 and all(len(row) == 4 for row in vertex_boxes), "need 5 x 4 vertex boxes")
    for row in vertex_boxes:
        for vertex in row:
            require(len(vertex) == 2 and all(len(axis) == 2 for axis in vertex), "each vertex needs two closed intervals")
            for low, high in vertex:
                require(isinstance(low, int) and isinstance(high, int) and low <= high, "bad dyadic integer interval")
    cache = {}
    min_reserve = None
    for index, cell, k, i, j, weights in leaves:
        witness_key = k, i, j
        if witness_key not in cache:
            cache[witness_key] = tuple(
                (multiplier * sum(w * vertex[d][0] for w, vertex in zip(weights, vertex_boxes[k])),
                 multiplier * sum(w * vertex[d][1] for w, vertex in zip(weights, vertex_boxes[k])))
                for d in (0, 1))
        qx, qy = cache[witness_key]
        dx = max(abs(cell[0] - qx[1]), abs(cell[1] - qx[0]))
        dy = max(abs(cell[2] - qy[1]), abs(cell[3] - qy[0]))
        # Strict original bound (dx/D)^2+(dy/D)^2 < 1/4.
        reserve = denominator * denominator - 4 * (dx * dx + dy * dy)
        if reserve <= 0:
            return {"verified": False, "first_unproved_core_leaf": index,
                    "scaled_squared_reserve": reserve, "original_D02_row_closed": False}
        min_reserve = reserve if min_reserve is None else min(min_reserve, reserve)
    return {"verified": True, "checked_core_leaves": len(leaves),
            "minimum_scaled_squared_reserve": min_reserve,
            "positive_reserve_denominator": 4 * denominator * denominator,
            "maximum_other_units": 3, "maximum_total_units": 8,
            "original_D02_row_closed": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path, default=DEFAULT)
    parser.add_argument("--regenerate", action="store_true")
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text())
    if args.regenerate:
        data = regenerate(data)
        args.certificate.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    print(json.dumps(verify(data), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
