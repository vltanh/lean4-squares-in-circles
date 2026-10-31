"""Independent rational replay of an eleven-square axis exclusion tree.

Uses Fraction intervals, simultaneous updates and a different rounding scale.
Does not import the generator or trust its leaf summaries.
"""
from fractions import Fraction as F
from itertools import combinations
from math import isqrt
import json
import sys
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without -O: this independent certificate uses assertions.")

PRECISION = 10**6
Q = F(49013, 10000)
HALF = F(1, 2)
GRID = {(x, y) for x in (-1, 0, 1) for y in (-1, 0, 1)} | {
    (-2, 0), (2, 0), (0, -2), (0, 2)
}


def sqrt_upper(value):
    """Smallest multiple of 1/PRECISION whose square is >= value."""
    scaled = value * PRECISION**2
    z = isqrt(scaled.numerator // scaled.denominator)
    if F(z*z) < scaled:
        z += 1
    result = F(z, PRECISION)
    assert result * result >= value
    return result


def graph(cells):
    edges = set()
    alternatives = set()
    for i, j in combinations(range(11), 2):
        dx, dy = cells[j][0]-cells[i][0], cells[j][1]-cells[i][1]

        def directed(axis, difference):
            a, b = 2*i+axis, 2*j+axis
            return (a, b) if difference > 0 else (b, a)

        if dx == 0:
            edges.add(directed(1, dy))
        elif dy == 0:
            edges.add(directed(0, dx))
        elif abs(dx) < 2 and abs(dy) < 2:
            alternatives.add(frozenset((directed(0, dx), directed(1, dy))))
    return edges, alternatives


def refute(cells, fixed, alternatives, path):
    box = [(F(k)-HALF, F(k)+HALF) for p in cells for k in p]
    edges = fixed | set(path)
    for iteration in range(20000):
        proposals = [[lo, hi] for lo, hi in box]
        new_edges = set(edges)
        for i in range(11):
            for target, other in ((2*i, 2*i+1), (2*i+1, 2*i)):
                lo, hi = box[other]
                minimum_absolute = F(0) if lo <= 0 <= hi else min(abs(lo), abs(hi))
                available = Q-(minimum_absolute+HALF)**2
                if available < 0:
                    return iteration+1
                limit = sqrt_upper(available)-HALF
                proposals[target][0] = max(proposals[target][0], -limit)
                proposals[target][1] = min(proposals[target][1], limit)
        for source, target in edges:
            proposals[target][0] = max(proposals[target][0], box[source][0]+1)
            proposals[source][1] = min(proposals[source][1], box[target][1]-1)
        for pair in alternatives:
            legal = [(a, b) for a, b in pair if box[b][1]-box[a][0] >= 1]
            if not legal:
                return iteration+1
            if len(legal) == 1:
                new_edges.add(legal[0])
        if any(lo > hi for lo, hi in proposals):
            return iteration+1
        replacement = [tuple(p) for p in proposals]
        if replacement == box and new_edges == edges:
            raise AssertionError("The independent replay did not refute this leaf")
        box, edges = replacement, new_edges
    raise AssertionError("Independent replay exceeded its iteration limit")


def orbit(holes):
    transforms = []
    for swap in (False, True):
        for sx in (-1, 1):
            for sy in (-1, 1):
                transforms.append(frozenset(
                    (sx*(y if swap else x), sy*(x if swap else y)) for x, y in holes
                ))
    return frozenset(transforms)


def validate_cover(cases):
    allowed = {
        frozenset(holes) for holes in combinations(GRID, 2)
        if any(y == 0 for x, y in holes) and any(x == 0 for x, y in holes)
    }
    assert len(allowed) == 28
    representatives = [frozenset(map(tuple, case["holes"])) for case in cases]
    assert len(representatives) == len(set(representatives)) == 6
    orbits = [orbit(h) for h in representatives]
    assert sorted(map(len, orbits)) == [4, 4, 4, 4, 4, 8]
    assert set().union(*orbits) == allowed
    assert sum(map(len, orbits)) == len(allowed)


def replay(data):
    assert F(data["q_num"], data["q_den"]) == Q
    cases = data["cases"]
    validate_cover(cases)
    total_nodes = total_leaves = 0
    for case in cases:
        holes = set(map(tuple, case["holes"]))
        cells = [tuple(p) for p in case["cells"]]
        assert len(cells) == len(set(cells)) == 11
        assert set(cells) == GRID-holes
        fixed, alternatives = graph(cells)
        nodes = leaves = maximum_rounds = 0

        def visit(tree, path):
            nonlocal nodes, leaves, maximum_rounds
            nodes += 1
            if "split" not in tree:
                assert tree.get("closed") is True
                maximum_rounds = max(maximum_rounds,
                    refute(cells, fixed, alternatives, path))
                leaves += 1
                return
            split = [tuple(e) for e in tree["split"]]
            assert len(split) == 2 and len(set(split)) == 2
            assert frozenset(split) in alternatives
            assert len(tree["children"]) == 2
            for edge, child in zip(split, tree["children"]):
                visit(child, path+[edge])

        visit(case["tree"], [])
        assert nodes == case["stats"]["nodes"]
        assert leaves == case["stats"]["leaves"]
        total_nodes += nodes
        total_leaves += leaves
        print(case["holes"], {"nodes": nodes, "leaves": leaves,
                              "max_simultaneous_rounds": maximum_rounds})
    print({"replayed_nodes": total_nodes, "replayed_leaves": total_leaves,
           "rounding_scale": PRECISION, "q": str(Q)})


if __name__ == "__main__":
    with open(sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('AXIS_EXCLUSION.json')) as source:
        replay(json.load(source))
