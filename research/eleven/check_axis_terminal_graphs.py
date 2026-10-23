"""Replay the axis exclusion and verify the hand motif in every terminal graph.

Place beside axis_exclusion.py, AXIS_EXCLUSION.json and AXIS_TERMINAL_GRAPHS.json.
Only integer and Fraction arithmetic is used. No optimizer is imported.
"""
import argparse
import hashlib
import json
from collections import Counter
from fractions import Fraction
from math import isqrt
from pathlib import Path

if not __debug__:
    raise SystemExit('Run without -O: this checker uses assertions.')

import axis_exclusion as source


def propagate_with_trace(bounds, edges, choices):
    """Independent replay retaining all separators justified before closure."""
    scale = source.SCALE
    bounds = [interval.copy() for interval in bounds]
    edges = edges.copy()
    choices = choices.copy()
    for iteration in range(10000):
        changed = False
        for square in range(11):
            for coord, other in ((2*square, 2*square+1), (2*square+1, 2*square)):
                lower, upper = bounds[coord]
                other_lower, other_upper = bounds[other]
                min_abs = max(other_lower, -other_upper, 0)
                radicand = (source.Q_NUM*scale*scale//source.Q_DEN
                            - (min_abs+scale//2)**2)
                if radicand < 0:
                    return ({'closed': True, 'reason': 'disk-negative',
                             'square': square, 'iteration': iteration,
                             'radicand': radicand}, edges)
                root = isqrt(radicand)
                if root*root < radicand:
                    root += 1
                assert root*root >= radicand
                assert root == 0 or (root-1)**2 < radicand
                cap = root-scale//2
                new_lower, new_upper = max(lower, -cap), min(upper, cap)
                if new_lower > new_upper:
                    return ({'closed': True, 'reason': 'disk-empty',
                             'coordinate': coord, 'iteration': iteration,
                             'lower': new_lower, 'upper': new_upper}, edges)
                if new_lower > lower or new_upper < upper:
                    changed = True
                bounds[coord] = [new_lower, new_upper]
        for a, b in edges:
            lower = max(bounds[b][0], bounds[a][0]+scale)
            upper = min(bounds[a][1], bounds[b][1]-scale)
            if lower > bounds[b][1] or upper < bounds[a][0]:
                return ({'closed': True, 'reason': 'edge-empty', 'edge': [a, b],
                         'iteration': iteration, 'source_lower': bounds[a][0],
                         'target_upper': bounds[b][1]}, edges)
            if lower > bounds[b][0] or upper < bounds[a][1]:
                changed = True
            bounds[b][0], bounds[a][1] = lower, upper
        remaining = []
        for e, f in choices:
            legal = [bounds[b][1]-bounds[a][0] >= scale for a, b in (e, f)]
            if not any(legal):
                return ({'closed': True, 'reason': 'both-separators-empty',
                         'choice': [list(e), list(f)], 'iteration': iteration,
                         'gaps': [bounds[b][1]-bounds[a][0] for a, b in (e, f)]},
                        edges)
            if all(legal):
                remaining.append((e, f))
            else:
                edges.append(e if legal[0] else f)
                changed = True
        choices = remaining
        if not changed:
            return ({'closed': False, 'bounds': bounds, 'edges': edges,
                     'choices': choices, 'rounds': iteration+1}, edges)
    raise RuntimeError('Replay iteration limit reached; no closure claimed.')


def adjacency(edges, swap=False, flipx=False, flipy=False):
    graphs = [[set() for _ in range(11)] for _ in range(2)]
    for a, b in edges:
        assert 0 <= a < 22 and 0 <= b < 22 and a % 2 == b % 2
        assert a//2 != b//2
        axis = a % 2
        if swap:
            axis = 1-axis
        i, j = a//2, b//2
        if (flipx, flipy)[axis]:
            i, j = j, i
        graphs[axis][i].add(j)
    return graphs


def path_at_least(graph, start, end, length):
    """A simple directed path certifies the telescoped coordinate gap."""
    def visit(path):
        if path[-1] == end and len(path)-1 >= length:
            return path
        for vertex in sorted(graph[path[-1]]):
            if vertex not in path:
                result = visit(path+[vertex])
                if result is not None:
                    return result
        return None
    result = visit([start])
    assert result is not None, (start, end, length)
    return result


def verify_motif(record, edges):
    assert record['edges'] == [list(edge) for edge in edges]
    kind = record['kind']
    if kind == 'two-four-chains':
        graph = adjacency(edges)[record['axis']]
        first, second = record['paths']
        assert len(first) == len(second) == 4
        assert len(set(first+second)) == 8
        for path in (first, second):
            assert all(0 <= i < 11 for i in path)
            assert all(b in graph[a] for a, b in zip(path, path[1:]))
        return
    graph_x, graph_y = adjacency(
        edges, record.get('swap', False), record.get('flipx', False),
        record.get('flipy', False))
    labels = record['labels']
    assert all(0 <= i < 11 for i in labels)
    if kind == 'six-square-stress':
        assert len(labels) == len(set(labels)) == 6
        a, b, c, d, e, f = labels
        requirements = ((graph_x, a, c, 1), (graph_x, c, e, 1),
                        (graph_x, b, f, 3), (graph_x, d, f, 2),
                        (graph_y, a, b, 1), (graph_y, c, d, 3),
                        (graph_y, e, f, 2))
    else:
        assert kind == 'three-square-fork'
        assert len(labels) == len(set(labels)) == 3
        a, b, c = labels
        requirements = ((graph_x, a, b, 3), (graph_x, a, c, 3),
                        (graph_y, b, c, 2))
    for graph, a, b, length in requirements:
        path_at_least(graph, a, b, length)


def verify_constants():
    q = Fraction(source.Q_NUM, source.Q_DEN)
    assert source.SCALE > 0 and source.SCALE % 2 == 0
    assert (source.Q_NUM*source.SCALE*source.SCALE) % source.Q_DEN == 0
    bounds = {2: Fraction(1415, 1000), 17: Fraction(4124, 1000),
              10: Fraction(3163, 1000), 106: Fraction(10296, 1000),
              13: Fraction(3606, 1000)}
    assert all(upper > 0 and upper*upper > n for n, upper in bounds.items())
    upper_sum = bounds[2]+bounds[17]+3*bounds[10]+bounds[106]+5*bounds[13]
    assert upper_sum < Fraction(1084, 25)
    forces = [(0, 0) for _ in range(6)]
    # (source, target, coordinate, weight, minimum chain gap)
    inequalities = [(0, 2, 0, 1, 1), (2, 4, 0, 4, 1),
                    (1, 5, 0, 4, 3), (3, 5, 0, 5, 2),
                    (0, 1, 1, 1, 1), (2, 3, 1, 9, 3),
                    (4, 5, 1, 6, 2)]
    forces = [list(v) for v in forces]
    for a, b, axis, weight, _ in inequalities:
        forces[a][axis] -= weight
        forces[b][axis] += weight
    assert forces == [[-1, -1], [-4, 1], [-3, -9], [-5, 9], [4, -6], [9, 6]]
    rhs = sum(weight*gap for _, _, _, weight, gap in inequalities)
    support = sum(Fraction(abs(x)+abs(y), 2) for x, y in forces)
    assert rhs == 67 and support == 29 and rhs+support == 96
    assert [x*x+y*y for x, y in forces] == [2, 17, 90, 106, 52, 117]
    assert Fraction(96, 1)/Fraction(1084, 25) == Fraction(600, 271)
    assert Fraction(600, 271)**2 > q
    assert Fraction(73, 32)**2 > 5 > q


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path,
                        default=Path(source.__file__).with_name('AXIS_EXCLUSION.json'))
    parser.add_argument('--terminals', type=Path,
                        default=Path(__file__).with_name('AXIS_TERMINAL_GRAPHS.json'))
    args = parser.parse_args()
    raw = args.certificate.read_bytes()
    certificate = json.loads(raw)
    manifest = json.loads(args.terminals.read_text())
    assert manifest['schema'] == 'eleven-axis-terminal-graphs-v1'
    assert manifest['certificate_sha256'] == hashlib.sha256(raw).hexdigest()
    assert certificate['schema'] == 'eleven-axis-exclusion-v1'
    assert certificate['q_num'] == source.Q_NUM
    assert certificate['q_den'] == source.Q_DEN
    assert certificate['scale'] == source.SCALE
    verify_constants()
    records = {}
    for record in manifest['terminals']:
        key = (tuple(map(tuple, record['holes'])), tuple(record['path']))
        assert key not in records
        records[key] = record
    assert len(records) == 19
    visited = set()
    kinds = Counter()
    total_nodes = 0
    assert len(certificate['cases']) == len(source.HOLES) == 6
    for case, expected_holes in zip(certificate['cases'], source.HOLES):
        holes = tuple(map(tuple, case['holes']))
        assert holes == tuple(expected_holes)
        cells, edges, choices, bounds = source.problem(holes)
        assert case['cells'] == [list(cell) for cell in cells]
        assert case['initial_binary_pairs'] == len(choices)
        stats = Counter()
        def walk(tree, bounds, edges, choices, path):
            stats['nodes'] += 1
            result, traced_edges = propagate_with_trace(bounds, edges, choices)
            assert result == source.propagate(bounds, edges, choices)
            if result['closed']:
                assert result == tree
                key = (holes, tuple(path))
                assert key in records and key not in visited
                verify_motif(records[key], traced_edges)
                visited.add(key)
                kinds[records[key]['kind']] += 1
                stats['leaves'] += 1
                return
            assert 'split' in tree and len(tree['children']) == 2
            choice = tuple(map(tuple, tree['split']))
            assert choice in result['choices']
            remaining = result['choices'].copy()
            remaining.remove(choice)
            for k, edge in enumerate(choice):
                walk(tree['children'][k], result['bounds'], result['edges']+[edge],
                     remaining, path+[k])
        walk(case['tree'], bounds, edges, choices, [])
        assert dict(stats) == case['stats']
        total_nodes += stats['nodes']
    assert visited == set(records) and total_nodes == 32
    assert kinds == {'six-square-stress': 10, 'two-four-chains': 7,
                     'three-square-fork': 2}
    print('PASS: all 32 certificate nodes replayed and all 19 terminal motifs verified.')
    print('10 six-square stresses; 7 pairs of four-chains; 2 three-square forks.')
    print('Forced separators still use the exact interval replay; no optimizer input.')

if __name__ == '__main__':
    main()
