#!/usr/bin/env python3
"""Independent literal hand/table audit of three complete B16a quarters.

Uses only Python's standard library and the frozen packet. The published
portable exact replay supplies the row-validity and bound-induction proofs;
this audit separately checks every finite union and displayed terminal sum.
It never imports a producer or any mathematical checker from the packet.
"""
from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import json


def read(path):
    return json.loads(Path(path).read_text())


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def variable(index):
    return '0' if index == 18 else ('x_' if index % 2 == 0 else 'y_') + 'ABCDEFGHI'[index // 2]


def interval_cycle(state):
    """Return an exact negative cycle of necessary center differences."""
    edges = []

    def add(u, v, rhs, source):
        edges.append((u, v, F(rhs), source))

    for index, (lo, hi) in enumerate(state['positions']):
        add(18, index, hi, 'certified coordinate upper bound')
        add(index, 18, -F(lo), 'certified coordinate lower bound')
    for item in state.get('differences', []):
        i, j = item['pair']
        for axis, (lo, hi) in enumerate(item['intervals']):
            add(2 * i + axis, 2 * j + axis, hi, 'certified original difference upper bound')
            add(2 * j + axis, 2 * i + axis, -F(lo), 'certified original difference lower bound')
    for step in state['path']:
        if step[0] != 'proxy':
            continue
        i, j = step[1]
        axis, sign = step[2]
        assert axis in (0, 1) and sign in (-1, 1)
        gap = F(state['scalar'][27 + i][0]) + F(state['scalar'][27 + j][0])
        u, v = (2 * j + axis, 2 * i + axis) if sign == 1 else (2 * i + axis, 2 * j + axis)
        add(u, v, -gap, 'selected physical inset separation; sum of certified inset lower bounds')
    distance, previous = [F(0)] * 19, [None] * 19
    for _ in range(19):
        changed = None
        for index, (u, v, rhs, _) in enumerate(edges):
            if distance[v] > distance[u] + rhs:
                distance[v] = distance[u] + rhs
                previous[v] = index
                changed = v
        if changed is None:
            return None
    vertex = changed
    for _ in range(19):
        vertex = edges[previous[vertex]][0]
    start, selected = vertex, []
    while True:
        edge = edges[previous[vertex]]
        selected.append(edge)
        vertex = edge[0]
        if vertex == start:
            break
    coefficients = Counter()
    for u, v, _, _ in selected:
        coefficients[v] += 1
        coefficients[u] -= 1
    assert all(value == 0 for value in coefficients.values())
    rhs = sum((edge[2] for edge in selected), F(0))
    assert rhs < 0
    return dict(reserve=str(-rhs), coefficient_sum_zero=True, rows=[dict(
        expression=f'{variable(v)} - {variable(u)}', rhs=str(bound), source=source)
        for u, v, bound, source in selected])


def affine_reserve(terminal):
    rows = {row['index']: row for row in terminal['rows']}
    assert len(rows) == len(terminal['rows'])
    assert len(terminal['weights']) == len({i for i, _ in terminal['weights']})
    assert {i for i, _ in terminal['weights']} == set(rows)
    bounds = list(map(F, terminal['absolute_variable_bounds']))
    # There are no SAT splits in these three trees. The original center
    # normalization and unit frames give these absolute bounds directly.
    assert bounds == [F(91, 60)] * 18 + [F(1)] * 36
    coefficients, rhs = [F(0)] * 54, F(0)
    for index, numerator in terminal['weights']:
        assert type(numerator) is int and numerator >= 0
        weight, row = F(numerator, 1 << 40), rows[index]
        rhs += weight * F(row['rhs'])
        assert len(row['coefficients']) == len({k for k, _ in row['coefficients']})
        for k, value in row['coefficients']:
            assert 0 <= k < 54
            coefficients[k] += weight * F(value)
    assert coefficients == list(map(F, terminal['weighted_coefficients']))
    assert rhs == F(terminal['weighted_rhs'])
    residual = sum((bound * abs(value) for bound, value in zip(bounds, coefficients)), F(0))
    reserve = -rhs - residual
    assert reserve == F(terminal['reserve']) and reserve > 0
    return dict(reserve=str(reserve), weighted_rhs=str(rhs), residual_payment=str(residual),
                rows=len(rows), all_multipliers_nonnegative=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = args.packet.resolve()
    proof = read(root / 'COMPLEMENTARY_PROOF.json')
    assert proof['original_id'] == 'negative-16a2fc93c8d133f0'
    assert proof['whole_original_proved'] is False
    assert len(proof['pieces']) == 3 and {p['label'] for p in proof['pieces']} == {'I20', 'I31', 'I33'}
    table = {(row['quarter'], row['node']): row for row in proof['terminal_table']}
    assert len(table) == len(proof['terminal_table']) == 23
    expected_path = [['angle', 3, 0], ['angle_cut', [0, '0'], 0],
                     ['position_cut', [11, '1/2'], 1], ['f_side_escape', [5, 7], [3]]]
    assert proof['original_path'] == expected_path
    a, b, c, d = F(-1474347, 1048576), F(5, 4), F(-91, 60), F(91, 60)
    terminals, summaries, consumed = [], [], set()
    totals = Counter()
    for piece in proof['pieces']:
        label = piece['label']
        assert piece['domain']['root'] == piece['tree']['root'] == 'packet'
        domain_path, tree_path = root / piece['domain']['path'], root / piece['tree']['path']
        assert digest(domain_path) == piece['domain']['sha256']
        assert digest(tree_path) == piece['tree']['sha256']
        domain, manifest = read(domain_path), read(tree_path)
        i, j = int(label[1]), int(label[2])
        rectangle = [[str(a + (b - a) * F(i, 4)), str(a + (b - a) * F(i + 1, 4))],
                     [str(c + (d - c) * F(j, 4)), str(c + (d - c) * F(j + 1, 4))]]
        assert domain['rectangle'] == rectangle and domain['tile'] == [i, j]
        assert domain['parent']['sha256'] == proof['parent_sha256']
        assert domain['grid']['sha256'] == proof['grid_sha256']
        assert manifest['completed'] is True
        nodes = {}
        for entry in manifest['nodes']:
            path = tree_path.parent / entry['file']
            assert digest(path) == entry['sha256']
            node = read(path)
            assert (node['index'], node['depth'], node['status']) == (entry['index'], entry['depth'], entry['status'])
            assert node['index'] not in nodes and node['initial'] == node['record']['initial']
            nodes[node['index']] = node
            for round_ in node['record']['rounds']:
                totals['rounds'] += 1
                totals['deductions'] += len(round_['proposals'])
                totals['premise_rows'] += len(round_['printed_rows'])
            totals['terminal_rows'] += len(node['record'].get('terminal', {}).get('rows', []))
        visited, unions, leaves = set(), Counter(), []

        def visit(index):
            assert index not in visited
            visited.add(index)
            node, record = nodes[index], nodes[index]['record']
            assert node['initial']['path'][:len(expected_path)] == expected_path
            if not node['children']:
                assert node['status'] == 'CANDIDATE_CLOSED'
                terminal = record['terminal']
                display = table[(label, index)]
                consumed.add((label, index))
                result = dict(quarter=label, node=index, source_node_sha256=next(
                    e['sha256'] for e in manifest['nodes'] if e['index'] == index), kind=terminal['kind'])
                if terminal['kind'] == 'positive_exact_reserve':
                    result.update(affine_reserve(terminal))
                    assert F(display['reserve']) == F(result['reserve']) >= F(display['dyadic_lower_bound']) > 0
                    result['displayed_lower_bound'] = display['dyadic_lower_bound']
                else:
                    assert terminal['kind'] == 'accepted_center_interval_terminal'
                    state = record.get('terminal_state') or (record['rounds'][-1]['after'] if record['rounds'] else record['initial'])
                    if label == 'I20':
                        literal = read(root / 'I20_CENTER_INSET_TERMINAL_TABLE.json')
                        assert literal['source_node_sha256'] == result['source_node_sha256']
                        gap = F(state['scalar'][29][0]) + F(state['scalar'][35][0])
                        assert {(r['axis'], r['left_original'], r['right_original']) for r in literal['alternatives']} == {
                            (axis, left, right) for axis in (0, 1) for left, right in ((2, 8), (8, 2))}
                        for row in literal['alternatives']:
                            axis, left, right = row['axis'], row['left_original'], row['right_original']
                            upper = F(state['positions'][2 * right + axis][1]) - F(state['positions'][2 * left + axis][0])
                            assert F(row['upper_bound']) == upper and F(row['required_gap']) == gap
                            assert F(row['positive_margin']) == gap - upper > 0
                        result['four_inset_gaps'] = literal['alternatives']
                    else:
                        cycle = interval_cycle(state)
                        assert cycle is not None
                        result['short_interval_contradiction'] = cycle
                terminals.append(result)
                leaves.append(index)
                return
            assert node['complete_closed_children'] is True
            parent_state, split = record['final'], node['split']
            kind = split['kind']
            assert kind in ('proxy', 'angle')
            expected = [list(x) for x in product((0, 1), (-1, 1))] if kind == 'proxy' else [0, 1]
            assert len(node['children']) == len(set(node['children'])) == len(expected)
            assert [nodes[k]['choice'] for k in node['children']] == expected
            for child_index, choice in zip(node['children'], expected):
                child = nodes[child_index]
                assert child['parent'] == index and child['depth'] == node['depth'] + 1
                expected_state = deepcopy(parent_state)
                if kind == 'proxy':
                    expected_state['path'].append(['proxy', split['pair'], choice])
                else:
                    owner, cut = split['owner'], F(split['cut'])
                    lo, hi = map(F, expected_state['angles'][owner])
                    assert lo < cut < hi
                    expected_state['angles'][owner] = [str(lo), str(cut)] if choice == 0 else [str(cut), str(hi)]
                    expected_state['path'].append(['angle_cut', [owner, str(cut)], choice])
                assert child['initial'] == expected_state
                visit(child_index)
            unions[kind] += 1

        assert nodes[0]['parent'] is None and nodes[0]['depth'] == 0
        visit(0)
        assert visited == set(nodes)
        summaries.append(dict(quarter=label, rectangle=rectangle, nodes=len(nodes), leaves=len(leaves),
                              unions=dict(unions), open_leaves=0, manifest_sha256=digest(tree_path)))
    assert consumed == set(table)
    assert totals == Counter(rounds=19, deductions=2919, premise_rows=6707, terminal_rows=236)
    assert sum(s['nodes'] for s in summaries) == 31
    assert sum(s['leaves'] for s in summaries) == 23
    assert sum(t['kind'] == 'positive_exact_reserve' for t in terminals) == 10
    assert sum('short_interval_contradiction' in t for t in terminals) == 12
    result = dict(status='PASS_INDEPENDENT_COMPLETE_B16A_QUARTER_HAND_TABLE_AUDIT',
                  original_id=proof['original_id'], original_path=expected_path, quarter_covers=summaries,
                  totals=dict(totals), terminal_audits=sorted(terminals, key=lambda t: (t['quarter'], t['node'])),
                  parent_sha256=proof['parent_sha256'], grid_sha256=proof['grid_sha256'],
                  packet_manifest_sha256=digest(root / 'INPUT_MANIFEST.json'),
                  portable_exact_replay_supplies_all_row_validity_and_bound_induction=True,
                  no_packet_math_code_imported=True, whole_original_proved=False,
                  new_original_cells=0, new_masks=0)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'totals', 'whole_original_proved', 'new_original_cells', 'new_masks')}))


if __name__ == '__main__':
    main()
