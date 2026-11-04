"""Independent source/table topology and affine-terminal audit for D821.

This does not replace fresh geometric row reconstruction by the native or
portable checker. It checks the complete literal table against every raw
record and independently sums every affine terminal using Fraction.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from collections import Counter
from copy import deepcopy
import hashlib
import json
import time

ROOT = Path(__file__).resolve().parent.parent
BASE = ROOT / 'global_work/d821_work'
REPORT = BASE / 'D821_COMPLETE_ORIGINAL_EXACT_REPLAY.json'
TABLE = BASE / 'complete_literal_terminal_table/COMPLETE_TERMINAL_TABLE.json'
MARKDOWN = TABLE.with_suffix('.md')
OUTPUT = ROOT / 'd_work/D821_COMPLETE_LITERAL_TABLE_ROOT_AUDIT.json'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    started = time.monotonic()
    report = json.loads(REPORT.read_text())
    table = json.loads(TABLE.read_text())
    assert report['status'] == 'PASS_COMPLETE_ORIGINAL_CELL'
    assert report['whole_original_proved'] is True
    assert report['original_id'] == 'positive-821c9a2debeed0aa'
    assert report['complete_closed_complement_domains'] == 5
    assert table['exact_report'] == dict(path=str(REPORT), sha256=sha(REPORT))
    covers = {x['manifest']['sha256']: x for x in report['grafted_cover_nodes']}
    audits = {x['manifest_sha256']: x for x in report['exact_tree_reports'].values()}
    assert len(covers) == len(audits) == table['tree_count'] == 46
    assert set(covers) == set(audits)
    table_rows = {(x['manifest']['sha256'], x['node']): x for x in table['nodes']}
    assert len(table_rows) == len(table['nodes']) == table['node_count'] == 650
    labels = {h: f'T{k:03d}' for k, h in enumerate(covers)}
    expected_keys = set()
    terminals = Counter()
    unions = Counter()
    total = Counter()
    reserve_receipts = []
    all_nodes = {}
    complete_edges = {}
    originals = report['original_path']
    for digest, cover in covers.items():
        ref = cover['manifest']
        path = Path(ref['path'])
        assert sha(path) == digest
        manifest = json.loads(path.read_text())
        entries = {n['index']: n for n in manifest['nodes']}
        assert set(entries) == set(range(len(entries)))
        local = {n['index']: n['audit'] for n in audits[digest]['node_audits']}
        assert set(local) == set(entries)
        grafts = {g['leaf_index']: g['continuation'] for g in cover['grafts']}
        assert len(grafts) == len(cover['grafts'])
        used_grafts = set()
        for index, entry in entries.items():
            key = (digest, index)
            expected_keys.add(key)
            literal = table_rows[key]
            source = path.parent / entry['file']
            raw_bytes = source.read_bytes()
            assert hashlib.sha256(raw_bytes).hexdigest() == entry['sha256']
            node = json.loads(raw_bytes)
            record = node['record']
            audit = local[index]
            assert literal['raw_node'] == dict(path=str(source), sha256=entry['sha256'])
            assert literal['manifest'] == ref and literal['tree'] == labels[digest]
            assert literal['component'] == manifest['component'] == cover['component']
            assert literal['node'] == node['index'] == index
            for field in ('parent', 'depth', 'choice'):
                assert literal[field] == node[field]
            assert literal['original_path'] == node['initial']['path']
            assert node['initial']['id'] == report['original_id']
            assert node['initial']['path'][:len(originals)] == originals
            assert record['initial'] == node['initial']
            assert literal['audit'] == audit
            terminal = record.get('terminal')
            rounds = len(record['rounds'])
            deductions = sum(len(r['proposals']) for r in record['rounds'])
            premises = sum(len(r['printed_rows']) for r in record['rounds'])
            terminal_rows = len(terminal['rows']) if terminal and terminal['kind'] == 'positive_exact_reserve' else 0
            assert audit['rounds'] == rounds
            assert audit['deductions'] == deductions
            assert audit['printed_rows_checked'] == premises + terminal_rows
            assert audit['numerical_discovery_fields_used'] is False
            assert audit['whole_original_credit'] == audit['whole_mask_credit'] == 0
            total.update(rounds=rounds, deductions=deductions,
                         premise_rows=premises, terminal_rows=terminal_rows, nodes=1)
            view = {k: deepcopy(node[k]) for k in ('index', 'parent', 'depth', 'choice', 'initial', 'children')}
            if 'final' in record:
                view['final'] = record['final']
            if 'split' in node:
                view['split'] = node['split']
            all_nodes[key] = view
            if audit['status'] == 'PASS_EXCLUDED_PHYSICAL_DOMAIN':
                assert terminal is not None and not node['children'] and index not in grafts
                assert literal['terminal_kind'] == terminal['kind']
                terminals[terminal['kind']] += 1
                complete_edges[key] = []
                if terminal['kind'] == 'positive_exact_reserve':
                    bounds = list(map(Q, terminal['absolute_variable_bounds']))
                    assert len(bounds) >= 54 and all(x >= 0 for x in bounds)
                    rows = {r['index']: r for r in terminal['rows']}
                    assert len(rows) == len(terminal['rows'])
                    weights = terminal['weights']
                    assert {i for i, w in weights} == set(rows)
                    assert len(weights) == len(rows)
                    coeff = [Q(0)] * len(bounds)
                    rhs = Q(0)
                    for i, weight in weights:
                        assert type(weight) is int and weight > 0
                        factor = Q(weight, 1 << 40)
                        rhs += factor * Q(rows[i]['rhs'])
                        for column, value in rows[i]['coefficients']:
                            assert type(column) is int and 0 <= column < len(coeff)
                            coeff[column] += factor * Q(value)
                    reserve = -rhs - sum(abs(c) * b for c, b in zip(coeff, bounds))
                    assert reserve > 0 and reserve == Q(terminal['reserve']) == Q(audit['reserve'])
                    assert coeff == list(map(Q, terminal['weighted_coefficients']))
                    assert rhs == Q(terminal['weighted_rhs'])
                    prefix = 'exact reserve >= '
                    assert literal['conclusion'].startswith(prefix)
                    lower = Q(literal['conclusion'][len(prefix):])
                    assert 0 < lower <= reserve and lower.numerator == 1
                    assert lower.denominator & (lower.denominator - 1) == 0
                    reserve_receipts.append(dict(tree=labels[digest], node=index,
                                                 rows=len(rows), reserve=str(reserve), lower=str(lower)))
                else:
                    assert audit['reserve'] is None and literal['conclusion'] == terminal['kind']
            else:
                assert audit['status'] == 'PASS_CERTIFIED_PHYSICAL_STATE_OPEN' and terminal is None
                if node['children']:
                    split = node['split']
                    count = {'proxy': 4, 'sat': 8, 'angle': 2}[split['kind']]
                    assert len(node['children']) == len(set(node['children'])) == count
                    assert index not in grafts and node['complete_closed_children'] is True
                    assert literal['conclusion'] == f"complete {split['kind']}{count} cover: {node['children']}"
                    unions[split['kind']] += 1
                    complete_edges[key] = [(digest, child) for child in node['children']]
                else:
                    child = grafts[index]
                    used_grafts.add(index)
                    assert child['sha256'] in covers and covers[child['sha256']]['manifest'] == child
                    assert literal['conclusion'] == 'graft to ' + labels[child['sha256']]
                    complete_edges[key] = [(child['sha256'], 0)]
                    total['grafts'] += 1
        assert used_grafts == set(grafts)
    assert set(table_rows) == expected_keys
    for key, node in all_nodes.items():
        if not node['children']:
            continue
        split = node['split']
        kind = split['kind']
        expected = (set(product((0, 1), (-1, 1))) if kind == 'proxy' else
                    set(product(split['pair'], (0, 1), (-1, 1))) if kind == 'sat' else {0, 1})
        choices = set()
        for child_key in complete_edges[key]:
            child = all_nodes[child_key]
            assert child['parent'] == node['index'] and child['depth'] == node['depth'] + 1
            choice = tuple(child['choice']) if kind != 'angle' else child['choice']
            choices.add(choice)
            state = deepcopy(node['final'])
            if kind == 'angle':
                owner, cut = split['owner'], Q(split['cut'])
                lo, hi = map(Q, state['angles'][owner])
                assert lo < cut < hi
                state['angles'][owner] = list(map(str, (lo, cut) if choice == 0 else (cut, hi)))
                state['path'].append(['angle_cut', [owner, str(cut)], choice])
            else:
                state['path'].append([kind, split['pair'], list(choice)])
            assert child['initial'] == state
        assert choices == expected
    roots = []
    for component in report['component_audits']:
        assert component['complete'] is True
        if component['tree'] is not None:
            roots.append((component['tree']['sha256'], 0))
        else:
            assert component['pilot']['status'] == 'PASS_EXCLUDED_PHYSICAL_DOMAIN'
    assert {c['component'] for c in report['component_audits']} == set(range(5))
    seen = set()
    def walk(key, active):
        assert key not in active and key not in seen
        for child in complete_edges[key]:
            walk(child, active | {key})
        seen.add(key)
    for root in roots:
        walk(root, set())
    assert seen == expected_keys
    assert len([line for line in MARKDOWN.read_text().splitlines() if line.startswith('| T')]) == 651
    result = dict(status='PASS_D821_COMPLETE_LITERAL_TABLE_AND_INDEPENDENT_AFFINE_TERMINAL_AUDIT',
        report_sha256=sha(REPORT), table_sha256=sha(TABLE), markdown_sha256=sha(MARKDOWN),
        checker_sha256=sha(__file__), trees=len(covers), **dict(total),
        checked_row_occurrences=total['premise_rows'] + total['terminal_rows'],
        exclusions_by_kind=dict(terminals), closed_unions=dict(unions),
        independent_affine_terminal_sums=reserve_receipts,
        complete_five_domain_graft_graph=True, every_raw_node_hash_verified=True,
        every_closed_child_choice_and_initial_state_checked=True,
        fresh_geometric_row_reconstruction_is_in_separate_native_and_portable_replays=True,
        new_original_credit_from_this_review=0, new_masks=0,
        seconds=time.monotonic() - started)
    assert not OUTPUT.exists()
    OUTPUT.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if not isinstance(v,(dict,list))}), flush=True)


if __name__ == '__main__':
    main()
