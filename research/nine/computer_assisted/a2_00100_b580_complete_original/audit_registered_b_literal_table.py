"""Audit a complete registered B-original literal table and source-bound row accounting.

This reads exact proof bytes and their accepted report. It does not repeat
weighted arithmetic or turn a candidate into a proof.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import hashlib
import json
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('tree', type=Path)
    parser.add_argument('report', type=Path)
    parser.add_argument('table', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--original-id', required=True)
    args = parser.parse_args()
    started = time.monotonic()
    manifest = json.loads(args.tree.read_text())
    report = json.loads(args.report.read_text())
    assert report['status'] == 'PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE'
    assert report['initial_original_id'] == args.original_id
    assert report['certificate_sha256'] == sha(args.tree)
    assert report['complete'] is True and report['whole_original_proved'] is True
    assert report['entire_registered_original_domain_retained'] is True
    assert report['nodes'] == len(manifest['nodes'])
    assert report['excluded_leaves'] == report['terminal_leaves'] and report['open_leaves'] == 0
    expected_leaves = report['terminal_leaves']
    assert expected_leaves > 0
    audits = {audit['index']: audit for audit in report['node_audits']}
    leaves = {leaf['index']: leaf for leaf in report['leaf_table']}
    rows = [line.split('|')[1:-1] for line in args.table.read_text().splitlines()
        if line.startswith('| ') and line.split('|')[1].strip().isdigit()]
    table = {int(row[0]): [item.strip() for item in row] for row in rows}
    assert len(rows) == len(table) == len(leaves) == expected_leaves and set(table) == set(leaves)
    assert len(audits) == len(report['node_audits']) == len(manifest['nodes'])
    assert set(audits) == {entry['index'] for entry in manifest['nodes']}
    accounting, names, terminal_kinds = [], Counter(), Counter()
    for entry in manifest['nodes']:
        path = args.tree.parent / entry['file']
        assert sha(path) == entry['sha256']
        node = json.loads(path.read_text())
        record = node['record']
        index = entry['index']
        audit = audits[index]['audit']
        rounds = record['rounds']
        deductions = sum(len(round['proposals']) for round in rounds)
        bound_rows = sum(len(round['printed_rows']) for round in rounds)
        terminal = record.get('terminal', {})
        terminal_rows = terminal.get('rows', [])
        assert len(rounds) == audit['rounds'] and deductions == audit['deductions']
        assert bound_rows + len(terminal_rows) == audit['printed_rows_checked']
        for round in rounds:
            for row in round['printed_rows']:
                names['_'.join(row['name'].split('_')[:2])] += 1
        for row in terminal_rows:
            names['_'.join(row['name'].split('_')[:2])] += 1
        if index in leaves:
            leaf = leaves[index]
            assert leaf['excluded'] is True and not node['children']
            assert leaf['terminal_kind'] == terminal['kind']
            line = table[index]
            assert int(line[1]) == leaf['depth'] and int(line[4]) == len(rounds)
            assert int(line[2]) == audits[index]['parent']
            assert line[3] == str(audits[index]['choice'])
            assert int(line[5]) == deductions
            if audit['reserve'] is None:
                assert line[6] == terminal['kind']
            else:
                reserve = F(audit['reserve'])
                assert reserve > 0 and F(terminal['reserve']) == reserve
                prefix = 'positive exact reserve ≥ '
                assert line[6].startswith(prefix)
                assert 0 < F(line[6][len(prefix):]) <= reserve
            terminal_kinds[terminal['kind']] += 1
        accounting.append(dict(index=index, record_sha256=entry['sha256'], rounds=len(rounds),
            deductions=deductions, premise_rows=bound_rows, terminal_rows=len(terminal_rows),
            excluded_leaf=index in leaves))
    totals = {key: sum(item[key] for item in accounting)
        for key in ('rounds', 'deductions', 'premise_rows', 'terminal_rows')}
    assert totals['rounds'] == report['local_rounds']
    assert totals['deductions'] == report['local_deductions']
    assert totals['premise_rows'] + totals['terminal_rows'] == report['local_printed_rows']
    assert sum(names.values()) == report['local_printed_rows']
    result = dict(status='PASS_REGISTERED_B_COMPLETE_LITERAL_TABLE_AND_ROW_ACCOUNTING',
        original_id=report['initial_original_id'], original_path=report['initial_path'],
        tree_manifest_sha256=sha(args.tree), exact_report_sha256=sha(args.report),
        terminal_table_sha256=sha(args.table), terminal_leaves=expected_leaves,
        terminal_kinds=dict(terminal_kinds), totals=totals, nodes=accounting,
        literal_row_name_first_two_component_counts=dict(sorted(names.items())),
        row_name_counts_are_literal_identifiers_not_new_geometric_classifications=True,
        all_printed_terminal_reserve_lower_bounds_valid=True,
        weighted_arithmetic_repeated=False, new_original_cells=0, new_masks=0,
        seconds=time.monotonic() - started)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ('status', 'terminal_leaves',
        'terminal_kinds', 'totals', 'seconds')}, indent=2), flush=True)


if __name__ == '__main__':
    main()
