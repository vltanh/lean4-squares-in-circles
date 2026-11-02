#!/usr/bin/env python3
"""Rejection controls for the low opposite-half ordering certificate."""
from copy import deepcopy
from pathlib import Path
import hashlib
import json

from verify_low_opposite_original_order import verify


def main():
    base = Path(__file__).resolve().parent
    path = base / 'low_opposite_original_order_cover.json'
    raw = path.read_bytes()
    data = json.loads(raw)
    accepted = json.loads((base / 'low_opposite_original_order_cover_independent_replay.json').read_text())
    checker = base / 'verify_low_opposite_original_order.py'
    kernel = base / 'verify_ownhalf_above_side.py'
    assert accepted['result'] == 'PASS' and accepted['complete'] is True
    assert accepted['certificate_sha256'] == hashlib.sha256(raw).hexdigest()
    assert accepted['checker_sha256'] == hashlib.sha256(checker.read_bytes()).hexdigest()
    assert accepted['independent_fraction_kernel_sha256'] == hashlib.sha256(kernel.read_bytes()).hexdigest()
    results = []

    def reject(name, damaged):
        try:
            verify(damaged)
        except (AssertionError, ValueError, KeyError, TypeError, IndexError) as exc:
            results.append({'name': name, 'rejected': True, 'exception': type(exc).__name__})
            return
        raise AssertionError(('false proof accepted', name))

    for name, key, value in (
        ('wrong_schema', 'schema', 'invalid'),
        ('unfinished_status', 'status', 'INCOMPLETE'),
        ('unresolved_count', 'remaining', 1),
        ('unresolved_frontier', 'pending', [{}]),
        ('wrong_leaf_count', 'leaves', data['leaves'] - 1),
        ('wrong_rule_counts', 'counts', [0, 0, 0, 0]),
        ('excessive_depth', 'maximum_depth', 61),
    ):
        damaged = dict(data)
        damaged[key] = value
        reject(name, damaged)
    damaged = dict(data)
    damaged['root'] = deepcopy(data['root'])
    damaged['root'][1][1] = '1'
    reject('truncated_horizontal_root', damaged)
    for name, mutate in (
        ('missing_chirality', lambda rows: rows.pop()),
        ('duplicate_chirality', lambda rows: rows[1].update(sign=rows[0]['sign'])),
        ('duplicate_root', lambda rows: rows[1].update(index=rows[0]['index'])),
        ('boolean_chirality', lambda rows: rows[0].update(sign=True)),
    ):
        damaged = dict(data)
        damaged['roots'] = deepcopy(data['roots'])
        mutate(damaged['roots'])
        reject(name, damaged)
    root = data['roots'][0]['index']
    for name, node in (
        ('invalid_axis', {'axis': 2, 'children': [0, 1]}),
        ('boolean_axis', {'axis': False, 'children': [0, 1]}),
        ('cycle', {'axis': 0, 'children': [root, root]}),
        ('invalid_rule', {'rule': 4, 'upper': '-1'}),
        ('boolean_rule', {'rule': False, 'upper': '-1'}),
    ):
        damaged = dict(data)
        damaged['nodes'] = list(data['nodes'])
        damaged['nodes'][root] = node
        reject(name, damaged)
    damaged = dict(data)
    damaged.update(nodes=[{'rule': 0, 'upper': '-1'}, {'rule': 0, 'upper': '-1'}],
                   roots=[{'index': 0, 'sign': -1}, {'index': 1, 'sign': 1}],
                   leaves=2, counts=[2, 0, 0, 0], maximum_depth=0)
    reject('false_whole_root_leaves', damaged)
    report = {'result': 'PASS', 'controls_rejected': len(results), 'controls': results,
              'certificate_sha256': accepted['certificate_sha256'],
              'checker_sha256': accepted['checker_sha256'],
              'independent_fraction_kernel_sha256': accepted['independent_fraction_kernel_sha256']}
    (base / 'low_opposite_original_order_rejection_controls.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
