#!/usr/bin/env python3
"""Damage controls for the independent own-half upper-side verifier."""
from copy import deepcopy
from pathlib import Path
import hashlib
import json

from verify_ownhalf_above_side import verify


def main():
    base = Path(__file__).resolve().parent
    path = base / 'ownhalf_above_side_cover.json'
    raw = path.read_bytes()
    data = json.loads(raw)
    report = json.loads((base / 'ownhalf_above_side_cover_independent_replay.json').read_text())
    source = base / 'verify_ownhalf_above_side.py'
    assert report['result'] == 'PASS' and report['complete'] is True
    assert report['certificate_sha256'] == hashlib.sha256(raw).hexdigest()
    assert report['checker_sha256'] == hashlib.sha256(source.read_bytes()).hexdigest()
    cases = []

    def rejected(name, damaged):
        try:
            verify(damaged)
        except (AssertionError, ValueError, TypeError, KeyError, IndexError) as exc:
            cases.append({'name': name, 'rejected': True, 'exception': type(exc).__name__})
            return
        raise AssertionError(('false proof accepted', name))

    for name, key, value in (
        ('wrong_schema', 'schema', 'invalid'),
        ('unfinished_status', 'status', 'INCOMPLETE'),
        ('nonempty_frontier_count', 'remaining', 1),
        ('nonempty_frontier', 'pending', [{}]),
        ('wrong_processed_count', 'processed', data['processed'] - 1),
        ('wrong_leaf_count', 'leaves', data['leaves'] - 1),
        ('excessive_depth', 'maximum_depth', 61),
    ):
        damaged = dict(data)
        damaged[key] = value
        rejected(name, damaged)

    damaged = dict(data)
    damaged['root'] = deepcopy(data['root'])
    damaged['root'][0][1] = '3/5'
    rejected('truncated_main_width_domain', damaged)

    for name, mutate in (
        ('missing_sign_family', lambda rows: rows.pop()),
        ('duplicate_sign_family', lambda rows: rows[1].update(signs=rows[0]['signs'])),
        ('duplicate_root_index', lambda rows: rows[1].update(index=rows[0]['index'])),
        ('boolean_sign', lambda rows: rows[0]['signs'].__setitem__(0, True)),
    ):
        damaged = dict(data)
        damaged['roots'] = deepcopy(data['roots'])
        mutate(damaged['roots'])
        rejected(name, damaged)

    root_id = data['roots'][0]['index']
    for name, node in (
        ('invalid_split_dimension', {'axis': 3, 'children': [0, 1]}),
        ('boolean_split_dimension', {'axis': True, 'children': [0, 1]}),
        ('cyclic_tree', {'axis': 0, 'children': [root_id, root_id]}),
        ('invalid_scalar_rule', {'rule': 1, 'upper': '-1'}),
        ('boolean_scalar_rule', {'rule': False, 'upper': '-1'}),
    ):
        damaged = dict(data)
        damaged['nodes'] = list(data['nodes'])
        damaged['nodes'][root_id] = node
        rejected(name, damaged)

    damaged = dict(data)
    damaged['roots'] = [dict(index=i, signs=list(row['signs']))
                        for i, row in enumerate(data['roots'])]
    damaged.update(nodes=[{'rule': 0, 'upper': '-1'} for _ in range(8)],
                   processed=8, leaves=8, maximum_depth=0)
    rejected('false_whole_root_scalar_leaves', damaged)

    result = {'result': 'PASS', 'controls_rejected': len(cases), 'controls': cases,
              'certificate_sha256': hashlib.sha256(raw).hexdigest(),
              'checker_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'scope': 'metadata, root union, original domains, split and scalar tags, cycles, false exact leaves'}
    (base / 'ownhalf_above_side_rejection_controls.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
