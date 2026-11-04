#!/usr/bin/env python3
"""Read-only byte, register-history and finite mask checks; not a proof replay."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path


def check(root):
    manifest = json.loads((root / 'PUBLICATION_MANIFEST.json').read_bytes())
    files = manifest['files']
    actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
    assert actual == set(files) | {'PUBLICATION_MANIFEST.json'}
    assert not any(p.is_symlink() for p in root.rglob('*'))
    for name, identity in files.items():
        data = (root / name).read_bytes()
        assert len(data) == identity['bytes'], name
        assert hashlib.sha256(data).hexdigest() == identity['sha256'], name
    assert len(files) == manifest['file_count_excluding_this_manifest']
    assert sum(x['bytes'] for x in files.values()) == manifest['total_bytes_excluding_this_manifest']
    state = json.loads((root / 'PUBLICATION_STATE.json').read_bytes())
    old = json.loads((root / 'source_snapshot/repo/research/nine/gates/A2_00100_FIXED_FRONTIER.json').read_bytes())
    now = json.loads((root / 'CURRENT_FIXED_REGISTER_SNAPSHOT.json').read_bytes())
    before, after = ({r['id']: r for r in x['cells']} for x in (old, now))
    assert len(before) == len(after) == 231 and before.keys() == after.keys()
    changed = [k for k in before if before[k] != after[k]]
    assert changed == ['positive-821c9a2debeed0aa']
    assert before[changed[0]]['status'] == 'OPEN' and after[changed[0]]['status'] == 'CLOSED'
    for register, expected in ((old, (221, 10)), (now, (222, 9))):
        assert register['original_cells'] == 231 and register['whole_mask_closed'] is False
        counts = tuple(sum(r['status'] == status for r in register['cells']) for status in ('CLOSED', 'OPEN'))
        assert counts == expected == (register['closed_cells'], register['open_cells'])
    assert state['current_open_original_ids'] == sorted(k for k in after if after[k]['status'] == 'OPEN')
    masks = json.loads((root / 'source_snapshot/repo/research/nine/gates/A2_MASK_FRONTIER.json').read_bytes())
    statuses = {r['id']: r['status'] for r in masks['rows']}
    universe = {''.join(x[:3]) + '/' + ''.join(x[3:]) for x in itertools.product('01', repeat=5)}
    assert len(statuses) == 32 and set(statuses) == universe
    opened = {k for k, v in statuses.items() if v == 'OPEN'}
    closed = {k for k, v in statuses.items() if v == 'CLOSED_STRICT'}
    assert len(opened) == 24 and len(closed) == 8 and opened | closed == universe
    def reverse(x):
        a, b = x.split('/')
        return a[::-1] + '/' + b[::-1]
    assert all(statuses[m] == statuses[reverse(m)] and reverse(reverse(m)) == m for m in universe)
    classes = {tuple(sorted({m, reverse(m)})) for m in opened}
    assert len(classes) == 14
    remaining = opened - {'001/00', '100/00'}
    assert len(remaining) == 22 and len({tuple(sorted({m, reverse(m)})) for m in remaining}) == 13
    assert state['new_original_closures'] == state['new_mask_closures'] == 0
    assert manifest['new_original_closures'] == manifest['new_mask_closures'] == 0
    assert state['strict011_geometry_adapter_installed'] is False
    assert manifest['root_adapter_installed'] is False
    assert state['portable_geometric_proof'] is False and manifest['self_contained_geometric_proof'] is False
    return {'status': 'PASS_CHECKPOINT_IDENTITIES_AND_METADATA_ONLY', 'verified_files': len(files),
            'current_originals': {'closed': 222, 'open': 9, 'total': 231},
            'masks': {'closed_strict': 8, 'open': 24, 'total': 32},
            'remaining_reversal_classes': 14, 'new_proof_credit': 0,
            'numerical_solver_called': False, 'exact_geometric_tree_replay': False}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Assertions must be enabled for checkpoint verification')
    parser = argparse.ArgumentParser()
    parser.add_argument('--checkpoint', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    print(json.dumps(check(args.checkpoint.resolve()), indent=2))
