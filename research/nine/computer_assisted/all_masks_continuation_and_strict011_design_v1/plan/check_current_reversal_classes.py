#!/usr/bin/env python3
"""Read-only finite metadata check; this is not a geometric proof."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

EXPECTED = [
    ('001/00', '100/00'), ('001/01', '100/10'),
    ('001/10', '100/01'), ('001/11', '100/11'),
    ('011/00', '110/00'), ('011/01', '110/10'),
    ('011/10', '110/01'), ('011/11', '110/11'),
    ('101/00', '101/00'), ('101/01', '101/10'),
    ('101/11', '101/11'), ('111/00', '111/00'),
    ('111/01', '111/10'), ('111/11', '111/11'),
]

def reverse(mask):
    long, short = mask.split('/')
    return long[::-1] + '/' + short[::-1]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--workspace', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    paths = {
        'mask_frontier': args.workspace / 'repo/research/nine/gates/A2_MASK_FRONTIER.json',
        'fixed_original_frontier': args.workspace / 'repo/research/nine/gates/A2_00100_FIXED_FRONTIER.json',
    }
    masks = json.loads(paths['mask_frontier'].read_text())
    originals = json.loads(paths['fixed_original_frontier'].read_text())
    rows = masks['rows']
    complete = {''.join(a) + '/' + ''.join(b)
                for a in itertools.product('01', repeat=3)
                for b in itertools.product('01', repeat=2)}
    assert len(rows) == 32
    assert {row['id'] for row in rows} == complete
    status = {row['id']: row['status'] for row in rows}
    open_masks = {m for m, s in status.items() if s == 'OPEN'}
    closed = {m for m, s in status.items() if s == 'CLOSED_STRICT'}
    assert len(open_masks) == 24 and len(closed) == 8
    assert open_masks.isdisjoint(closed) and open_masks | closed == complete
    assert masks['open_count'] == 24
    assert masks['closed_for_strict_radius_count'] == 8
    actual = sorted({tuple(sorted({m, reverse(m)})) for m in open_masks})
    expected = [tuple(sorted(set(pair))) for pair in EXPECTED]
    assert actual == expected
    assert len(actual) == 14
    assert {m for orbit in actual for m in orbit} == open_masks
    assert sum(map(len, actual)) == 24
    assert all(reverse(reverse(m)) == m and status[reverse(m)] == status[m]
               for m in complete)
    after = open_masks - {'001/00', '100/00'}
    assert len(after) == 22
    assert len({tuple(sorted({m, reverse(m)})) for m in after}) == 13
    assert originals['target_mask'] == '001/00'
    assert originals['reversal_partner'] == '100/00'
    assert originals['original_cells'] == 231
    assert originals['closed_cells'] == 221 and originals['open_cells'] == 10
    assert originals['whole_mask_closed'] is False
    assert len(originals['cells']) == 231
    report = {
        'schema': 'remaining_fixed_mask_reversal_plan_metadata_v1',
        'status': 'PASS_METADATA_ONLY_NO_GEOMETRIC_PROOF',
        'source_sha256': {key: digest(path) for key, path in paths.items()},
        'all_masks': 32, 'closed_strict_masks': 8, 'open_masks': 24,
        'remaining_reversal_classes': [list(o) for o in actual],
        'class_count': 14,
        'conditional_after_complete_00100_and_reversal': {'open_masks': 22, 'classes': 13},
        'fixed_original_cells': {'total': 231, 'closed': 221, 'open': 10},
        'new_mask_closures': 0, 'new_original_cell_closures': 0,
        'numerical_solver_called': False, 'primary_inputs_modified': False,
        'proof_scope': 'Strict radius; exact nine-frame/36-corner/36-pair/five-cone predicates unchanged',
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as out:
        json.dump(report, out, indent=2)
        out.write('\n')
    print(json.dumps({'status': report['status'], 'classes': 14, 'open_masks': 24}))

if __name__ == '__main__':
    main()
