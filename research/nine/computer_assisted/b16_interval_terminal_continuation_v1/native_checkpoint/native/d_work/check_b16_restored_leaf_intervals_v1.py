#!/usr/bin/env python3
"""Exact interval-terminal screen on a published, freshly replayed B16 cover.

This reuses the accepted complete45-node proof explicitly and performs no LP.
It grants no whole-tree or original credit; positive findings need composition.
"""
if not __debug__:
    raise RuntimeError('Exact interval screening requires assertions.')
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from copy import deepcopy
import hashlib
import json
import sys

ROOT = Path('/workspace/scratch/f9f48fcfb253')
sys.path.insert(0, str(ROOT / 'b_work'))
import verify_b_accepted_center_disk_tree_v1 as EXACT

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def state(raw, adapter):
    result = dict(id=raw['id'], path=deepcopy(raw['path']))
    for key in ('angles', 'positions', 'scalar'):
        result[key] = tuple(tuple(map(F, interval)) for interval in raw[key])
    result['differences'] = {tuple(row['pair']): tuple(tuple(map(F, interval)) for interval in row['intervals'])
                             for row in raw['differences']}
    result['choices'] = adapter.choices(result['path'])
    EXACT.CORE.valid_state(result)
    assert EXACT.CORE.state_view(result) == raw
    return result

def proposal(current, adapter):
    K = adapter.K
    V = K.V
    effective, label = V.effective_boxes(current['angles'], current['choices'], K.LEGACY)
    if label is not None:
        return dict(kind='accepted_effective_angle_terminal', label=label)
    positions, heights, insets, label = V.center_bounds(effective, current['positions'], current['choices'], K.LEGACY)
    if label is not None:
        return dict(kind='accepted_center_interval_terminal', label=label)
    scalar = tuple((max(a, c), min(b, d)) for (a, b), (c, d)
                   in zip(current['scalar'], K.analytic(effective)))
    for i, (lo, hi) in enumerate(scalar):
        if lo > hi:
            return dict(kind='empty_analytic_scalar', witness=[str(v) for v in (i, lo, hi)])
    for pair in combinations(range(9), 2):
        physical = V.difference_bounds(pair, positions, insets, K.LEGACY)
        inherited = current['differences'].get(pair, physical)
        actual = tuple((max(a, c), min(b, d)) for (a, b), (c, d) in zip(physical, inherited))
        for axis, (lo, hi) in enumerate(actual):
            if lo > hi:
                return dict(kind='empty_difference', pair=list(pair), axis=axis, lower=str(lo), upper=str(hi))
    return None

def main(output):
    assert not output.exists()
    saved = ROOT / 'b_work/recovery_20261105_reset2/RESTORED_B16A_45_ACCEPTED_CENTER_FRESH_EXACT_REPLAY.json'
    assert sha(saved) == '6957aef8e8867eb8c36ff8df268f448896f27e203e59e76547000a926b31fbfa'
    proof = json.loads(saved.read_text())
    assert proof['nodes'] == 45 and proof['open_leaves'] == 28 and proof['excluded_leaves'] == 2
    assert proof['entire_registered_original_domain_retained'] is False
    for path, expected in proof['source_sha256'].items():
        assert sha(path) == expected, path
    assert sha(EXACT.__file__) == '5e18bec014381a657dde410a1a457ed1f8d7ae02d16e95de3b3d6040ff6cd0c0'
    folder = ROOT / 'b_work/recovery_20261105/reassembled_B16a_published_prefix_v1'
    assert sha(folder / 'manifest.json') == proof['certificate_sha256']
    manifest = json.loads((folder / 'manifest.json').read_text())
    cap = ROOT / 'b_work/recovery_20261105/extracted_b340/unpacked/b340_complete_original_package/accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1'
    adapter = EXACT.Adapter(ROOT / 'b_work/b16a_I32_complete_H_checkpoint', cap)
    expected_open = {row['index'] for row in proof['leaf_table'] if not row['excluded']}
    assert len(expected_open) == 28
    scanned, candidates = [], []
    for entry in manifest['nodes']:
        path = folder / entry['file']
        assert sha(path) == entry['sha256']
        node = json.loads(path.read_text())
        assert node['index'] == entry['index']
        if entry['index'] not in expected_open:
            continue
        assert node['status'] == node['record']['status'] == 'OPEN' and node['children'] == []
        current = state(node['record']['final'], adapter)
        terminal = proposal(current, adapter)
        row = dict(node=entry['index'], node_sha256=entry['sha256'], prior_rounds=len(node['record']['rounds']))
        if terminal is not None:
            assert adapter.verify_early_terminal(current, terminal)
            small = dict(initial=EXACT.CORE.state_view(current), rounds=[], status='CANDIDATE_CLOSED', terminal=terminal)
            audit, after = EXACT.CORE.check_record(small, current, adapter)
            assert after is None
            row.update(terminal=terminal, fresh_terminal_audit=audit, source_final_state_sha256=sha_bytes_state(current))
            candidates.append(row)
        scanned.append(row)
    assert {row['node'] for row in scanned} == expected_open
    adapter.recheck()
    for path, expected in proof['source_sha256'].items():
        assert sha(path) == expected
    assert not any(name in sys.modules for name in ('numpy', 'scipy', 'highspy'))
    report = dict(status='PASS_EXACT_RESTORED_B16_LEAF_INTERVAL_SCREEN',
        original_id=proof['initial_original_id'], scope='merged closed I21/I22 region only',
        complete_prior_proof_sha256=sha(saved), prior_manifest_sha256=sha(folder / 'manifest.json'),
        prior_proof_source_pins_rehashed=len(proof['source_sha256']), prior_node_payloads_rehashed=45,
        open_leaves_scanned=28, exact_terminal_candidates=len(candidates), candidates=candidates,
        scanned=scanned, old_source_and_45node_round_arithmetic_reused=True,
        fresh_candidate_terminal_arithmetic=True, numerical_solves=0, changed_tree_written=False,
        original_or_whole_mask_exclusion_claimed=False, helper_sha256=sha(__file__),
        new_original_cells=0, new_masks=0)
    with output.open('x') as out:
        json.dump(report, out, indent=2, sort_keys=True)
        out.write('\n')
    print(json.dumps(dict(status=report['status'], scanned=28, terminal_candidates=len(candidates), report_sha256=sha(output))))

def sha_bytes_state(value):
    return hashlib.sha256(json.dumps(EXACT.CORE.state_view(value), sort_keys=True, separators=(',', ':')).encode()).hexdigest()

if __name__ == '__main__':
    assert len(sys.argv) == 2
    main(Path(sys.argv[1]))
