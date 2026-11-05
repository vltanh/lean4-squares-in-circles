#!/usr/bin/env python3
"""Attach the exact published B462 two-round record to its registered root.

The missing historical capture program and old run metadata are not premises
of this new attachment. The unchanged checker must reconstruct the whole root
and validate the record's complete initial state before any bound round.
"""
from pathlib import Path
from copy import deepcopy
import hashlib
import json
import os

ROOT = Path('/workspace/scratch/f9f48fcfb253')
HERE = Path(__file__).resolve().parent
OLD = ROOT / 'b_work/recovery_20261105/B462_first_center_weighted_prefix_v1'
OUTPUT = HERE / 'B462_preserved_two_round_whole_attachment_v1'
ROOT_SHA = '24d91df8ce4a2472ebf76ac4b73c1fc07c58fbb5f9c213be8b415d1b8b2cc302'
NODE_SHA = 'b3e57974e756c308a4121f2f2e4a0e515dec22c0c20d97ad3077c32819c92d64'
OLD_MANIFEST_SHA = '6e58fa1ab35c8b247b3c1b2979cf8f63e0670f955275e94f8464543317d71a7d'
EXCLUDED = {
    str(ROOT / 'repo/research/nine/.runs/b462_fresh_accepted_center_atomic_v1/PREVIOUS_COMPLETE_MANIFEST.json'):
        'ce7510a78c54c6d8eadf3c1e0f549ec3b84b8cc1d8bc57c5a7b53065571b1cc2',
    str(ROOT / 'b_work/recovery_20261105/capture_b462_center_weighted_prefix_v1.py'):
        'c2f205204abb4a6ba375749195a2b03db08f26b289ff0cbd34ba365c85ca8571'}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    assert not OUTPUT.exists()
    assert sha(OLD / 'manifest.json') == OLD_MANIFEST_SHA
    assert sha(OLD / 'node_0000.json') == NODE_SHA
    old = json.loads((OLD / 'manifest.json').read_text())
    node = json.loads((OLD / 'node_0000.json').read_text())
    parent = Path(old['parent']['path'])
    assert parent.name == 'negative-462e78d2e2d8be05.json'
    assert sha(parent) == old['parent']['sha256'] == ROOT_SHA
    root = json.loads(parent.read_text())
    expected_path = [['angle', 3, 0], ['angle_cut', [0, '0'], 0],
                     ['position_cut', [11, '1/2'], 1], ['f_side_escape', [5, 7], [1]]]
    assert root['id'] == 'negative-462e78d2e2d8be05' and root['path'] == expected_path
    assert root['scope'] == 'WHOLE_UNCHANGED_ORIGINAL_PARENT'
    assert root['all_nine_originals_retained'] and root['all_original_corners_and_pairs_retained']
    assert root['strict_CD_retained'] and root['status'] == 'OPEN'
    assert node['initial'] == node['record']['initial'] == root['final']
    assert node['index'] == node['depth'] == 0 and node['parent'] is None and node['choice'] is None
    assert node['status'] == node['record']['status'] == 'OPEN' and node['children'] == []
    assert len(node['record']['rounds']) == 2 and 'terminal' not in node['record']
    assert node['record']['final']['id'] == root['id']
    assert node['record']['final']['path'] == expected_path
    assert old['nodes'] == [dict(index=0, file='node_0000.json', sha256=NODE_SHA, status='OPEN', depth=0)]
    for path, digest in EXCLUDED.items():
        assert old['sources'][path] == digest
        assert not Path(path).exists(), 'Do not recreate historical unavailable provenance'
    retained_sources = {p: h for p, h in old['sources'].items() if p not in EXCLUDED}
    assert len(old['sources']) == 55 and len(retained_sources) == 53
    for group in (retained_sources, old['accepted_geometric_sources']):
        for path, digest in group.items():
            assert sha(path) == digest, path
    checker = ROOT / 'b_work/verify_b_accepted_center_disk_tree_v1.py'
    assert sha(checker) == '5e18bec014381a657dde410a1a457ed1f8d7ae02d16e95de3b3d6040ff6cd0c0'
    OUTPUT.mkdir()
    os.link(OLD / 'node_0000.json', OUTPUT / 'node_0000.json')
    binding = dict(schema='B462_preserved_raw_record_registered_whole_attachment_v1',
        original_id=root['id'], original_path=expected_path, scope='WHOLE_UNCHANGED_ORIGINAL_PARENT',
        parent=old['parent'], raw_node_sha256=NODE_SHA, raw_node_bytes_unchanged=True,
        complete_initial_state_equals_registered_root_final=True, rows_and_rounds_unchanged=True,
        mathematical_ancestry_supplied_by_fresh_registered_root_replay=True,
        inherited_capture_program_or_old_run_metadata_supplies_no_mathematical_premise=True,
        unavailable_historical_provenance=EXCLUDED,
        old_run_directory_recreated=False, missing_capture_program_recreated=False,
        historical_manifest_sha256_for_provenance_only=OLD_MANIFEST_SHA,
        published_commit='35ac6d675d74f013a59804ef5506b74b005b59d6',
        independent_checker=dict(path=str(checker), sha256=sha(checker)),
        retained_source_sha256=retained_sources, accepted_geometric_sources=old['accepted_geometric_sources'],
        producer_sha256=sha(__file__), arithmetic_replay_pending=True,
        numerical_search_started=False, new_original_cells=0, new_masks=0)
    binding_path = OUTPUT / 'ATTACHMENT_BINDING.json'
    with binding_path.open('x') as f:
        json.dump(binding, f, indent=2); f.write('\n')
    manifest = deepcopy(old)
    manifest['sources'] = dict(retained_sources)
    manifest['sources'][str(Path(__file__).resolve())] = sha(__file__)
    manifest['sources'][str(binding_path)] = sha(binding_path)
    manifest['acceptance_status'] = 'NEW_PRESERVED_RECORD_WHOLE_ROOT_ATTACHMENT_FRESH_EXACT_REPLAY_PENDING'
    manifest_path = OUTPUT / 'manifest.json'
    with manifest_path.open('x') as f:
        json.dump(manifest, f, indent=2); f.write('\n')
    assert sha(OUTPUT / 'node_0000.json') == NODE_SHA
    for path, digest in manifest['sources'].items():
        assert sha(path) == digest
    print(json.dumps(dict(status='PREPARED_NEW_WHOLE_ROOT_ATTACHMENT_UNCHANGED_RAW_RECORD',
        manifest_sha256=sha(manifest_path), binding_sha256=sha(binding_path), node_sha256=NODE_SHA,
        output=str(OUTPUT), arithmetic_replay_pending=True, old_run_directory_recreated=False)), flush=True)


if __name__ == '__main__':
    main()
