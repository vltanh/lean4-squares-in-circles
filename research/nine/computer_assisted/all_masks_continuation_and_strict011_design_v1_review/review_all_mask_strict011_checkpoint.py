#!/usr/bin/env python3
"""Independent byte/metadata review; no geometric proof or producer imports."""
from pathlib import Path
from hashlib import sha256
from itertools import product, combinations
from collections import Counter
import json
import subprocess

W = Path(__file__).resolve().parents[1]
P = W / 'd_work/all_masks_continuation_and_strict011_design_v1'
EXPECTED = '9293308c9d23acfaeefe88b6727c293a921a9d6f9384fd22722d5424c5a6821e'

def digest(data):
    return sha256(data).hexdigest()

def read(name):
    return json.loads((P / name).read_text())

if not __debug__:
    raise RuntimeError('Assertions are required')
assert digest((P / 'PUBLICATION_MANIFEST.json').read_bytes()) == EXPECTED
manifest = read('PUBLICATION_MANIFEST.json')
actual = {str(q.relative_to(P)) for q in P.rglob('*') if q.is_file()}
assert not any(q.is_symlink() for q in P.rglob('*'))
assert actual == set(manifest['files']) | {'PUBLICATION_MANIFEST.json'}
for name, pin in manifest['files'].items():
    b = (P / name).read_bytes()
    assert len(b) == pin['bytes'] and digest(b) == pin['sha256'], name
assert len(manifest['files']) == 59
assert sum(p['bytes'] for p in manifest['files'].values()) == 2920531

plan = read('plan/PLAN_BINDINGS.json')
design = read('strict011_design/SOURCE_MAP.json')
recovery = read('SOURCE_RECOVERY_AND_RECONCILIATION.json')
sources = {}
for item in list(plan['sources'].values()) + design['sources']:
    key = item['path']
    pin = {'sha256': item['sha256'], 'bytes': item['bytes']}
    assert key not in sources or sources[key] == pin
    sources[key] = pin
assert len(sources) == 38 and set(sources) == set(recovery['sources'])
origin_counts = Counter()
source_audits = []
for name, pin in sorted(sources.items()):
    rec = recovery['sources'][name]
    assert all(rec[k] == v for k, v in pin.items())
    assert rec['packaged_path'] == 'source_snapshot/' + name
    packaged = (P / rec['packaged_path']).read_bytes()
    assert len(packaged) == pin['bytes'] and digest(packaged) == pin['sha256']
    origin = rec['provenance']
    origin_counts[origin['kind']] += 1
    if origin['kind'] == 'unchanged_native_file':
        assert origin['logical_path'] == name
        native = (W / name).read_bytes()
    else:
        assert name.startswith('repo/')
        assert origin['repository_path'] == name[5:]
        if origin['kind'] == 'historical_git_blob':
            assert name == 'repo/research/nine/gates/A2_00100_FIXED_FRONTIER.json'
            assert origin['commit'] == '925e1112814a0758889cafa5c975c27414b86570'
        else:
            assert origin['kind'] == 'published_git_blob'
            assert origin['commit'] == '2c0fb06a27cd568297c2b9320e005eb33ae89cdb'
        native = subprocess.check_output(['git', '-C', str(W / 'repo'), 'show', origin['commit'] + ':' + origin['repository_path']])
    assert native == packaged, name
    source_audits.append({'path': name, **pin, 'origin': origin, 'independent_byte_comparison': 'PASS'})

for name, pin in plan['outputs'].items():
    assert (P / 'plan' / name).read_bytes() == (W / pin['path']).read_bytes()
for name, pin in design['prepared_files'].items():
    b = (P / 'strict011_design' / name).read_bytes()
    assert digest(b) == pin['sha256'] and len(b) == pin['bytes']
    assert b == (W / 'global_work/strict_011_root_adapter_design' / name).read_bytes()
fresh = json.loads((W / 'd_work/ALL_MASK_PLAN_HISTORICAL_METADATA_FRESH.json').read_text())
assert fresh == read('plan/PLAN_METADATA_CHECK.json')

historical = read('source_snapshot/repo/research/nine/gates/A2_00100_FIXED_FRONTIER.json')
current = read('CURRENT_FIXED_REGISTER_SNAPSHOT.json')
assert (P / 'CURRENT_FIXED_REGISTER_SNAPSHOT.json').read_bytes() == (W / 'repo/research/nine/gates/A2_00100_FIXED_FRONTIER.json').read_bytes()
by_id = lambda r: {c['id']: c for c in r['cells']}
before, after = by_id(historical), by_id(current)
assert len(before) == len(after) == len(historical['cells']) == len(current['cells']) == 231
assert set(before) == set(after)
delta = [key for key in before if before[key] != after[key]]
assert delta == ['positive-821c9a2debeed0aa']
assert before[delta[0]]['status'] == 'OPEN' and after[delta[0]]['status'] == 'CLOSED'
assert Counter(c['status'] for c in before.values()) == {'CLOSED': 221, 'OPEN': 10}
assert Counter(c['status'] for c in after.values()) == {'CLOSED': 222, 'OPEN': 9}
assert all(before[key] == after[key] for key in before if key != delta[0])
state = read('PUBLICATION_STATE.json')
assert sorted(k for k, c in after.items() if c['status'] == 'OPEN') == state['current_open_original_ids']

masks = read('source_snapshot/repo/research/nine/gates/A2_MASK_FRONTIER.json')
rows = {r['id']: r for r in masks['rows']}
all_masks = {''.join(a) + '/' + ''.join(b) for a in product('01', repeat=3) for b in product('01', repeat=2)}
assert set(rows) == all_masks and len(rows) == len(masks['rows']) == 32
reverse = lambda s: s[:3][::-1] + '/' + s[4:][::-1]
opened = {key for key in rows if rows[key]['status'] == 'OPEN'}
closed = {key for key in rows if rows[key]['status'] == 'CLOSED_STRICT'}
assert len(opened) == 24 and len(closed) == 8
assert all(reverse(reverse(k)) == k and rows[reverse(k)]['status'] == rows[k]['status'] for k in rows)
classes = sorted({tuple(sorted({k, reverse(k)})) for k in opened})
assert len(classes) == 14
assert [list(c) for c in classes] == read('plan/PLAN_METADATA_CHECK.json')['remaining_reversal_classes']
remaining = opened - {'001/00', '100/00'}
assert len(remaining) == 22 and len({tuple(sorted({k, reverse(k)})) for k in remaining}) == 13

root = read('strict011_design/FRESH_ROOT_SPEC_PREPARED.json')
assert len(root['physical_originals']) == 9 and len(root['original_corners']) == 36
assert len(root['absolute_original_variable_bounds']) == 54
assert len(root['elementary_necessary_affine_rows']) == root['row_count'] == 159
assert {tuple(x) for x in root['original_pairs']} == set(combinations(range(9), 2))
assert len(root['owned_pair_cover']) == 36
for choice in root['owned_pair_cover']:
    i, j = choice['pair']
    assert choice['alternatives'] == [[o, a, s] for o in (i, j) for a in (0, 1) for s in (-1, 1)]
assert sum(len(x['alternatives']) for x in root['owned_pair_cover']) == 288
assert [(x['pair'], x['bit']) for x in root['exact_mask_edges']] == [([0, 1], 0), ([1, 2], 1), ([2, 3], 1), ([4, 5], 0), ([5, 6], 0)]
assert all(not root['initial'][key] for key in ('path', 'choices', 'differences', 'diagonal'))
assert root['initial']['positions'] == [['-2', '2']] * 18
assert root['accepted_geometry_adapter'] is False and root['proof_credit'] == 0
assert root['solver_called'] is False and root['old_001_ancestry_imported'] is False
categories = Counter(s['category'] for s in design['sources'])
assert categories['legacy_reference_prohibited_import'] == 3
assert categories['discovery_reference_only'] == categories['fixed_original_reference_only'] == 1
assert not manifest['root_adapter_installed'] and not manifest['self_contained_geometric_proof']
assert manifest['new_original_closures'] == manifest['new_mask_closures'] == 0
assert state['portable_geometric_proof'] is False and state['exact_tree_replay_performed_by_checkpoint'] is False

report = {
    'status': 'PASS_INDEPENDENT_SOURCE_IDENTITY_AND_METADATA_REVIEW',
    'scope': 'Read-only packaging, declared design scope, source recovery and ledger snapshot reconciliation; no geometric arithmetic or scalar proof rerun',
    'checkpoint_manifest_sha256': EXPECTED,
    'review_source_sha256': digest(Path(__file__).read_bytes()),
    'files_checked': 59,
    'total_packet_files_including_manifest': 60,
    'bytes_excluding_manifest': 2920531,
    'direct_sources_checked': 38,
    'direct_source_origins': dict(origin_counts),
    'source_audits': source_audits,
    'historical_plan_and_reviews_kept_byte_exact': True,
    'fresh_historical_metadata_entire_json_equal': True,
    'historical_counts': {'closed': 221, 'open': 10},
    'current_counts': {'closed': 222, 'open': 9},
    'only_changed_original_entry': delta[0],
    'other_230_original_entries_unchanged': True,
    'mask_counts': {'closed_strict': 8, 'open': 24, 'open_reversal_classes': 14},
    'strict011_design_counts': {'originals': 9, 'corners': 36, 'pairs': 36, 'cones': 5, 'original_affine_variables': 54, 'elementary_rows': 159, 'owned_pair_alternatives': 288},
    'prohibited_legacy_import_sources': 3,
    'additional_reference_only_sources': 2,
    'transitive_proof_ancestry_not_packaged_or_replayed': True,
    'root_adapter_installed': False,
    'new_proof_credit': 0,
    'repo_or_index_changed_by_review': False,
    'narrow_frozen_whitespace_exceptions': ['source_snapshot/repo/research/nine/A2_COVERAGE_AND_CLOSURE_CONTRACT.md', 'source_snapshot/global_work/ORIGINAL_FOUR_ROW_MASK_TRANSFER_AND_CLOSED_ESCAPE_COVER.md'],
}
out = W / 'b_work/ALL_MASK_STRICT011_CHECKPOINT_INDEPENDENT_REVIEW.json'
with out.open('x') as f:
    json.dump(report, f, indent=2, sort_keys=True)
    f.write('\n')
print(json.dumps({'status': report['status'], 'report': str(out), 'sha256': digest(out.read_bytes()), 'sources': 38, 'files': 60}, indent=2))
