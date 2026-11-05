#!/usr/bin/env python3
"""Replace only certified terminal leaves and resulting ancestor status flags."""
if not __debug__:
    raise RuntimeError('Exact continuation preparation requires assertions.')
from pathlib import Path
from copy import deepcopy
import hashlib
import json

ROOT = Path('/workspace/scratch/f9f48fcfb253')
SOURCE = ROOT / 'b_work/recovery_20261105/reassembled_B16a_published_prefix_v1'
OUTPUT = ROOT / 'd_work/b16_restored45_interval_continuation_v1'
SCREEN = ROOT / 'd_work/B16_RESTORED45_LEAF_INTERVAL_SCREEN.json'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def write(path, value):
    with path.open('x') as out:
        json.dump(value, out, indent=2)
        out.write('\n')

def main():
    assert not OUTPUT.exists()
    assert sha(SCREEN) == 'e9301b6b8ca119da1724c24e00e35e6e030cfda7b071ee7aa3f5fcb638730790'
    screen = json.loads(SCREEN.read_text())
    assert screen['exact_terminal_candidates'] == 14 and screen['open_leaves_scanned'] == 28
    assert sha(SOURCE / 'manifest.json') == screen['prior_manifest_sha256']
    manifest = json.loads((SOURCE / 'manifest.json').read_text())
    assert len(manifest['nodes']) == 45 and manifest['status'] == 'OPEN'
    before, nodes = {}, {}
    for entry in manifest['nodes']:
        path = SOURCE / entry['file']
        assert sha(path) == entry['sha256']
        before[entry['index']] = path.read_bytes()
        nodes[entry['index']] = json.loads(before[entry['index']])
    changed = {row['node']: row for row in screen['candidates']}
    assert len(changed) == 14
    for index, witness in changed.items():
        node = nodes[index]
        assert witness['node_sha256'] == sha(SOURCE / manifest['nodes'][index]['file'])
        assert node['status'] == node['record']['status'] == 'OPEN' and node['children'] == []
        record = node['record']
        assert record['rounds'] == [] and record['initial'] == record['final'] == node['initial']
        assert witness['prior_rounds'] == 0
        record['status'] = 'CANDIDATE_CLOSED'
        record['terminal'] = deepcopy(witness['terminal'])
        del record['final']
        node['status'] = 'CANDIDATE_CLOSED'
    visited = set()
    changed_parent_statuses = []
    def close(index):
        assert index not in visited
        visited.add(index)
        node = nodes[index]
        if not node['children']:
            return node['status'] == 'CANDIDATE_CLOSED'
        outcomes = [close(child) for child in node['children']]
        closed = all(outcomes)
        desired = 'CANDIDATE_COVER_CLOSED' if closed else 'OPEN'
        if node['status'] != desired:
            changed_parent_statuses.append(index)
            node['status'] = desired
        return closed
    assert close(0) is False and visited == set(nodes)
    OUTPUT.mkdir()
    changes, aliases = [], []
    for entry in manifest['nodes']:
        index = entry['index']
        old = json.loads(before[index])
        new = nodes[index]
        assert all(new.get(key) == old.get(key) for key in ('index', 'parent', 'depth', 'choice',
            'initial', 'children', 'split', 'complete_closed_children'))
        if index not in changed:
            assert new['record'] == old['record']
        else:
            expected = deepcopy(old)
            expected['status'] = expected['record']['status'] = 'CANDIDATE_CLOSED'
            expected['record']['terminal'] = deepcopy(changed[index]['terminal'])
            del expected['record']['final']
            assert new == expected
        target = OUTPUT / entry['file']
        if new == old:
            with target.open('xb') as out:
                out.write(before[index])
            aliases.append(dict(index=index, file=entry['file'], sha256=sha(target)))
        else:
            write(target, new)
            changes.append(dict(index=index, file=entry['file'], old_sha256=entry['sha256'],
                new_sha256=sha(target), kind='new_exact_terminal' if index in changed else 'ancestor_status_only'))
        entry['status'] = new['status']
        entry['sha256'] = sha(target)
    manifest['status'] = nodes[0]['status']
    manifest['acceptance_status'] = 'NEW_INTERVAL_TERMINAL_CONTINUATION_FRESH_COMPLETE_REPLAY_PENDING'
    for path in (SCREEN, Path(__file__).resolve(), ROOT / 'd_work/check_b16_restored_leaf_intervals_v1.py'):
        manifest['sources'][str(path)] = sha(path)
    write(OUTPUT / 'manifest.json', manifest)
    note = dict(schema='B16_retained45_exact_interval_terminal_continuation_v1',
        source_manifest=dict(path=str(SOURCE / 'manifest.json'), sha256=sha(SOURCE / 'manifest.json')),
        source_complete_report_sha256=screen['complete_prior_proof_sha256'],
        new_manifest_sha256=sha(OUTPUT / 'manifest.json'), source_nodes=45, retained_nodes=45,
        new_terminal_leaves=sorted(changed), ancestor_status_updates=sorted(changed_parent_statuses),
        all_initials_parent_links_rounds_and_closed_covers_preserved=True,
        unchanged_payload_aliases=aliases, changed_payloads=changes,
        prior_excluded_leaves=2, proposed_excluded_leaves=16, proposed_open_leaves=14,
        regional_scope='merged closed I21/I22 only', new_original_cells=0, new_masks=0,
        numerical_solves=0, fresh_full_arithmetic_gate_pending=True)
    write(OUTPUT / 'CONTINUATION_ATTACHMENT.json', note)
    print(json.dumps(dict(status='PREPARED_B16_14_INTERVAL_TERMINAL_CONTINUATION',
        manifest_sha256=note['new_manifest_sha256'], changed=len(changes), unchanged=len(aliases),
        parent_status_updates=changed_parent_statuses)))

if __name__ == '__main__':
    main()
