#!/usr/bin/env python3
"""Thin B16 checkpoint identities and exact delta; no arithmetic replay."""
from pathlib import Path
from copy import deepcopy
import argparse
import hashlib
import json

CHANGED = (2, 3, 6, 8, 10, 12, 20, 22, 35, 37, 39, 41, 43, 44)
TREE = 'native/d_work/b16_restored45_interval_continuation_v1'
NATIVE_ROOT = '/workspace/scratch/f9f48fcfb253'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def check(root, prior_tree=None):
    root = Path(root).resolve()
    inventory = read(root / 'INPUT_MANIFEST.json')
    assert inventory['schema'] == 'B16_interval_terminal_publication_inventory_v1'
    actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
    assert actual == set(inventory['files']) | {'INPUT_MANIFEST.json'}
    for name, pin in inventory['files'].items():
        p = root / name
        assert p.resolve().is_relative_to(root)
        assert p.stat().st_size == pin['bytes'] and sha(p) == pin['sha256'], name
    manifest = read(root / TREE / 'manifest.json')
    assert sha(root / TREE / 'manifest.json') == '941243cf54bde2070916a29c95c1a2bdba7b5c5e8651ec690c1f482788c210db'
    report_path = root / 'native/d_work/B16_INTERVAL_CONTINUATION45_FRESH_EXACT_REPLAY.json'
    assert sha(report_path) == '03754a15723bc8e9fc67a685a980ccaa50d034487ca94b827849d1acc31be451'
    report = read(report_path); reference = read(root / 'PUBLISHED_DEPENDENCIES.json')
    assert (report['nodes'], report['excluded_leaves'], report['open_leaves'], report['local_rounds'],
            report['local_deductions'], report['local_printed_rows']) == (45, 16, 14, 21, 2324, 7865)
    assert report['whole_original_proved'] is report['entire_registered_original_domain_retained'] is False
    assert report['complete_unions'] == {'proxy': 7, 'angle': 8}
    assert report['new_original_ledger_credit'] == report['new_mask_ledger_credit'] == 0
    assert report['certificate_sha256'] == sha(root / TREE / 'manifest.json')
    screen = read(root / 'native/d_work/B16_RESTORED45_LEAF_INTERVAL_SCREEN.json')
    candidates = {row['node']: row for row in screen['candidates']}
    assert sorted(candidates) == list(CHANGED)
    old = read(root / 'published_dependency_metadata/PRIOR_45_MANIFEST.json')
    assert sha(root / 'published_dependency_metadata/PRIOR_45_MANIFEST.json') == reference['prior_tree_manifest_sha256']
    expected = deepcopy(old)
    expected['acceptance_status'] = 'NEW_INTERVAL_TERMINAL_CONTINUATION_FRESH_COMPLETE_REPLAY_PENDING'
    for name in ('B16_RESTORED45_LEAF_INTERVAL_SCREEN.json', 'prepare_b16_interval_continuation_v1.py',
                 'check_b16_restored_leaf_intervals_v1.py'):
        expected['sources'][NATIVE_ROOT + '/d_work/' + name] = sha(root / 'native/d_work' / name)
    entries = {entry['index']: entry for entry in manifest['nodes']}
    aliases = {entry['index']: entry for entry in reference['old45_payload_aliases']}
    assert set(entries) == set(aliases) == set(range(45))
    published = read(root / 'published_dependency_metadata/PUBLISHED_185_MEMBER_MANIFEST.json')['members']
    for index, alias in aliases.items():
        assert alias['sha256'] == old['nodes'][index]['sha256']
        member = published[alias['published_member']]
        assert (alias['sha256'], alias['bytes']) == (member['sha256'], member['bytes'])
        assert alias['new_tree_uses_published_bytes'] is (index not in CHANGED)
        if index in CHANGED:
            p = root / TREE / entries[index]['file']
            assert sha(p) == entries[index]['sha256']
            node = read(p)
            assert node['children'] == [] and node['record']['rounds'] == []
            assert node['status'] == node['record']['status'] == 'CANDIDATE_CLOSED'
            assert node['record']['terminal'] == candidates[index]['terminal'] and 'final' not in node['record']
            expected['nodes'][index]['sha256'] = sha(p)
            expected['nodes'][index]['status'] = 'CANDIDATE_CLOSED'
        else:
            assert entries[index]['sha256'] == alias['sha256']
    assert manifest == expected
    prior_checked = False
    if prior_tree is not None:
        prior_tree = Path(prior_tree).resolve()
        assert sha(prior_tree / 'manifest.json') == reference['prior_tree_manifest_sha256']
        for index, alias in aliases.items():
            p = prior_tree / alias['file']
            assert p.stat().st_size == alias['bytes'] and sha(p) == alias['sha256']
            if index not in CHANGED:
                continue
            prior = read(p); wanted = deepcopy(prior)
            assert prior['record']['initial'] == prior['record']['final'] == prior['initial']
            assert prior['record']['rounds'] == []
            wanted['status'] = wanted['record']['status'] = 'CANDIDATE_CLOSED'
            wanted['record']['terminal'] = candidates[index]['terminal']
            del wanted['record']['final']
            assert read(root / TREE / alias['file']) == wanted
        prior_checked = True
    return dict(status='PASS_B16_INTERVAL_CONTINUATION_PACKET_IDENTITIES',
        files=len(inventory['files']), bytes=inventory['total_bytes'],
        manifest_sha256=sha(root / 'INPUT_MANIFEST.json'),
        new_terminal_payloads=14, unchanged_published_aliases=31,
        all45_prior_payloads_checked=prior_checked, weighted_arithmetic_repeated=False,
        new_original_cells=0, new_masks=0)


def main():
    if not __debug__:
        raise RuntimeError('Exact identity checks require assertions')
    parser = argparse.ArgumentParser(); parser.add_argument('--prior-tree', type=Path)
    args = parser.parse_args()
    print(json.dumps(check(Path(__file__).resolve().parent, args.prior_tree)), flush=True)


if __name__ == '__main__':
    main()
