#!/usr/bin/env python3
"""Independent byte/domain/cover audit; no bound-arithmetic replay or LP."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
from collections import Counter
import hashlib
import json

ROOT = Path('/workspace/scratch/f9f48fcfb253')
OLD = ROOT / 'b_work/recovery_20261105/reassembled_B16a_published_prefix_v1'
NEW = ROOT / 'd_work/b16_restored45_interval_continuation_v1'
CHANGED = (2, 3, 6, 8, 10, 12, 20, 22, 35, 37, 39, 41, 43, 44)
PINS = {
    'd_work/check_b16_restored_leaf_intervals_v1.py': '3ef8d0ee7e7d286b205b8fb07970619de553f394489487a39b26b86786762cf3',
    'd_work/prepare_b16_interval_continuation_v1.py': '5a71c0da0cb42c97d70dd1e31ce336c73d6db1dd2608d1d875c45c82f8e8a611',
    'd_work/B16_RESTORED45_LEAF_INTERVAL_SCREEN.json': 'e9301b6b8ca119da1724c24e00e35e6e030cfda7b071ee7aa3f5fcb638730790',
    'd_work/B16_INTERVAL_CONTINUATION45_FRESH_EXACT_REPLAY.json': '03754a15723bc8e9fc67a685a980ccaa50d034487ca94b827849d1acc31be451',
    'd_work/b16_restored45_interval_continuation_v1/manifest.json': '941243cf54bde2070916a29c95c1a2bdba7b5c5e8651ec690c1f482788c210db',
    'b_work/recovery_20261105/reassembled_B16a_published_prefix_v1/manifest.json': 'b90924544fd382d2bc31c536ddd8b12be13d7748abe262106d40661b325283a5',
    'b_work/recovery_20261105_reset2/RESTORED_B16A_45_ACCEPTED_CENTER_FRESH_EXACT_REPLAY.json': '6957aef8e8867eb8c36ff8df268f448896f27e203e59e76547000a926b31fbfa',
    'b_work/B16A_MERGED_I21_I22_RESTRICTION.json': '142b74254b59e00267298ea59fa27bef68b392a220f9509aa4a88221f514d5cc',
    'b_work/verify_b_accepted_center_disk_tree_v1.py': '5e18bec014381a657dde410a1a457ed1f8d7ae02d16e95de3b3d6040ff6cd0c0',
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def main():
    if not __debug__:
        raise RuntimeError('Exact identity checks require assertions')
    for name, digest in PINS.items():
        assert sha(ROOT / name) == digest, name
    screen = read(ROOT / 'd_work/B16_RESTORED45_LEAF_INTERVAL_SCREEN.json')
    report = read(ROOT / 'd_work/B16_INTERVAL_CONTINUATION45_FRESH_EXACT_REPLAY.json')
    old_report = read(ROOT / 'b_work/recovery_20261105_reset2/RESTORED_B16A_45_ACCEPTED_CENTER_FRESH_EXACT_REPLAY.json')
    before = read(OLD / 'manifest.json'); after = read(NEW / 'manifest.json')
    restriction = read(ROOT / 'b_work/B16A_MERGED_I21_I22_RESTRICTION.json')
    assert restriction['schema'] == 'B_merged_original_I_rectangle_restriction_v1'
    assert restriction['covered_original_I_tiles'] == [[2, 1], [2, 2]]
    assert restriction['original'] == 8 and restriction['parts'] == 4
    assert restriction['rectangle'] == [['-163627/2097152', '2457813/4194304'], ['-91/120', '91/120']]
    assert before['parent'] == after['parent'] == {
        'path': str(ROOT / 'b_work/B16A_MERGED_I21_I22_RESTRICTION.json'),
        'sha256': PINS['b_work/B16A_MERGED_I21_I22_RESTRICTION.json']}
    assert report['entire_registered_original_domain_retained'] is False
    assert report['whole_original_proved'] is False and report['complete'] is False
    assert report['initial_original_id'] == 'negative-16a2fc93c8d133f0'
    assert report['initial_path'] == restriction['final']['path']
    assert report['certificate_sha256'] == PINS['d_work/b16_restored45_interval_continuation_v1/manifest.json']
    assert (report['nodes'], report['excluded_leaves'], report['open_leaves'],
            report['local_rounds'], report['local_deductions'], report['local_printed_rows']) == (45, 16, 14, 21, 2324, 7865)
    assert report['complete_unions'] == {'proxy': 7, 'angle': 8}
    assert report['new_original_ledger_credit'] == report['new_mask_ledger_credit'] == 0
    assert report['all_shared_closed_faces_retained'] is True
    assert (old_report['nodes'], old_report['excluded_leaves'], old_report['open_leaves']) == (45, 2, 28)
    expected = deepcopy(before)
    expected['acceptance_status'] = 'NEW_INTERVAL_TERMINAL_CONTINUATION_FRESH_COMPLETE_REPLAY_PENDING'
    for name in ('d_work/B16_RESTORED45_LEAF_INTERVAL_SCREEN.json',
                 'd_work/prepare_b16_interval_continuation_v1.py',
                 'd_work/check_b16_restored_leaf_intervals_v1.py'):
        expected['sources'][str(ROOT / name)] = PINS[name]
    candidates = {entry['node']: entry for entry in screen['candidates']}
    assert sorted(candidates) == list(CHANGED)
    assert [node['index'] for node in before['nodes']] == list(range(45))
    assert [node['index'] for node in after['nodes']] == list(range(45))
    small = {}; payloads = []; terminal_counts = Counter(); sums = [0, 0, 0]
    audits = {item['index']: item for item in report['node_audits']}
    assert set(audits) == set(range(45))
    for old_entry, new_entry in zip(before['nodes'], after['nodes']):
        index = old_entry['index']; path = old_entry['file']
        assert sha(OLD / path) == old_entry['sha256']
        assert sha(NEW / path) == new_entry['sha256']
        old = read(OLD / path); new = read(NEW / path)
        wanted = deepcopy(old)
        if index in CHANGED:
            assert old['status'] == old['record']['status'] == 'OPEN' and old['children'] == []
            assert old['initial'] == old['record']['initial'] == old['record']['final']
            assert old['record']['rounds'] == [] and candidates[index]['prior_rounds'] == 0
            wanted['status'] = wanted['record']['status'] = 'CANDIDATE_CLOSED'
            wanted['record']['terminal'] = candidates[index]['terminal']
            del wanted['record']['final']
            assert new == wanted
            expected['nodes'][index]['status'] = 'CANDIDATE_CLOSED'
            expected['nodes'][index]['sha256'] = new_entry['sha256']
            terminal_counts[new['record']['terminal']['kind']] += 1
            audit = audits[index]['audit']
            assert audit['status'] == 'PASS_EXCLUDED_PHYSICAL_DOMAIN'
            assert (audit['rounds'], audit['deductions'], audit['printed_rows_checked']) == (0, 0, 0)
        else:
            assert (OLD / path).read_bytes() == (NEW / path).read_bytes()
        assert new['record']['rounds'] == old['record']['rounds']
        assert new['initial'] == old['initial'] and new['children'] == old['children']
        assert all(new.get(key) == old.get(key) for key in ('index', 'parent', 'depth', 'choice', 'split', 'complete_closed_children'))
        audit = audits[index]
        assert (audit['parent'], audit['depth'], audit['choice']) == (new['parent'], new['depth'], new['choice'])
        for j, field in enumerate(('rounds', 'deductions', 'printed_rows_checked')):
            sums[j] += audit['audit'][field]
        payloads.append(dict(index=index, file=path, old_sha256=old_entry['sha256'],
            new_sha256=new_entry['sha256'], changed=index in CHANGED))
        small[index] = {key: new.get(key) for key in ('index', 'parent', 'depth', 'choice', 'children', 'split', 'status')}
    assert after == expected
    assert sums == [21, 2324, 7865]
    assert terminal_counts == {'accepted_center_interval_terminal': 13, 'empty_difference': 1}
    visited = set(); covers = Counter(); leaves = []
    def visit(index, parent, depth, choice):
        assert index not in visited; visited.add(index); node = small[index]
        assert (node['parent'], node['depth'], node['choice']) == (parent, depth, choice)
        children = node['children']
        if not children:
            leaves.append((index, node['status'] == 'CANDIDATE_CLOSED'))
            return node['status'] == 'CANDIDATE_CLOSED'
        assert len(children) == len(set(children))
        kind = node['split']['kind']; covers[kind] += 1
        expected_choices = [[0, -1], [0, 1], [1, -1], [1, 1]] if kind == 'proxy' else [0, 1]
        assert kind in ('proxy', 'angle') and len(children) == len(expected_choices)
        outcomes = [visit(child, index, depth + 1, selected) for child, selected in zip(children, expected_choices)]
        closed = all(outcomes)
        assert node['status'] == ('CANDIDATE_COVER_CLOSED' if closed else 'OPEN')
        return closed
    assert visit(0, None, 0, None) is False
    assert visited == set(range(45)) and covers == {'proxy': 7, 'angle': 8}
    assert len(leaves) == 30 and sum(closed for _, closed in leaves) == 16
    for path, digest in report['source_sha256'].items():
        assert sha(path) == digest, path
    witness = candidates[43]['terminal']
    assert witness['kind'] == 'empty_difference' and witness['pair'] == [5, 8] and witness['axis'] == 1
    gap = F(witness['lower']) - F(witness['upper'])
    assert gap > 0
    for name, digest in PINS.items():
        assert sha(ROOT / name) == digest
    result = dict(status='PASS_INDEPENDENT_B16_INTERVAL_CONTINUATION_BYTE_SCOPE_AND_COVER_AUDIT',
        source_review_tool_sha256=sha(__file__), reviewed_inputs=PINS,
        report_source_pins_rehashed=len(report['source_sha256']),
        retained_nodes=45, unchanged_node_payloads=31, changed_terminal_leaves=list(CHANGED),
        all_prior_initials_rounds_children_and_covers_preserved=True,
        ancestor_status_updates=[], complete_covers=dict(covers),
        new_terminal_kinds=dict(terminal_counts), leaf43_exact_difference_gap=str(gap),
        terminal_leaves=30, excluded_leaves=16, open_leaves=14,
        full_new_replay_report_sha256=PINS['d_work/B16_INTERVAL_CONTINUATION45_FRESH_EXACT_REPLAY.json'],
        full_weighted_arithmetic_repeated_by_this_review=False,
        physical_scope='merged closed I21/I22 of negative-16a2fc93c8d133f0 only',
        new_original_cells=0, new_masks=0, numerical_solver_called=False, node_byte_audits=payloads)
    output = Path(__file__).resolve().parent / 'BYTE_SCOPE_COVER_AUDIT.json'
    with output.open('x') as handle:
        json.dump(result, handle, indent=2); handle.write('\n')
    print(json.dumps(dict(status=result['status'], report_sha256=sha(output),
        nodes=45, unchanged=31, changed=14, source_pins=result['report_source_pins_rehashed'])), flush=True)


if __name__ == '__main__':
    main()
