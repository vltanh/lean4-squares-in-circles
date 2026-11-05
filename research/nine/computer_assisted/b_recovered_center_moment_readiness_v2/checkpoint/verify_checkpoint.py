#!/usr/bin/env python3
"""Read-only inventory/scope check; never run a numerical or exact proof engine."""
from pathlib import Path
import argparse
import hashlib
import json


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as source:
        for chunk in iter(lambda: source.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def main():
    if not __debug__:
        raise RuntimeError('Verification assertions must be enabled')
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--workspace', type=Path)
    args = parser.parse_args()
    root = args.packet.resolve()

    def read(relative):
        p = root / relative
        assert p.resolve().is_relative_to(root)
        return json.loads(p.read_text())

    inventory = read('INPUT_MANIFEST.json')
    assert inventory['schema'] == 'B_reset2_source_readiness_checkpoint_inventory_v1'
    for relative, meta in inventory['files'].items():
        p = root / relative
        assert p.resolve().is_relative_to(root) and p.is_file() and not p.is_symlink()
        assert p.stat().st_size == meta['bytes'] and digest(p) == meta['sha256'], relative
    actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
    assert actual == set(inventory['files']) | {'INPUT_MANIFEST.json'}
    note = read('CHECKPOINT.json')
    assert note['new_original_cells'] == note['new_masks'] == 0
    assert note['accepted_counts'] == {'closed_originals': 222, 'total_originals': 231,
                                      'closed_masks': 8, 'total_masks': 32}
    assert note['numerical_search_started'] is False
    assert note['missing_old_B462_capture_script_recreated'] is False
    assert note['lost_B16_105_or_107_suffix_used'] is False
    prefix = 'native/b_work/recovery_20261105_reset2/'
    freeze = read(prefix + 'B_CENTER_EXACT_MOMENT_BOUNDED_READINESS_FREEZE_V1.json')
    assert len(freeze['files']) == 396 and freeze['numerical_search_started'] is False
    assert freeze['independent_checker_unchanged'] and freeze['no_new_mathematical_row_family']
    expected = {'B16A': (45, 2, 28, 21, 2324, 7865, False),
                'B462': (1, 0, 1, 2, 214, 490, True)}
    for case in freeze['cases']:
        label = case['label']; counts = expected[label]
        r = read(prefix + Path(case['exact_report']).name)
        assert r['status'] == 'PASS_PARTIAL_PHYSICAL_TREE'
        assert not r['whole_original_proved'] and not r['complete']
        fields = ('nodes', 'excluded_leaves', 'open_leaves', 'local_rounds',
                  'local_deductions', 'local_printed_rows', 'entire_registered_original_domain_retained')
        assert tuple(r[k] for k in fields) == counts
        assert r['certificate_sha256'] == case['source_manifest_sha256']
        assert digest(root / prefix / Path(case['exact_report']).name) == case['exact_report_sha256']
        launch = read(prefix + label + '_CENTER_EXACT_MOMENT_HELD_LAUNCH_V1.json')
        assert all(launch[k] == v for k, v in case.items())
        assert launch['common_source_freeze']['sha256'] == digest(root / prefix / 'B_CENTER_EXACT_MOMENT_BOUNDED_READINESS_FREEZE_V1.json')
        assert case['numerical_search_started'] is False and case['status'].startswith('HOLD_')
        assert case['command'][-10:] == ['--rounds', '2', '--existing-rounds', '1',
            '--proxy-rounds', '0', '--max-depth', '24', '--max-new-nodes', '64']
    parity = read(prefix + 'B16_ACTUAL_EXACT_MOMENT_LITERAL_PARITY.json')
    assert parity['rows_compared'] == 3072 and parity['pair_intervals'] == 36
    assert parity['complete_coefficients_rhs_names_and_order_equal'] and parity['numerical_LP_solves'] == 0
    assert len(parity['malformed_callers_rejected']) == 4
    members = read('dependencies/PUBLISHED_185_MEMBER_MANIFEST.json')['members']
    files = read('dependencies/PUBLISHED_35AC_PUBLICATION_MANIFEST.json')['files']
    aliases = read('PUBLISHED_PAYLOAD_ALIASES.json')
    assert aliases['published_commit'] == '35ac6d675d74f013a59804ef5506b74b005b59d6'
    seen = set()
    for row in aliases['aliases']:
        assert row['target'] not in seen; seen.add(row['target'])
        table = members if row['kind'] == 'archive_member' else files
        assert row['kind'] in ('archive_member', 'publication_file')
        assert table[row['published_path']] == {'bytes': row['bytes'], 'sha256': row['sha256']}
    assert len(seen) == 93
    native_checked = 0
    if args.workspace:
        workspace = args.workspace.resolve()
        old_root = '/workspace/scratch/f9f48fcfb253/'
        for path, wanted in freeze['files'].items():
            assert path.startswith(old_root)
            p = workspace / path[len(old_root):]
            assert p.resolve().is_relative_to(workspace) and digest(p) == wanted, path
            native_checked += 1
        for row in aliases['aliases']:
            p = workspace / row['target']
            assert p.resolve().is_relative_to(workspace)
            assert p.stat().st_size == row['bytes'] and digest(p) == row['sha256'], row['target']
        parent = json.loads((workspace / 'b_work/recovery_20261105/registered_B_initial_states/negative-462e78d2e2d8be05.json').read_text())
        node = json.loads((workspace / 'b_work/recovery_20261105_reset2/B462_preserved_two_round_whole_attachment_v1/node_0000.json').read_text())
        assert parent['scope'] == 'WHOLE_UNCHANGED_ORIGINAL_PARENT'
        assert node['initial'] == node['record']['initial'] == parent['final']
        assert len(node['record']['rounds']) == 2 and node['children'] == []
        assert not (workspace / 'b_work/recovery_20261105/capture_b462_center_weighted_prefix_v1.py').exists()
        assert not (workspace / 'repo/research/nine/.runs/b462_fresh_accepted_center_atomic_v1').exists()
    print(json.dumps({'status': 'PASS_B_SOURCE_READINESS_INVENTORY_AND_SCOPE',
        'packaged_files': len(inventory['files']), 'published_payload_aliases': len(seen),
        'native_readiness_pins_rehashed': native_checked, 'arithmetic_replayed': False,
        'numerical_search_started': False, 'new_original_cells': 0, 'new_masks': 0}), flush=True)


if __name__ == '__main__':
    main()
