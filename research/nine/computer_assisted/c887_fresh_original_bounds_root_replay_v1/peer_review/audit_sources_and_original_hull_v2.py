#!/usr/bin/env python3
"""Read-only byte, original-domain, and exact hull audit; no row replay."""
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
PUBLISHED = HERE / 'published'
DATA = HERE / 'extracted'
TARGET = 'negative-887236b78100baf3'
ROOT_PATH = [['angle', 3, 0], ['angle_cut', [0, '0'], 1],
             ['alternate_four_escape', [1, 7], [1]]]
PINS = {
    'EXPORT_RECEIPT.json': 'cc465194f48c36de9b30c892f8b52ced313b6b00fc99f983e7378a150aa795f3',
    'published/MANIFEST.json': '6429fc802ac002f5d9ae4a2edcdaa2fb0b3473a9778f8499b257dae3aeeba1a5',
    'published/DEPENDENCY_BINDINGS.json': 'f4d8441a29920b6ac05ab2b23cd85fe4e4587953ff9f1a2697bf99ddc1bc4847',
    'extracted/reports/fresh_whole_state_replay.json': 'b28300bc3a89d1e949a057d5965e3e08ea1e543b7a42b1a9740f4587e7d528a8',
    'extracted/reports/rejoined_tree_partial_replay.json': 'fb1aa03208e4c007d79cac5660cf9829faa647c78b606f04b3e5881b2e19df5b',
    'extracted/bindings/old_starting_state.json': 'b24a9fa7675eb4d2330518da7481e5bca75700928035d202eeb9bf964a4adf2d',
}
checked = {}


def pin(path, digest):
    path = Path(path).resolve()
    actual = sha256(path.read_bytes()).hexdigest()
    assert actual == digest, (str(path), digest, actual)
    if str(path) in checked:
        assert checked[str(path)] == digest
    checked[str(path)] = digest


def read(path):
    return json.loads(Path(path).read_text())


def flat(state):
    assert state['id'] == TARGET
    assert set(state) == {'id', 'path', 'angles', 'positions', 'scalar',
                          'differences', 'diagonal'}
    out = {}
    for field, length in [('angles', 9), ('positions', 18), ('scalar', 36)]:
        assert len(state[field]) == length
        for index, endpoints in enumerate(state[field]):
            assert len(endpoints) == 2
            lo, hi = map(F, endpoints)
            assert lo <= hi
            out[field, index] = lo, hi
    for field in ['differences', 'diagonal']:
        table = {tuple(row['pair']): row['intervals'] for row in state[field]}
        assert len(table) == len(state[field]) == 36
        assert set(table) == set(combinations(range(9), 2))
        for pair, axes in table.items():
            assert len(axes) == 2
            for axis, endpoints in enumerate(axes):
                assert len(endpoints) == 2
                lo, hi = map(F, endpoints)
                assert lo <= hi
                out[field, pair, axis] = lo, hi
    assert len(out) == 207
    return out


def printed(record):
    rows = [row for rd in record['rounds'] for row in rd['printed_rows']]
    if record.get('terminal', {}).get('kind') == 'positive_exact_reserve':
        rows.extend(record['terminal']['rows'])
    return rows


def main():
    if not __debug__:
        raise RuntimeError('Assertions required')
    for rel, digest in PINS.items():
        pin(HERE / rel, digest)
    export = read(HERE / 'EXPORT_RECEIPT.json')
    assert export['commit'] == '4efd616976b22fb3dd1802a0314deba461753099'
    for entry in export['published_files']:
        pin(PUBLISHED / entry['path'], entry['sha256'])
        assert (PUBLISHED / entry['path']).stat().st_size == entry['bytes']
    for entry in export['archive_members']:
        pin(DATA / entry['path'], entry['sha256'])
        assert (DATA / entry['path']).stat().st_size == entry['bytes']
    manifest = read(PUBLISHED / 'MANIFEST.json')
    assert manifest['standalone_portable'] is False
    assert manifest['new_original_cells'] == manifest['new_masks'] == 0
    for entry in manifest['files']:
        pin(DATA / entry['path'], entry['sha256'])
        if 'source_path' in entry:
            pin(entry['source_path'], entry['sha256'])
    report = read(DATA / 'reports/fresh_whole_state_replay.json')
    partial = read(DATA / 'reports/rejoined_tree_partial_replay.json')
    dependencies = read(PUBLISHED / 'DEPENDENCY_BINDINGS.json')
    assert dependencies['input_sha256'] == report['input_sha256']
    groups = [('fresh_native_inputs', report['input_sha256']),
              ('partial_integration_inputs', partial['input_sha256']),
              ('independent_checker_modules', partial['checker_dependency_sha256'])]
    for _, table in groups:
        for path, digest in table.items():
            pin(path, digest)
    root = read(DATA / 'records/whole_root_six_rounds.json')
    dg = read(DATA / 'records/dg8/MANIFEST.original.json')
    old = read(DATA / 'bindings/old_starting_state.json')
    assert root['status'] == 'OPEN' and len(root['rounds']) == 6
    assert root['initial']['id'] == TARGET and root['initial']['path'] == ROOT_PATH
    assert root['final']['id'] == TARGET and root['final']['path'] == ROOT_PATH
    assert sum(len(rd['proposals']) for rd in root['rounds']) == 624
    assert len(printed(root)) == 1288
    assert dg['initial'] == root['final'] and dg['pair'] == [3, 6]
    assert dg['completed'] is True and dg['pending'] == []
    assert dg['status'] == 'OPEN' and dg['closed_children'] == 4
    assert dg['new_original_cells'] == dg['new_masks'] == 0
    predecessor = root['source_predecessor']
    pin(predecessor['path'], predecessor['sha256'])
    old_root = read(predecessor['path'])
    assert len(old_root['rounds']) == 3
    assert old_root['initial'] == root['initial']
    assert old_root['rounds'] == root['rounds'][:3]
    expected = [list(c) for c in product((3, 6), (0, 1), (-1, 1))]
    assert dg['alternatives'] == expected and len(dg['children']) == 8
    children, survivors = [], []
    for index, (entry, choice) in enumerate(zip(dg['children'], expected)):
        assert entry['index'] == index and entry['choice'] == choice
        assert entry['file'] == f'child_{index}.json'
        path = DATA / 'records/dg8' / entry['file']
        pin(path, entry['sha256'])
        record = read(path)
        initial = deepcopy(root['final'])
        initial['path'].append(['sat', [3, 6], choice])
        assert record['initial'] == initial
        assert record['status'] == entry['status']
        assert not any('certified_original_root_bound_' in row['name']
                       for row in printed(record))
        audit = report['complete_union']['complete_cover']['children'][index]
        assert audit['choice'] == choice
        assert audit['audit']['rounds'] == len(record['rounds'])
        assert audit['audit']['deductions'] == sum(len(rd['proposals']) for rd in record['rounds'])
        assert audit['audit']['printed_rows_checked'] == len(printed(record))
        if record['status'] == 'OPEN':
            assert record['final']['path'] == initial['path']
            survivors.append((index, flat(record['final'])))
        else:
            assert record['status'] == 'CANDIDATE_CLOSED'
            assert 'final' not in record and 'terminal' in record
        children.append(record)
    assert [i for i, _ in survivors] == [0, 3, 4, 7]
    assert not any('certified_original_root_bound_' in row['name'] for row in printed(root))
    joined = dg['joined_original_state']
    assert joined == report['certified_state']
    assert joined['path'] == ROOT_PATH
    prior, actual, target = flat(root['final']), flat(joined), flat(old['state'])
    assert old['state']['path'] == ROOT_PATH
    assert old['original_id'] == TARGET and old['original_path'] == ROOT_PATH
    strict = 0
    for key, (lo, hi) in actual.items():
        expected_lo = max(prior[key][0], min(state[key][0] for _, state in survivors))
        expected_hi = min(prior[key][1], max(state[key][1] for _, state in survivors))
        assert (lo, hi) == (expected_lo, expected_hi), key
        tlo, thi = target[key]
        assert tlo <= lo <= hi <= thi, key
        strict += (tlo < lo or hi < thi)
    assert strict == 165
    assert report['status'] == 'PASS_FRESH_WHOLE_C887_COMPLETE_DG_UNION_BOUNDS'
    assert report['whole_original_excluded'] is False
    assert report['old_starting_state_implied'] is True and not report['old_state_interval_deficits']
    assert report['missing_archived_bound_state_assumed'] is False
    assert report['no_selected_child_assumed'] is True
    assert report['new_original_cells'] == report['new_masks'] == 0
    assert report['new_row_counts'] == dict(general_cone=11, incircle=5, rotating_tangent=0, rotating_cone=20)
    for path, digest in list(checked.items()):
        pin(path, digest)
    result = dict(
        status='PASS_INDEPENDENT_SOURCE_BYTE_DOMAIN_AND_HULL_REVIEW',
        commit=export['commit'], original_id=TARGET, original_path=ROOT_PATH,
        published_files=len(export['published_files']), archive_members=len(export['archive_members']),
        native_binding_groups={name: len(table) for name, table in groups},
        old_three_round_prefix_retained=True, six_round_deductions=624, six_round_printed_rows=1288,
        all_eight_exact_child_initial_states_checked=True, surviving_indices=[i for i, _ in survivors],
        interval_hull_reconstructed_without_importing_producer_or_checker=True,
        target_intervals=207, strictly_improved_intervals=strict,
        same_original_path_retained=True, child_specific_auxiliary_or_predicate_transported=False,
        weighted_row_arithmetic_repeated=False, source_or_tree_modified=False,
        native_integration_only=True, standalone_portable=False,
        native_arithmetic_evidence=report['status'],
        native_arithmetic_report_sha256=PINS['extracted/reports/fresh_whole_state_replay.json'],
        fresh_row_arithmetic_acceptance_remains_root_gate=True,
        new_original_cells=0, new_masks=0, input_sha256=checked,
        audit_source_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    output = HERE / 'BYTE_DOMAIN_HULL_AUDIT.json'
    assert not output.exists()
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'input_sha256'}, indent=2))


if __name__ == '__main__':
    main()
