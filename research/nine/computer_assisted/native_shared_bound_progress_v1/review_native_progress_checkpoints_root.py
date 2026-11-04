#!/usr/bin/env python3
"""Independent publication identity/domain audit, without repeating proof arithmetic."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import subprocess

ROOT = Path('/workspace/scratch/f9f48fcfb253')
PACKET = ROOT / 'ac_work/native_progress_checkpoints_v1'
RELEASE_SHA = 'd5313c814e773a2109e1208c6daf032baf90af7d6161518a17cf5bec1baa7753'
READY_SHA = '33aac7c72892f2589e1ace329563223cf691c48c6154c4c204230fda8dc2c410'
OUTPUT = ROOT / 'd_work/NATIVE_PROGRESS_CHECKPOINTS_ROOT_PUBLICATION_REVIEW.json'


def digest(path):
    h = sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_bytes())


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    assert digest(PACKET / 'RELEASE_INVENTORY.json') == RELEASE_SHA
    assert digest(PACKET / 'READY.json') == READY_SHA
    release = read(PACKET / 'RELEASE_INVENTORY.json')
    files = release['files']
    assert not any(p.is_symlink() for p in PACKET.rglob('*'))
    assert {p.relative_to(PACKET).as_posix() for p in PACKET.rglob('*') if p.is_file()} == set(files) | {'RELEASE_INVENTORY.json'}
    for name, expected in files.items():
        p = PACKET / name
        assert p.stat().st_size == expected['bytes'] and digest(p) == expected['sha256'], name
    ready = read(PACKET / 'READY.json')
    assert ready['new_original_cells'] == ready['new_masks'] == 0
    assert ready['self_contained_cold_proof'] is False and ready['full_arithmetic_rerun'] is False
    gates, source_count, publications = [], 0, {}
    for package in ready['packages']:
        folder = PACKET / package['folder']
        inventory = read(folder / 'INPUT_MANIFEST.json')['files']
        assert digest(folder / 'INPUT_MANIFEST.json') == package['input_manifest_sha256']
        assert len(inventory) == package['inventoried_files']
        assert sum(v['bytes'] for v in inventory.values()) == package['bytes']
        assert {p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file()} == set(inventory) | {'INPUT_MANIFEST.json'}
        for name, expected in inventory.items():
            assert files[package['folder'] + '/' + name] == expected
        provenance = read(folder / 'SOURCE_PROVENANCE.json')
        for native, item in provenance.items():
            assert Path(native).is_absolute()
            assert digest(native) == digest(folder / item['member']) == item['sha256'], native
            assert Path(native).stat().st_size == item['bytes']
        source_count += len(provenance)
        header = read(folder / 'CHECKPOINT.json')
        assert header['native_exact_evidence_only'] is True and header['self_contained_cold_proof'] is False
        assert header['new_original_cells'] == header['new_masks'] == 0
        assert header['live_numerical_frontiers_included'] is False
        dependencies = read(folder / 'DEPENDENCIES.json')
        assert dict(Counter(r['availability'] for r in dependencies['references'])) == dependencies['availability_counts'] == package['dependency_counts']
        for item in dependencies['published_packages']:
            raw = subprocess.check_output(['git', 'show', item['commit'] + ':' + item['repository_path']], cwd=ROOT / 'repo')
            assert sha256(raw).hexdigest() == item['manifest_sha256'] == digest(folder / item['manifest_member'])
            metadata = json.loads(raw)
            assert metadata.get('archive_sha256', metadata.get('sha256')) == item['archive_sha256']
            publications[item['name']] = item['archive_sha256']
        for gate in header['actual_native_gates']:
            report = read(folder / gate['report_member'])
            manifest = read(folder / gate['manifest_member'])
            record = read(folder / gate['record_member'])
            assert report['original_id'] == manifest['id'] == gate['original_id']
            assert report['original_path'] == manifest['original_path'] == gate['original_path']
            assert len(manifest['nodes']) == 1
            node = manifest['nodes'][0]
            assert node['children'] == [] and node['parent'] is None and node['restriction'] is None
            assert node['status'] == record['status'] == 'OPEN'
            assert node['sha256'] == digest(folder / gate['record_member'])
            assert report['input_sha256'][gate['native_manifest_path']] == digest(folder / gate['manifest_member'])
            assert report['input_sha256'][gate['native_record_path']] == digest(folder / gate['record_member'])
            for key, expected in gate['expected_report_fields'].items():
                assert report[key] == expected, (gate['name'], key)
            assert len(record['rounds']) == report['rounds']
            assert sum(len(r['proposals']) for r in record['rounds']) == report['deductions']
            if 'component' in gate:
                assert report['component'] == manifest['component'] == gate['component']
                assert report['closed_domain'] == manifest['closed_domain'] == gate['closed_domain']
            gates.append(dict(name=gate['name'], original_id=gate['original_id'],
                component=gate.get('component'), rounds=report['rounds'], deductions=report['deductions'],
                report_sha256=digest(folder / gate['report_member']), record_sha256=node['sha256'], open=True))
        if header['kind'] == 'A_c744_component3_post_A1_conditional_bound_rows':
            assert header['component'] == 3 and header['valid_on_whole_original'] is False
            assert header['rows_in_conditional_family'] == 414
    transitive = read(PACKET / 'outer_publication_notes/TRANSITIVE_CB882_PUBLICATION_REFERENCE.json')
    raw = subprocess.check_output(['git', 'show', transitive['commit'] + ':' + transitive['repository_path']], cwd=ROOT / 'repo')
    assert sha256(raw).hexdigest() == transitive['manifest_sha256']
    assert json.loads(raw)['archive_sha256'] == transitive['archive_sha256'] == ready['transitive_cb882_archive_sha256']
    assert (len(gates), sum(g['deductions'] for g in gates)) == (3, 1094)
    report = dict(status='PASS_NATIVE_PROGRESS_PUBLICATION_IDENTITY_AND_SCOPE_REVIEW',
        release_inventory_sha256=RELEASE_SHA, ready_sha256=READY_SHA,
        inventoried_files=len(files), inventoried_bytes=sum(x['bytes'] for x in files.values()),
        native_source_occurrences_rehashed=source_count, saved_native_gate_headers=gates,
        published_archive_identities=publications, transitive_cb882_archive_sha256=transitive['archive_sha256'],
        all_three_saved_domains_remain_open=True,
        A3_family_conditional_on_component3=True,
        native_evidence_only=True, self_contained_cold_proof=False,
        weighted_arithmetic_repeated=False, unbundled_transitive_ancestry_not_replayed=True,
        numerical_solver_called=False, live_frontiers_modified=False,
        new_original_cells=0, new_masks=0,
        current_fixed_register_sha256=digest(ROOT / 'repo/research/nine/gates/A2_00100_FIXED_FRONTIER.json'),
        review_source_sha256=digest(__file__))
    with OUTPUT.open('x') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    print(json.dumps(dict(status=report['status'], report=str(OUTPUT), sha256=digest(OUTPUT),
                          files=len(files), native_source_occurrences=source_count)))


if __name__ == '__main__':
    main()
