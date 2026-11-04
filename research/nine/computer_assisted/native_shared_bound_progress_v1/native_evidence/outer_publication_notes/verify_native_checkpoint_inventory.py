#!/usr/bin/env python3
"""Read-only byte/header audit of a native progress checkpoint, not proof replay."""
from pathlib import Path
import argparse
import hashlib
import json


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def check(folder):
    folder = Path(folder).resolve(strict=True)
    inventory = json.loads((folder / 'INPUT_MANIFEST.json').read_text())
    assert inventory['schema'] == 'native_progress_checkpoint_file_inventory_v1'
    actual = set()
    for p in folder.rglob('*'):
        assert not p.is_symlink()
        if p.is_file():
            actual.add(p.relative_to(folder).as_posix())
    assert actual == set(inventory['files']) | {'INPUT_MANIFEST.json'}
    for name, entry in inventory['files'].items():
        rel = Path(name)
        assert not rel.is_absolute() and '..' not in rel.parts
        p = folder / rel
        assert p.resolve(strict=True).is_relative_to(folder)
        assert p.stat().st_size == entry['bytes'] and sha(p) == entry['sha256']
    header = json.loads((folder / 'CHECKPOINT.json').read_text())
    assert header['native_exact_evidence_only'] is True
    assert header['self_contained_cold_proof'] is False
    assert header['new_original_cells'] == header['new_masks'] == 0
    assert header['full_proof_replayed_during_checkpoint_build'] is False
    assert header['live_numerical_frontiers_included'] is False
    provenance = json.loads((folder / 'SOURCE_PROVENANCE.json').read_text())
    for original, entry in provenance.items():
        assert Path(original).is_absolute()
        assert inventory['files'][entry['member']]['sha256'] == entry['sha256']
        assert inventory['files'][entry['member']]['bytes'] == entry['bytes']
    dependencies = json.loads((folder / 'DEPENDENCIES.json').read_text())
    assert dependencies['unresolved_references_are_explicitly_not_bundled'] is True
    for entry in dependencies['references']:
        assert entry['availability'] in ('included_exact_bytes', 'published_content_by_hash_not_bundled',
                                         'native_reference_not_bundled')
        assert len(entry['sha256']) == 64
        if entry['availability'] == 'included_exact_bytes':
            assert inventory['files'][entry['member']]['sha256'] == entry['sha256']
    for gate in header['actual_native_gates']:
        report = json.loads((folder / gate['report_member']).read_text())
        manifest = json.loads((folder / gate['manifest_member']).read_text())
        assert report['original_id'] == manifest['id'] == gate['original_id']
        assert report['original_path'] == manifest['original_path'] == gate['original_path']
        for key, value in gate['expected_report_fields'].items():
            assert report[key] == value, (gate['name'], key)
        assert len(manifest['nodes']) == 1 and manifest['nodes'][0]['children'] == []
        node = manifest['nodes'][0]
        assert node['parent'] is None and node['restriction'] is None and node['status'] == 'OPEN'
        record_path = folder / gate['record_member']
        assert sha(record_path) == node['sha256']
        record = json.loads(record_path.read_text())
        assert record['status'] == 'OPEN'
        assert len(record['rounds']) == report['rounds']
        assert sum(len(r['proposals']) for r in record['rounds']) == report['deductions']
        native_manifest = gate['native_manifest_path']
        assert report['input_sha256'][native_manifest] == sha(folder / gate['manifest_member'])
        assert report['input_sha256'][gate['native_record_path']] == sha(record_path)
        if 'component' in gate:
            assert report['component'] == manifest['component'] == gate['component']
            assert report['closed_domain'] == manifest['closed_domain'] == gate['closed_domain']
    if header['kind'] == 'direct_shared_bounds_and_C_lazy_readers':
        comparison = json.loads((folder / header['cb_comparison_attachment']).read_text())
        eager = json.loads((folder / header['cb_eager_report']).read_text())
        lazy = json.loads((folder / header['actual_native_gates'][0]['report_member']).read_text())
        assert sha(folder / header['cb_eager_report']) == comparison['old_report_sha256']
        assert sha(folder / header['actual_native_gates'][0]['report_member']) == comparison['new_report_sha256']
        for field in comparison['exactly_equal_result_fields']:
            assert eager[field] == lazy[field]
    else:
        assert header['kind'] == 'A_c744_component3_post_A1_conditional_bound_rows'
        assert header['valid_on_whole_original'] is False and header['component'] == 3
    return dict(status='PASS_NATIVE_CHECKPOINT_BYTES_AND_HEADER_CONSISTENCY_ONLY',
        kind=header['kind'], files=len(inventory['files']),
        bytes=sum(x['bytes'] for x in inventory['files'].values()),
        input_manifest_sha256=sha(folder / 'INPUT_MANIFEST.json'),
        included_records_and_reports_hash_verified=True,
        declared_native_gate_headers_consistent=True,
        published_archives_downloaded_or_rehashed_by_this_audit=False,
        omitted_native_prerequisites_rehashed_by_this_audit=False,
        weighted_arithmetic_repeated=False, self_contained_cold_proof=False,
        live_frontiers_changed=False, new_original_cells=0, new_masks=0)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Optimized Python is not supported for inventory checks.')
    parser = argparse.ArgumentParser()
    parser.add_argument('folder', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = check(args.folder)
    if args.output:
        assert not args.output.exists()
        assert not args.output.resolve().is_relative_to(args.folder.resolve())
        with args.output.open('x') as stream:
            json.dump(report, stream, indent=2)
            stream.write('\n')
    print(json.dumps(report, indent=2))
