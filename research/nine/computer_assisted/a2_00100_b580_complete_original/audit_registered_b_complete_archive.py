"""Independent complete registered B-original part, member, receipt and input audit.

This audits transport and literal report identities, not weighted arithmetic.
It never mutates a proof packet, register or archive.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import tarfile
import time


def digest(path):
    h = sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('packet', type=Path)
    ap.add_argument('archive_directory', type=Path)
    ap.add_argument('output', type=Path)
    ap.add_argument('--original-id', required=True)
    a = ap.parse_args()
    started = time.monotonic()
    packet = a.packet.resolve()
    directory = a.archive_directory.resolve()
    ready_path = directory / 'ARCHIVE_READY.json'
    ready = json.loads(ready_path.read_text())
    assert ready['original_id'] == a.original_id
    assert ready['xz_integrity_pass'] and ready['all_member_hashes_match']
    assert ready['fresh_portable_replay_pass']
    archive = directory / ready['archive']
    assert digest(archive) == ready['archive_sha256']
    concatenated = sha256()
    total_bytes = 0
    for entry in ready['parts']:
        path = directory / entry['file']
        assert path.stat().st_size == entry['bytes']
        assert digest(path) == entry['sha256']
        with path.open('rb') as stream:
            for block in iter(lambda: stream.read(4 * 1024 * 1024), b''):
                concatenated.update(block)
                total_bytes += len(block)
    assert total_bytes == ready['archive_bytes'] == archive.stat().st_size
    assert concatenated.hexdigest() == ready['archive_sha256']
    release_path = packet / 'RELEASE_MANIFEST.json'
    assert digest(release_path) == ready['release_manifest_sha256']
    release = json.loads(release_path.read_text())
    expected = dict(release['files'])
    assert 'RELEASE_MANIFEST.json' not in expected
    expected['RELEASE_MANIFEST.json'] = ready['release_manifest_sha256']
    assert len(expected) == ready['all_archive_members_verified']
    seen = set()
    with tarfile.open(archive, 'r|xz') as tar:
        for member in tar:
            if member.isdir():
                continue
            assert member.isfile() and member.name.startswith(packet.name + '/')
            name = member.name[len(packet.name) + 1:]
            assert name in expected and name not in seen
            assert '..' not in Path(name).parts
            stream = tar.extractfile(member)
            assert stream is not None
            h = sha256()
            for block in iter(lambda: stream.read(4 * 1024 * 1024), b''):
                h.update(block)
            assert h.hexdigest() == expected[name]
            seen.add(name)
    assert seen == set(expected)
    for name, expected_hash in expected.items():
        assert digest(packet / name) == expected_hash

    info = json.loads((packet / 'ORIGINAL_PROOF.json').read_text())
    receipt_path = packet / 'original_audits/FRESH_PORTABLE_RECEIPT.json'
    receipt = json.loads(receipt_path.read_text())
    report_path = packet / 'original_audits/FRESH_COMPLETE_ORIGINAL_REPLAY.json'
    assert digest(report_path) == receipt['report_sha256']
    report = json.loads(report_path.read_text())
    native = json.loads((packet / 'original_audits/EXACT_TREE_REPLAY.json').read_text())
    assert info['original_id'] == receipt['original_id'] == report['initial_original_id'] == ready['original_id']
    assert receipt['status'] == 'PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL'
    assert receipt['complete'] and receipt['whole_original_proved']
    assert receipt['every_new_bound_and_cover_replayed']
    assert receipt['all_inputs_rehashed_at_completion']
    assert receipt['external_workspace_reads_forbidden']
    assert receipt['numerical_modules_imported'] is False
    for key in ('status', 'initial_original_id', 'initial_path', 'certificate_sha256',
                'parent_certificate_sha256', 'complete', 'whole_original_proved',
                'entire_registered_original_domain_retained',
                'nodes', 'terminal_leaves', 'excluded_leaves', 'open_leaves',
                'complete_unions', 'local_rounds', 'local_deductions',
                'local_printed_rows', 'leaf_table'):
        assert report[key] == native[key], key
    assert report['status'] == 'PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE'
    assert report['complete'] and report['whole_original_proved']
    assert report['entire_registered_original_domain_retained'] is True
    assert report['nodes'] > 0 and report['excluded_leaves'] == report['terminal_leaves'] > 0
    assert report['open_leaves'] == 0
    for key, value in info['counts'].items():
        assert report[key] == native[key] == value, key
    arity = {'proxy': 4, 'angle': 2, 'sat': 8, 'difference': 2}
    assert set(report['complete_unions']) <= set(arity)
    assert report['nodes'] == 1 + sum(arity[k] * v for k, v in report['complete_unions'].items())
    assert report['terminal_leaves'] == report['nodes'] - sum(report['complete_unions'].values())
    assert receipt['packet_manifest_sha256'] == digest(packet / 'INPUT_MANIFEST.json')
    inputs = json.loads((packet / 'INPUT_MANIFEST.json').read_text())['files']
    assert len(inputs) == receipt['packet_inputs'] and receipt['prior_inputs'] == 507
    for name, expected_hash in inputs.items():
        assert digest(packet / name) == expected_hash
    result = dict(status='PASS_REGISTERED_B_COMPLETE_ARCHIVE_AND_PART_AUDIT',
                  original_id=ready['original_id'], original_path=info['original_path'],
                  archive_sha256=ready['archive_sha256'], archive_bytes=total_bytes,
                  complete_part_count=len(ready['parts']), every_part_hash_checked=True,
                  concatenated_part_digest_matches_archive=True,
                  all_regular_members_verified=len(seen), all_source_packet_bytes_rehashed=True,
                  native_and_portable_mathematical_reports_match=True,
                  release_manifest_sha256=ready['release_manifest_sha256'],
                  fresh_complete_report_sha256=receipt['report_sha256'],
                  fresh_portable_receipt_sha256=digest(receipt_path),
                  input_manifest_sha256=receipt['packet_manifest_sha256'],
                  archive_ready_sha256=digest(ready_path),
                  weighted_arithmetic_repeated=False, numerical_optimizer_called=False,
                  no_original_ledger_mutation_by_auditor=True,
                  new_original_cells=0, new_masks=0, seconds=time.monotonic() - started)
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
