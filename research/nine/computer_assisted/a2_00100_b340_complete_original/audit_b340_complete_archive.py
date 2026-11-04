"""Independent byte/member audit of the complete B340 publication archive."""
from pathlib import Path
import hashlib
import json
import tarfile
import time

WORK = Path(__file__).resolve().parent.parent
PACKET = WORK / 'b_work/portable_b340_complete_v1/b340_complete_original_package'
ARCHIVES = WORK / 'b_work/b340_complete_original_archive_v1'


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for data in iter(lambda: stream.read(4 * 1024 * 1024), b''):
            digest.update(data)
    return digest.hexdigest()


def main():
    started = time.monotonic()
    ready_path = ARCHIVES / 'ARCHIVE_READY.json'
    ready = json.loads(ready_path.read_text())
    assert ready['original_id'] == 'negative-34029ea8b047982f'
    assert ready['archive_sha256'] == 'b4b3db56da2b3ac7a006d8c8e1060d07e4ab0103070fdce88c7611c74744569f'
    assert ready['archive_bytes'] == 53274488 and len(ready['parts']) == 7
    assert ready['all_archive_members_verified'] == 730
    assert ready['xz_integrity_pass'] is True and ready['all_member_hashes_match'] is True
    assert ready['raw_tar_intermediate_created'] is False
    archive = ARCHIVES / ready['archive']
    assert sha(archive) == ready['archive_sha256']
    concatenated = hashlib.sha256()
    total_bytes = 0
    for part in ready['parts']:
        path = ARCHIVES / part['file']
        assert path.stat().st_size == part['bytes'] and sha(path) == part['sha256']
        with path.open('rb') as stream:
            for data in iter(lambda: stream.read(4 * 1024 * 1024), b''):
                concatenated.update(data)
                total_bytes += len(data)
    assert total_bytes == ready['archive_bytes'] and concatenated.hexdigest() == ready['archive_sha256']
    release_path = PACKET / 'RELEASE_MANIFEST.json'
    assert sha(release_path) == ready['release_manifest_sha256']
    release = json.loads(release_path.read_text())
    expected = dict(release['files'])
    assert 'RELEASE_MANIFEST.json' not in expected
    expected['RELEASE_MANIFEST.json'] = ready['release_manifest_sha256']
    assert len(expected) == 730
    seen = set()
    with tarfile.open(archive, 'r|xz') as tar:
        for member in tar:
            if member.isdir():
                continue
            assert member.isfile() and member.name.startswith(PACKET.name + '/')
            name = member.name[len(PACKET.name) + 1:]
            assert name in expected and name not in seen and '..' not in Path(name).parts
            stream = tar.extractfile(member)
            assert stream is not None
            digest = hashlib.sha256()
            for data in iter(lambda: stream.read(4 * 1024 * 1024), b''):
                digest.update(data)
            assert digest.hexdigest() == expected[name]
            seen.add(name)
    assert seen == set(expected)
    for name, digest in expected.items():
        assert sha(PACKET / name) == digest
    info = json.loads((PACKET / 'ORIGINAL_PROOF.json').read_text())
    receipt = json.loads((PACKET / 'original_audits/FRESH_PORTABLE_RECEIPT.json').read_text())
    report_path = PACKET / 'original_audits/FRESH_COMPLETE_ORIGINAL_REPLAY.json'
    assert sha(report_path) == receipt['report_sha256']
    report = json.loads(report_path.read_text())
    assert info['original_id'] == receipt['original_id'] == report['initial_original_id'] == ready['original_id']
    assert receipt['status'] == 'PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL'
    assert receipt['complete'] is True and receipt['whole_original_proved'] is True
    assert report['status'] == 'PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE'
    assert report['complete'] is True and report['whole_original_proved'] is True
    assert report['open_leaves'] == 0 and report['excluded_leaves'] == 279
    assert receipt['packet_manifest_sha256'] == sha(PACKET / 'INPUT_MANIFEST.json')
    assert receipt['packet_inputs'] == 726 and receipt['prior_inputs'] == 507
    result = dict(status='PASS_ROOT_B340_COMPLETE_ARCHIVE_AND_PART_AUDIT',
        original_id=ready['original_id'], original_path=info['original_path'],
        archive_sha256=ready['archive_sha256'], archive_bytes=total_bytes,
        complete_part_count=7, every_part_hash_checked=True,
        concatenated_part_digest_matches_archive=True,
        all_regular_members_verified=len(seen), all_source_packet_bytes_rehashed=True,
        release_manifest_sha256=ready['release_manifest_sha256'],
        fresh_complete_report_sha256=receipt['report_sha256'],
        fresh_portable_receipt_sha256=sha(PACKET / 'original_audits/FRESH_PORTABLE_RECEIPT.json'),
        input_manifest_sha256=receipt['packet_manifest_sha256'],
        archive_ready_sha256=sha(ready_path), raw_tar_intermediate_created=False,
        weighted_arithmetic_repeated=False, numerical_optimizer_called=False,
        no_original_ledger_mutation_by_auditor=True, new_masks=0,
        seconds=time.monotonic() - started)
    output = WORK / 'd_work/B340_COMPLETE_ROOT_ARCHIVE_AUDIT.json'
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
