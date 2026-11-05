#!/usr/bin/env python3
"""Archive an independently replayed OPEN B checkpoint, with zero ledger credit.

This is deliberately separate from the complete-original release gate.
Every archived regular member is hashed and read back after compression.
"""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, tarfile, time

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('packet', type=Path)
    ap.add_argument('replay', type=Path)
    ap.add_argument('output', type=Path)
    a = ap.parse_args()
    packet, replay, output = a.packet.resolve(), a.replay.resolve(), a.output.resolve()
    started = time.monotonic()
    info = json.loads((packet / 'ORIGINAL_PROOF.json').read_text())
    receipt = json.loads((replay / 'PORTABLE_RECEIPT.json').read_text())
    assert info['complete'] is False and info['open_prototype'] is True
    assert info['counts']['open_leaves'] > 0
    assert receipt['status'] == 'PASS_PORTABLE_B7_CENTRAL_POSITION_OPEN_COVER'
    assert info['original_id'] == 'negative-7c60be8b07a358e9'
    assert receipt['complete'] is False and receipt['whole_original_proved'] is False
    assert receipt['original_id'] == info['original_id']
    assert receipt['packet_manifest_sha256'] == sha(packet / 'INPUT_MANIFEST.json')
    assert receipt['report_sha256'] == sha(replay / 'COMPLETE_ORIGINAL_REPLAY.json')
    for key in ('new_original_ledger_credit', 'new_mask_ledger_credit'):
        assert receipt[key] == info[key] == 0
    for name in ('PORTABLE_RECEIPT.json', 'COMPLETE_ORIGINAL_REPLAY.json'):
        target = packet / 'original_audits' / ('FRESH_' + name)
        assert not target.exists()
        target.write_bytes((replay / name).read_bytes())
    sources = {str(p.relative_to(packet)): sha(p) for p in sorted(packet.rglob('*')) if p.is_file()}
    assert 'PARTIAL_RELEASE_MANIFEST.json' not in sources
    release = dict(schema='open_registered_B_checkpoint_release_v1', original_id=info['original_id'],
                   files=sources, counts=info['counts'], complete_original=False,
                   new_original_ledger_credit=0, new_mask_ledger_credit=0,
                   prior_archive_sha256=info['prior_archive_sha256'])
    (packet / 'PARTIAL_RELEASE_MANIFEST.json').write_text(json.dumps(release, indent=2) + '\n')
    expected = dict(sources)
    expected['PARTIAL_RELEASE_MANIFEST.json'] = sha(packet / 'PARTIAL_RELEASE_MANIFEST.json')
    output.mkdir(parents=True, exist_ok=False)
    archive = output / (packet.name + '.tar.xz')
    temporary = output / (archive.name + '.tmp')
    with temporary.open('xb') as stream:
        producer = subprocess.Popen(['tar', '--sort=name', '--mtime=@0', '--owner=0', '--group=0',
                                     '--numeric-owner', '--format=gnu', '--hard-dereference',
                                     '-cf', '-', '-C', str(packet.parent), packet.name], stdout=subprocess.PIPE)
        compressor = None
        try:
            compressor = subprocess.Popen(['xz', '-T1', '-6', '-c'], stdin=producer.stdout, stdout=stream)
            producer.stdout.close()
            assert compressor.wait() == 0 and producer.wait() == 0
        finally:
            for child in (compressor, producer):
                if child is not None and child.poll() is None:
                    child.terminate()
                    child.wait()
        stream.flush()
        os.fsync(stream.fileno())
    subprocess.run(['xz', '-t', str(temporary)], check=True)
    found = set()
    with tarfile.open(temporary, 'r|xz') as stream:
        for member in stream:
            if member.isdir():
                continue
            assert member.isfile()
            rel = Path(member.name).relative_to(packet.name)
            name = str(rel)
            assert '..' not in rel.parts and name in expected and name not in found
            h = hashlib.sha256()
            source = stream.extractfile(member)
            for block in iter(lambda: source.read(1 << 20), b''):
                h.update(block)
            assert h.hexdigest() == expected[name]
            found.add(name)
    assert found == set(expected)
    os.replace(temporary, archive)
    report = dict(schema='open_registered_B_checkpoint_archive_v1', original_id=info['original_id'],
                  archive=archive.name, archive_bytes=archive.stat().st_size, archive_sha256=sha(archive),
                  archive_members_verified=len(found), all_member_hashes_match=True, xz_integrity_pass=True,
                  counts=info['counts'], complete_original=False, new_original_ledger_credit=0,
                  new_mask_ledger_credit=0, portable_receipt_sha256=sha(replay / 'PORTABLE_RECEIPT.json'),
                  release_manifest_sha256=expected['PARTIAL_RELEASE_MANIFEST.json'],
                  prior_archive_sha256=info['prior_archive_sha256'], seconds=time.monotonic()-started)
    (output / 'ARCHIVE_READY.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2), flush=True)

if __name__ == '__main__':
    main()
