#!/usr/bin/env python3
"""Verify/restore discovery bytes. This performs NO mathematical proof replay."""
from pathlib import Path, PurePosixPath
import argparse, base64, hashlib, json, tarfile, tempfile, time


def run():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--destination', type=Path,
                    help='New directory for extraction; omit for verification only.')
    args = ap.parse_args()
    here = Path(__file__).resolve().parent
    metadata = json.loads((here/'PARTS.json').read_text())
    inventory_bytes = (here/metadata['internal_inventory']).read_bytes()
    inventory = json.loads(inventory_bytes)['files']
    expected = dict(inventory)
    if metadata.get('inventory_is_member', True):
        expected[metadata['internal_inventory']] = hashlib.sha256(inventory_bytes).hexdigest()
    assert metadata['mathematical_replay'] is False
    assert metadata['new_original_cells'] == metadata['new_masks'] == 0
    destination = args.destination.resolve() if args.destination else None
    if destination is not None:
        destination.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix='native-discovery-') as tmp:
        archive = Path(tmp)/'payload.tar.xz'
        digest = hashlib.sha256()
        size = 0
        with archive.open('wb') as output:
            for part in metadata['parts']:
                relative = PurePosixPath(part['path'])
                assert not relative.is_absolute() and '..' not in relative.parts
                encoded = (here/part['path']).read_bytes()
                assert len(encoded) == part['bytes']
                assert hashlib.sha256(encoded).hexdigest() == part['sha256']
                raw = base64.b64decode(encoded.strip(), validate=True)
                assert len(raw) == part['decoded_bytes']
                assert hashlib.sha256(raw).hexdigest() == part['decoded_sha256']
                digest.update(raw); size += len(raw); output.write(raw)
        assert size == metadata['archive_bytes']
        assert digest.hexdigest() == metadata['archive_sha256']
        seen = {}
        with tarfile.open(archive, mode='r|xz') as stream:
            for member in stream:
                relative = PurePosixPath(member.name)
                assert not relative.is_absolute() and '..' not in relative.parts
                assert relative.parts[0] == metadata['archive_root']
                if member.isdir():
                    continue
                assert member.isfile() and not member.issym() and not member.islnk()
                name = str(PurePosixPath(*relative.parts[1:]))
                assert name in expected and name not in seen, name
                source = stream.extractfile(member)
                assert source is not None
                out = None
                if destination is not None:
                    path = destination.joinpath(*relative.parts)
                    path.parent.mkdir(parents=True, exist_ok=True)
                    out = path.open('xb')
                checksum = hashlib.sha256()
                try:
                    while chunk := source.read(1 << 20):
                        checksum.update(chunk)
                        if out is not None:
                            out.write(chunk)
                finally:
                    if out is not None:
                        out.close()
                seen[name] = checksum.hexdigest()
                assert seen[name] == expected[name], name
        assert seen == expected
    report = dict(status='PASS_HASH_VERIFIED_NATIVE_DISCOVERY_ARCHIVE',
                  archive_sha256=metadata['archive_sha256'], archive_bytes=size,
                  parts_checked=len(metadata['parts']), regular_members_checked=len(seen),
                  mathematical_replay=False, standalone_portable_proof=False,
                  new_original_cells=0, new_masks=0,
                  seconds=time.monotonic()-started)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    run()
