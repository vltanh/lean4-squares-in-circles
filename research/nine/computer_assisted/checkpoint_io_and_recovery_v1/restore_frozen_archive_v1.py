#!/usr/bin/env python3
"""Join pinned committed archive parts and extract only ordinary files safely.

The fresh receipt proves availability of these archive bytes and members. It
does not repeat mathematical replay or recover any uncommitted search suffix.
"""
if not __debug__:
    raise RuntimeError('Assertions must be enabled')
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import tarfile


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def restore(manifest_path, expected_manifest, output):
    manifest_path = Path(manifest_path).resolve()
    assert sha(manifest_path) == expected_manifest
    manifest = json.loads(manifest_path.read_text())
    output = Path(output).absolute()
    assert not os.path.lexists(output)
    output.mkdir(parents=True, exist_ok=False)
    archive_name = manifest['archive']
    assert PurePosixPath(archive_name).name == archive_name
    archive = output / archive_name
    total, seen_parts = 0, set()
    with archive.open('xb') as stream:
        for item in manifest['parts']:
            name = item['file']
            assert PurePosixPath(name).name == name and name not in seen_parts
            seen_parts.add(name)
            part = manifest_path.parent / name
            assert part.is_file() and not part.is_symlink()
            assert part.stat().st_size == item['bytes'] and sha(part) == item['sha256']
            with part.open('rb') as source:
                for block in iter(lambda: source.read(1 << 20), b''):
                    stream.write(block)
                    total += len(block)
    assert total == manifest['archive_bytes'] == archive.stat().st_size
    assert sha(archive) == manifest['archive_sha256']
    extracted = output / 'extracted'
    extracted.mkdir()
    members, seen = {}, set()
    with tarfile.open(archive, 'r|xz') as tar:
        for member in tar:
            path = PurePosixPath(member.name)
            assert not path.is_absolute() and '..' not in path.parts and path.parts
            assert member.name not in seen
            seen.add(member.name)
            target = extracted.joinpath(*path.parts)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            assert member.isfile(), ('Only regular files or directories allowed', member.name)
            target.parent.mkdir(parents=True, exist_ok=True)
            h, size = hashlib.sha256(), 0
            with tar.extractfile(member) as source, target.open('xb') as destination:
                for block in iter(lambda: source.read(1 << 20), b''):
                    destination.write(block)
                    h.update(block)
                    size += len(block)
            assert size == member.size
            os.chmod(target, member.mode & 0o777)
            assert sha(target) == h.hexdigest()
            members[member.name] = {'bytes': size, 'sha256': h.hexdigest()}
    result = {'status': 'PASS_PINNED_ARCHIVE_PARTS_AND_REGULAR_MEMBERS_RESTORED',
        'manifest_sha256': expected_manifest, 'archive_sha256': sha(archive),
        'archive_bytes': total, 'members': members, 'regular_members': len(members),
        'uncompressed_bytes': sum(x['bytes'] for x in members.values()),
        'arithmetic_replayed': False, 'new_proof_credit': 0,
        'lost_uncommitted_suffix_reconstructed': False,
        'restorer_sha256': sha(__file__)}
    receipt = output / 'ARCHIVE_RESTORATION_RECEIPT.json'
    with receipt.open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps({k:result[k] for k in ('status', 'regular_members', 'archive_bytes', 'uncompressed_bytes')}))
    print('receipt_sha256=' + sha(receipt))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--manifest-sha', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    restore(args.manifest, args.manifest_sha, args.output)
