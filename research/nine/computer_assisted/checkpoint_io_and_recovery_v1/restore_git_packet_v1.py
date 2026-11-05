#!/usr/bin/env python3
"""Restore an exact Git tree prefix to a new scratch directory, without checkout.

This establishes byte availability only. It neither replays a proof nor turns
an old checkpoint into a newer lost frontier. The receipt pins every Git blob
and SHA256 and rejects symlinks, duplicate paths, and any existing output.
"""
if not __debug__:
    raise RuntimeError('Assertions must be enabled')

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess


def restore(repository, commit, prefixes, destination):
    repository = Path(repository).resolve()
    destination = Path(destination).absolute()
    assert not os.path.lexists(destination)
    assert re.fullmatch(r'[0-9a-f]{40}', commit)
    actual_commit = subprocess.check_output(
        ['git', 'rev-parse', commit + '^{commit}'], cwd=repository,
        text=True).strip()
    assert actual_commit == commit
    for prefix in prefixes:
        p = PurePosixPath(prefix)
        assert not p.is_absolute() and '..' not in p.parts and p.parts
    listing = subprocess.check_output(
        ['git', 'ls-tree', '-r', '-z', '--long', commit, '--', *prefixes],
        cwd=repository)
    entries = []
    names = set()
    for record in listing.split(b'\0'):
        if not record:
            continue
        metadata, raw_name = record.split(b'\t', 1)
        mode, kind, oid, size = metadata.decode().split()
        name = raw_name.decode('utf-8')
        path = PurePosixPath(name)
        assert mode in ('100644', '100755') and kind == 'blob'
        assert not path.is_absolute() and '..' not in path.parts
        assert name not in names and any(
            name == p or name.startswith(p.rstrip('/') + '/') for p in prefixes)
        names.add(name)
        entries.append((name, mode, oid, int(size)))
    assert entries, 'No committed files found for requested prefixes'
    destination.mkdir(parents=True, exist_ok=False)
    restored = {}
    for name, mode, oid, size in entries:
        data = subprocess.check_output(['git', 'cat-file', 'blob', oid], cwd=repository)
        assert len(data) == size
        assert hashlib.sha1(b'blob ' + str(size).encode() + b'\0' + data).hexdigest() == oid
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as stream:
            stream.write(data)
        os.chmod(target, int(mode[-3:], 8))
        digest = hashlib.sha256(data).hexdigest()
        assert hashlib.sha256(target.read_bytes()).hexdigest() == digest
        restored[name] = {'git_blob': oid, 'mode': mode, 'bytes': size, 'sha256': digest}
    result = {
        'status': 'PASS_EXACT_COMMITTED_BYTES_RESTORED',
        'commit': commit, 'prefixes': prefixes,
        'files': restored, 'file_count': len(restored),
        'bytes': sum(x['bytes'] for x in restored.values()),
        'arithmetic_replayed': False, 'new_proof_credit': 0,
        'lost_uncommitted_suffix_reconstructed': False,
        'restorer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    receipt = destination / 'GIT_RESTORATION_RECEIPT.json'
    with receipt.open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps({k: result[k] for k in ('status', 'commit', 'file_count', 'bytes')}))
    print('receipt_sha256=' + hashlib.sha256(receipt.read_bytes()).hexdigest())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--repository', type=Path, required=True)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--destination', type=Path, required=True)
    parser.add_argument('prefixes', nargs='+')
    args = parser.parse_args()
    restore(args.repository, args.commit, args.prefixes, args.destination)
