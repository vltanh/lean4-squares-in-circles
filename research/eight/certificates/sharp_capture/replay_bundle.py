#!/usr/bin/env python3
"""Extract authenticated proof evidence and replay the thirteen interfaces.

This does not rerun the 123 original subdivision trees. Their immutable
sources, data, manifests, and complete execution logs are in the bundle.
Use a fresh destination; no existing directory is modified.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import subprocess
import sys
import tarfile


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination', type=Path)
    parser.add_argument('--extract-only', action='store_true')
    args = parser.parse_args()
    bundle = Path(__file__).resolve().parent
    manifest = json.loads((bundle / 'BUNDLE_MANIFEST.json').read_text())
    destination = args.destination.resolve()
    if destination.exists():
        raise SystemExit('Destination must not exist: ' + str(destination))
    for record in manifest['archives']:
        path = bundle / record['file']
        assert path.stat().st_size == record['bytes'], path
        assert digest(path) == record['sha256'], path
    destination.mkdir(parents=True)
    extracted = set()
    for record in manifest['archives']:
        with tarfile.open(bundle / record['file'], 'r:xz') as archive:
            for member in archive.getmembers():
                name = PurePosixPath(member.name)
                assert not name.is_absolute() and '..' not in name.parts, name
                assert member.isfile(), ('Nonregular archive member', name)
                assert str(name) not in extracted, ('Duplicate member', name)
                extracted.add(str(name))
                target = destination.joinpath(*name.parts)
                target.parent.mkdir(parents=True, exist_ok=True)
                stream = archive.extractfile(member)
                assert stream is not None
                with stream, target.open('xb') as output:
                    for block in iter(lambda: stream.read(1024 * 1024), b''):
                        output.write(block)
    numeric = json.loads((destination / manifest['numeric_manifest']).read_text())
    interface = json.loads((destination / manifest['interface_manifest']).read_text())
    assert numeric['file_count'] == len(numeric['files'])
    assert len(interface['commands']) == manifest['root_interface_replays'] == 13
    expected = {manifest['numeric_manifest'], manifest['interface_manifest']}
    for record in numeric['files'] + interface['supplemental_members']:
        assert record['path'] not in expected, ('Duplicate manifest member', record['path'])
        expected.add(record['path'])
        path = destination / record['path']
        size = record.get('bytes', record.get('size'))
        assert size is not None and path.stat().st_size == size, path
        assert digest(path) == record['sha256'], path
    assert expected == extracted, (expected - extracted, extracted - expected)
    print('PASS: both archive hashes and all', len(extracted), 'member bindings', flush=True)
    replay = {'status': 'EXTRACTED AND AUTHENTICATED', 'member_count': len(extracted), 'commands': []}
    if not args.extract_only:
        for item in interface['commands']:
            command = [sys.executable, *item['command']]
            result = subprocess.run(command, cwd=destination, text=True, capture_output=True)
            replay['commands'].append({
                'command': item['command'], 'exit_code': result.returncode,
                'stdout': result.stdout, 'stderr': result.stderr,
            })
            if result.returncode:
                replay['status'] = 'FAILED'
                (destination / 'PORTABLE_REPLAY.json').write_text(json.dumps(replay, indent=2) + '\n')
                raise SystemExit(result.stdout + result.stderr)
            print('PASS:', ' '.join(item['command']), flush=True)
        replay['status'] = 'ALL THIRTEEN PORTABLE INTERFACE REPLAYS PASSED'
    (destination / 'PORTABLE_REPLAY.json').write_text(json.dumps(replay, indent=2) + '\n')
    print(replay['status'], flush=True)


if __name__ == '__main__':
    main()
