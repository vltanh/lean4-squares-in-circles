#!/usr/bin/env python3
"""Deterministic regular-file transport of an exactly inventoried checkpoint.

This is byte transport only. Extraction does not install native aliases or
execute any proof, solver, or preserved script.
"""
if not __debug__:
    raise RuntimeError('Transport verification requires assertions.')
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import io
import json
import lzma
import os
import tarfile

SCHEMA = 'native_proof_checkpoint_regular_file_archive_v2'

def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()

def sha(path):
    return sha_bytes(Path(path).read_bytes())

def canonical_name(name):
    assert isinstance(name, str) and name and '\\' not in name and '\x00' not in name
    path = PurePosixPath(name)
    assert not path.is_absolute() and all(x not in ('', '.', '..') for x in name.split('/'))
    assert str(path) == name
    return path

def validate_inventory(inv):
    assert inv['schema'] == SCHEMA and inv['file_only'] is True
    assert isinstance(inv['files'], dict) and inv['files']
    for name, entry in inv['files'].items():
        canonical_name(name)
        assert set(entry) == {'bytes', 'sha256'}
        assert type(entry['bytes']) is int and entry['bytes'] >= 0
        assert isinstance(entry['sha256'], str) and len(entry['sha256']) == 64
        assert all(c in '0123456789abcdef' for c in entry['sha256'])
    assert inv['members'] == len(inv['files'])
    assert inv['uncompressed_file_bytes'] == sum(x['bytes'] for x in inv['files'].values())
    name = inv['source_manifest_name']
    canonical_name(name)
    assert inv['files'][name]['sha256'] == inv['source_manifest_sha256']

def validated_members(archive, inv):
    validate_inventory(inv)
    assert sha(archive) == inv['archive_sha256']
    assert Path(archive).stat().st_size == inv['archive_bytes']
    result = {}
    with tarfile.open(archive, 'r:xz') as stream:
        for member in stream:
            name = member.name
            canonical_name(name)
            assert name in inv['files'] and name not in result
            assert member.isfile() and not member.issym() and not member.islnk()
            assert member.mode == 0o644 and member.uid == member.gid == 0
            assert member.uname == member.gname == '' and member.mtime == 0
            assert not member.pax_headers and not member.linkname
            entry = inv['files'][name]
            assert member.size == entry['bytes']
            source = stream.extractfile(member)
            assert source is not None
            data = source.read(entry['bytes'] + 1)
            assert len(data) == entry['bytes'] and sha_bytes(data) == entry['sha256']
            result[name] = data
    assert set(result) == set(inv['files'])
    with lzma.open(archive, 'rb') as source:
        while source.read(1 << 20):
            pass
    original = json.loads(result[inv['source_manifest_name']])
    assert set(original['files']) | {inv['source_manifest_name']} == set(result)
    for name, entry in original['files'].items():
        assert inv['files'][name] == {'bytes': entry['bytes'], 'sha256': entry['sha256']}
    return result

def build(source, archive, inventory, manifest_name, manifest_sha):
    source, archive, inventory = map(lambda p: Path(p).resolve(), (source, archive, inventory))
    canonical_name(manifest_name)
    assert source.is_dir() and not archive.exists() and not inventory.exists()
    assert not archive.is_relative_to(source) and not inventory.is_relative_to(source)
    assert sha(source / manifest_name) == manifest_sha
    original = json.loads((source / manifest_name).read_text())
    files = {}
    for path in sorted(source.rglob('*')):
        assert not path.is_symlink()
        if path.is_dir():
            continue
        assert path.is_file()
        name = str(path.relative_to(source))
        canonical_name(name)
        data = path.read_bytes()
        files[name] = dict(bytes=len(data), sha256=sha_bytes(data))
    assert set(files) == set(original['files']) | {manifest_name}
    for name, entry in original['files'].items():
        assert files[name] == {'bytes': entry['bytes'], 'sha256': entry['sha256']}
    with archive.open('xb') as raw:
        with lzma.LZMAFile(raw, 'w', format=lzma.FORMAT_XZ, check=lzma.CHECK_CRC64, preset=1) as compressed:
            with tarfile.open(fileobj=compressed, mode='w|', format=tarfile.USTAR_FORMAT) as stream:
                for name, entry in files.items():
                    data = (source / name).read_bytes()
                    assert len(data) == entry['bytes'] and sha_bytes(data) == entry['sha256']
                    member = tarfile.TarInfo(name)
                    member.size = len(data)
                    member.mode = 0o644
                    member.uid = member.gid = 0
                    member.uname = member.gname = ''
                    member.mtime = 0
                    stream.addfile(member, io.BytesIO(data))
        raw.flush()
        os.fsync(raw.fileno())
    inv = dict(schema=SCHEMA, file_only=True, compression='XZ CRC64 preset1', tar_format='USTAR',
        deterministic_order='lexicographically sorted relative regular-file paths',
        metadata=dict(mode='0644', uid=0, gid=0, uname='', gname='', mtime=0),
        source_manifest_name=manifest_name, source_manifest_sha256=manifest_sha,
        archive_sha256=sha(archive), archive_bytes=archive.stat().st_size, members=len(files),
        uncompressed_file_bytes=sum(x['bytes'] for x in files.values()), files=files)
    validated_members(archive, inv)
    for name, entry in files.items():
        assert sha(source / name) == entry['sha256']
    with inventory.open('x') as out:
        json.dump(inv, out, indent=2, sort_keys=True)
        out.write('\n')
    return inv

def extract(archive, inventory, output):
    archive, inventory = Path(archive).resolve(), Path(inventory).resolve()
    target = Path(os.path.abspath(output))
    assert target == target.resolve() and target.parent.is_dir()
    assert not target.exists() and not target.is_symlink()
    assert not archive.is_relative_to(target) and not inventory.is_relative_to(target)
    inv = json.loads(inventory.read_text())
    inventory_hash = sha(inventory)
    data = validated_members(archive, inv)
    target.mkdir(exist_ok=False)
    for name, content in data.items():
        path = target / name
        path.parent.mkdir(parents=True, exist_ok=True)
        assert path.resolve().is_relative_to(target)
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644)
        os.fchmod(fd, 0o644)
        with os.fdopen(fd, 'wb') as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        assert sha(path) == inv['files'][name]['sha256']
    observed = {str(path.relative_to(target)) for path in target.rglob('*') if path.is_file()}
    assert observed == set(inv['files'])
    assert sha(inventory) == inventory_hash and sha(archive) == inv['archive_sha256']
    return dict(status='PASS_EXACT_FRESH_CHECKPOINT_EXTRACTION', members=len(data),
        bytes=sum(len(x) for x in data.values()), archive_sha256=inv['archive_sha256'],
        inventory_sha256=inventory_hash, source_manifest_sha256=sha(target / inv['source_manifest_name']),
        proof_arithmetic_replayed=False, native_aliases_installed=False, new_original_cells=0, new_masks=0)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest='mode', required=True)
    builder = sub.add_parser('build')
    for name in ('source', 'archive', 'inventory'):
        builder.add_argument(name, type=Path)
    builder.add_argument('manifest_name')
    builder.add_argument('manifest_sha')
    extractor = sub.add_parser('extract')
    for name in ('archive', 'inventory', 'output'):
        extractor.add_argument(name, type=Path)
    verifier = sub.add_parser('verify')
    for name in ('archive', 'inventory'):
        verifier.add_argument(name, type=Path)
    args = parser.parse_args()
    if args.mode == 'build':
        result = build(args.source, args.archive, args.inventory, args.manifest_name, args.manifest_sha)
        print(json.dumps({k: result[k] for k in ('archive_sha256', 'archive_bytes', 'members', 'uncompressed_file_bytes')}))
    elif args.mode == 'extract':
        print(json.dumps(extract(args.archive, args.inventory, args.output)))
    else:
        result = json.loads(args.inventory.read_text())
        validated_members(args.archive, result)
        print(json.dumps(dict(status='PASS_COMPLETE_REGULAR_FILE_ARCHIVE', members=result['members'], archive_sha256=result['archive_sha256'])))
