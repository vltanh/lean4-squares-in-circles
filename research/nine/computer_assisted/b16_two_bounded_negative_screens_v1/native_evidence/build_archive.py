#!/usr/bin/env python3
"""Deterministic streaming preservation of two bounded negative exact screens."""
from pathlib import Path
import hashlib
import io
import json
import lzma
import tarfile

ROOT = Path('/workspace/scratch/f9f48fcfb253')
HERE = Path(__file__).resolve().parent
ARCHIVE = ROOT / 'b_work/B16_BOUNDED_NEGATIVE_SCREENS_V1.tar.xz'
SOURCES = {
    'README.md': HERE / 'README.md',
    'build_archive.py': HERE / 'build_archive.py',
    'source/existing_propagation_screen.py': ROOT / 'b_work/b16_existing_propagation_screen_v1/screen_repeated_propagation.py',
    'source/existing_propagation_binding.json': ROOT / 'b_work/b16_existing_propagation_screen_v1/SOURCE_BINDING.json',
    'dg/screen.py': ROOT / 'b_work/b16_dg_exact_screen_v1/screen.py',
    'dg/SOURCE_BINDING.json': ROOT / 'b_work/b16_dg_exact_screen_v1/SOURCE_BINDING.json',
    'dg/SCREEN.json': ROOT / 'b_work/B16_DG14_COMPLETE_EIGHT_SCREEN_V1.json',
    'dg/SCREEN.log': ROOT / 'b_work/B16_DG14_COMPLETE_EIGHT_SCREEN_V1.log',
    'dg/OBSERVED_EXIT.json': ROOT / 'b_work/B16_DG14_COMPLETE_EIGHT_SCREEN_V1_EXIT_RECEIPT.json',
    'intersection/screen.py': ROOT / 'b_work/b16_external127_root_bound_screen_v1/screen.py',
    'intersection/SOURCE_BINDING.json': ROOT / 'b_work/b16_external127_root_bound_screen_v1/SOURCE_BINDING.json',
    'intersection/SCREEN.json': ROOT / 'b_work/B16_EXTERNAL127_ROOT_BOUND_SCREEN_V1.json',
    'intersection/SCREEN.log': ROOT / 'b_work/B16_EXTERNAL127_ROOT_BOUND_SCREEN_V1.log',
    'intersection/OBSERVED_EXIT.json': ROOT / 'b_work/B16_EXTERNAL127_ROOT_BOUND_SCREEN_V1_EXIT_RECEIPT.json',
    'dependencies/EXTERNAL_SNAPSHOT_RECEIPT.json': ROOT / 'repo/research/nine/.runs/b16_external127_snapshot_v1/SNAPSHOT_RECEIPT.json',
    'dependencies/EXTERNAL_SNAPSHOT_EXIT.json': ROOT / 'b_work/B16_EXTERNAL127_SNAPSHOT_V3_EXIT_RECEIPT.json',
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    assert __debug__ and not ARCHIVE.exists()
    manifest_path = HERE / 'MEMBER_MANIFEST.json'
    receipt_path = HERE / 'ARCHIVE_READY.json'
    assert not manifest_path.exists() and not receipt_path.exists()
    pins = {name: dict(native_path=str(path), sha256=sha(path), bytes=path.stat().st_size)
            for name, path in sorted(SOURCES.items())}
    manifest = dict(schema='B16_two_bounded_negative_screens_archive_v1',
        members=pins, mathematical_credit=0, self_contained_proof_claimed=False,
        native_dependencies_explicit=True, no_raw_tar_created=True)
    raw_manifest = (json.dumps(manifest, indent=2) + '\n').encode()
    manifest_path.write_bytes(raw_manifest)
    with ARCHIVE.open('xb') as raw:
        with lzma.LZMAFile(raw, 'w', format=lzma.FORMAT_XZ, preset=1) as compressed:
            with tarfile.open(fileobj=compressed, mode='w|', format=tarfile.PAX_FORMAT) as archive:
                for name in sorted(list(SOURCES) + ['MEMBER_MANIFEST.json']):
                    data = raw_manifest if name == 'MEMBER_MANIFEST.json' else SOURCES[name].read_bytes()
                    if name != 'MEMBER_MANIFEST.json':
                        assert len(data) == pins[name]['bytes'] and hashlib.sha256(data).hexdigest() == pins[name]['sha256']
                    info = tarfile.TarInfo('b16_bounded_negative_screens_v1/' + name)
                    info.size = len(data)
                    info.mode = 0o644
                    info.uid = info.gid = info.mtime = 0
                    info.uname = info.gname = ''
                    archive.addfile(info, io.BytesIO(data))
    expected = dict(pins)
    expected['MEMBER_MANIFEST.json'] = dict(bytes=len(raw_manifest), sha256=hashlib.sha256(raw_manifest).hexdigest())
    seen = set()
    with tarfile.open(ARCHIVE, 'r:xz') as archive:
        for member in archive:
            assert member.isfile() and member.name.startswith('b16_bounded_negative_screens_v1/')
            name = member.name.removeprefix('b16_bounded_negative_screens_v1/')
            assert name in expected and name not in seen
            assert member.uid == member.gid == member.mtime == 0 and member.mode == 0o644
            data = archive.extractfile(member).read()
            assert len(data) == expected[name]['bytes'] and hashlib.sha256(data).hexdigest() == expected[name]['sha256']
            seen.add(name)
    assert seen == set(expected)
    for name, path in SOURCES.items():
        assert sha(path) == pins[name]['sha256'] and path.stat().st_size == pins[name]['bytes']
    assert sha(manifest_path) == expected['MEMBER_MANIFEST.json']['sha256']
    receipt = dict(status='PASS_COMPLETE_COMPRESSED_NEGATIVE_EVIDENCE_BYTE_AUDIT',
        archive=str(ARCHIVE), archive_sha256=sha(ARCHIVE), archive_bytes=ARCHIVE.stat().st_size,
        members=len(seen), member_manifest_sha256=sha(manifest_path),
        every_member_and_source_rehashed=True, no_raw_tar_created=True,
        arithmetic_replayed=False, new_original_cells=0, new_masks=0)
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
