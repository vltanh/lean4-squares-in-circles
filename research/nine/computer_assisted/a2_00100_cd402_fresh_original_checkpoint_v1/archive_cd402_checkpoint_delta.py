"""Stream the immutable delta to xz and audit every archive member."""
from pathlib import Path
import hashlib
import json
import lzma
import tarfile
import time

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'delta'
ARCHIVE = HERE / 'cd402_fresh_original_checkpoint_v1_delta.tar.xz'
ROOT = 'cd402_checkpoint_delta'


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for data in iter(lambda: stream.read(4 * 1024 * 1024), b''):
            digest.update(data)
    return digest.hexdigest()


def main():
    started = time.monotonic()
    assert not ARCHIVE.exists()
    files = {str(path.relative_to(SOURCE)): dict(sha256=sha(path), bytes=path.stat().st_size)
        for path in sorted(SOURCE.rglob('*')) if path.is_file()}
    assert all(not (SOURCE / name).is_symlink() for name in files)
    with lzma.open(ARCHIVE, 'wb', preset=6) as compressed:
        with tarfile.open(fileobj=compressed, mode='w|', format=tarfile.PAX_FORMAT) as archive:
            for name, entry in files.items():
                source = SOURCE / name
                member = tarfile.TarInfo(ROOT + '/' + name)
                member.size = entry['bytes']
                member.mode = 0o644
                member.mtime = 0
                member.uid = member.gid = 0
                member.uname = member.gname = ''
                with source.open('rb') as stream:
                    archive.addfile(member, stream)
    checked = set()
    with tarfile.open(ARCHIVE, mode='r|xz') as archive:
        for member in archive:
            assert member.isfile() and member.name.startswith(ROOT + '/')
            name = member.name[len(ROOT) + 1:]
            assert name in files and name not in checked
            assert member.size == files[name]['bytes']
            stream = archive.extractfile(member)
            assert stream is not None
            digest = hashlib.sha256()
            for data in iter(lambda: stream.read(4 * 1024 * 1024), b''):
                digest.update(data)
            assert digest.hexdigest() == files[name]['sha256']
            checked.add(name)
    assert checked == set(files)
    for name, entry in files.items():
        assert sha(SOURCE / name) == entry['sha256']
    result = dict(status='PASS_CD402_DELTA_ARCHIVE_BYTE_AUDIT', archive=ARCHIVE.name,
        archive_root=ROOT, archive_sha256=sha(ARCHIVE), bytes=ARCHIVE.stat().st_size,
        files=files, regular_members=len(files), all_sources_unchanged=True,
        no_raw_tar_intermediate=True, new_original_cells=0, new_masks=0,
        seconds=time.monotonic() - started)
    (HERE / 'ARCHIVE_BYTE_AUDIT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'files'}, indent=2), flush=True)


if __name__ == '__main__':
    main()
