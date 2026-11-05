"""Verify all checkpoint bytes; optionally install missing exact native inputs."""
from pathlib import Path
import argparse
import hashlib
import json
import tarfile

ROOTS = (Path('/workspace/scratch'),
         Path('/workspace/lean4-squares-in-circles/research/nine/.runs'))

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('packet', type=Path)
    ap.add_argument('--restore', action='store_true')
    args = ap.parse_args()
    here = args.packet.resolve()
    manifest = json.loads((here / 'MANIFEST.json').read_text())
    for name, expected in manifest['files'].items():
        assert Path(name).name == name and sha(here / name) == expected, name
    entries = json.loads((here / 'INPUTS.json').read_text())['files']
    assert len(entries) == manifest.get('source_input_paths', manifest.get('input_paths'))
    by_hash = {}
    for e in entries:
        p = Path(e['path'])
        assert p.is_absolute() and any(p.is_relative_to(root) for root in ROOTS)
        assert any(p.resolve().is_relative_to(root.resolve()) for root in ROOTS)
        assert not p.is_symlink()
        if args.restore and p.exists():
            assert p.is_file() and p.stat().st_size == e['bytes'] and sha(p) == e['sha256'], str(p)
        by_hash.setdefault(e['sha256'], []).append(e)
    observed = set()
    installed = 0
    with tarfile.open(here / 'inputs.tar.xz', 'r|xz') as t:
        for m in t:
            assert m.isfile() and m.name.startswith('sources/')
            digest = m.name.removeprefix('sources/')
            assert digest in by_hash and digest not in observed
            raw = t.extractfile(m).read()
            assert hashlib.sha256(raw).hexdigest() == digest
            for e in by_hash[digest]:
                assert len(raw) == e['bytes']
                p = Path(e['path'])
                if args.restore and not p.exists():
                    p.parent.mkdir(parents=True, exist_ok=True)
                    with p.open('xb') as f:
                        f.write(raw)
                    installed += 1
                if args.restore:
                    assert sha(p) == digest
            observed.add(digest)
    assert observed == set(by_hash)
    assert len(observed) == manifest.get('unique_input_blobs', manifest.get('unique_blobs'))
    print(json.dumps(dict(status='PASS_NATIVE_CHECKPOINT_BYTES', paths=len(entries),
        unique_blobs=len(observed), installed=installed, arithmetic_replayed=False,
        new_original_cells=0, new_masks=0)))

if __name__ == '__main__':
    assert __debug__
    main()
