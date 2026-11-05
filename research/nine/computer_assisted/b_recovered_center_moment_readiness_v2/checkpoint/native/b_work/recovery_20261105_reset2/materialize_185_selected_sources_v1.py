#!/usr/bin/env python3
"""Restore only the185 exact committed source/member mappings, absent-only."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import os
import tarfile
import tempfile

ROOT=Path('/workspace/scratch/f9f48fcfb253')
HERE=Path(__file__).resolve().parent
PACKET=HERE/'published_35ac6d675d/transport'

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb')as f:
        for b in iter(lambda:f.read(1<<20),b''):h.update(b)
    return h.hexdigest()

def main():
    if not __debug__:raise RuntimeError('Assertions must be enabled')
    selection=PACKET/'PUBLICATION_FILE_SELECTION.json'
    assert sha(selection)=='859dbc1a1433f10fa31a3f76a5445f7779977211e403497614d63dd70c5a0edc'
    data=json.loads(selection.read_text());entries={e['member']:e for e in data['files']}
    assert len(entries)==data['file_count']==185
    for member,e in entries.items():
        target=Path(e['source']);relative=target.relative_to(ROOT)
        assert member=='native/'+relative.as_posix()
        assert not target.is_symlink()and target.resolve().is_relative_to(ROOT)
        if target.exists():assert target.is_file()and sha(target)==e['sha256'],str(target)
    archive=PACKET/'b_recovery_center_continuations_v1.tar.xz'
    assert sha(archive)=='ddba86d2dda6c261e1a3b2868459ddbb7eced058fc0c91c8b72d56254d6f6e93'
    seen=set();installed=[];retained=[]
    with tarfile.open(archive,'r|xz')as stream:
        for m in stream:
            name=m.name;rel=PurePosixPath(name)
            assert name in entries and name not in seen and m.isfile()
            assert not rel.is_absolute()and '..'not in rel.parts
            e=entries[name];assert m.size==e['bytes']
            f=stream.extractfile(m);assert f is not None;content=f.read()
            assert len(content)==e['bytes']and hashlib.sha256(content).hexdigest()==e['sha256']
            target=Path(e['source']);target.parent.mkdir(parents=True,exist_ok=True)
            if target.exists():
                assert sha(target)==e['sha256'];retained.append(str(target))
            else:
                fd,temp=tempfile.mkstemp(prefix='B_RESTORE_EXACT_',dir=target.parent)
                try:
                    with os.fdopen(fd,'wb')as out:out.write(content);out.flush();os.fsync(out.fileno())
                    os.chmod(temp,0o644)
                    try:os.link(temp,target);installed.append(str(target))
                    except FileExistsError:
                        assert target.is_file()and sha(target)==e['sha256'];retained.append(str(target))
                finally:os.unlink(temp)
            assert sha(target)==e['sha256'];seen.add(name)
    assert seen==set(entries)
    for e in entries.values():assert sha(e['source'])==e['sha256']
    receipt=dict(status='PASS_EXACT185_CANONICAL_SOURCE_RESTORATION',
        selection_sha256=sha(selection),archive_sha256=sha(archive),members=185,
        installed_absent_paths=installed,retained_identical_paths=retained,
        all_canonical_paths_rehashed=True,existing_different_file_overwritten=False,
        arithmetic_repeated=False,live_tree_modified=False,numerical_search_started=False,
        new_original_cells=0,new_masks=0)
    output=HERE/'B_185_CANONICAL_RESTORATION.json'
    with output.open('x')as f:json.dump(receipt,f,indent=2);f.write('\n')
    print(json.dumps(dict(status=receipt['status'],installed=len(installed),retained=len(retained),
        receipt_sha256=sha(output))),flush=True)

if __name__=='__main__':main()
