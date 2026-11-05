#!/usr/bin/env python3
"""Export the committed B recovery packet to a new directory, without Git writes."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess

ROOT=Path('/workspace/scratch/f9f48fcfb253')
REPO=ROOT/'repo'
COMMIT='35ac6d675d74f013a59804ef5506b74b005b59d6'
PREFIX='research/nine/computer_assisted/b_recovery_center_continuations_v1'
OUTPUT=Path(__file__).resolve().parent/'published_35ac6d675d'
ARCHIVE_SHA='ddba86d2dda6c261e1a3b2868459ddbb7eced058fc0c91c8b72d56254d6f6e93'

def main():
    if not __debug__:raise RuntimeError('Assertions must be enabled')
    assert not OUTPUT.exists()
    raw=subprocess.check_output(['git','-C',str(REPO),'ls-tree','-r','-z',COMMIT,'--',PREFIX])
    entries=[]
    for item in raw.split(b'\0'):
        if not item:continue
        meta,path=item.split(b'\t',1);mode,kind,oid=meta.decode().split()
        path=path.decode();assert mode=='100644'and kind=='blob'
        assert path.startswith(PREFIX+'/')
        relative=PurePosixPath(path[len(PREFIX)+1:])
        assert not relative.is_absolute()and '..'not in relative.parts
        entries.append((str(relative),oid,path))
    assert entries and len({relative for relative,oid,path in entries})==len(entries)
    OUTPUT.mkdir()
    files=[]
    for relative,oid,path in entries:
        data=subprocess.check_output(['git','-C',str(REPO),'cat-file','blob',oid])
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==oid
        target=OUTPUT/relative;target.parent.mkdir(parents=True,exist_ok=True)
        with target.open('xb')as f:f.write(data)
        target.chmod(0o644)
        files.append(dict(path=relative,git_path=path,git_blob_sha1=oid,
                          sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
    archive=OUTPUT/'transport/b_recovery_center_continuations_v1.tar.xz'
    assert hashlib.sha256(archive.read_bytes()).hexdigest()==ARCHIVE_SHA
    for e in files:
        data=(OUTPUT/e['path']).read_bytes()
        assert len(data)==e['bytes']and hashlib.sha256(data).hexdigest()==e['sha256']
    receipt=dict(status='PASS_COMMITTED_GIT_BLOB_AND_SHA256_EXPORT',commit=COMMIT,
        prefix=PREFIX,output=str(OUTPUT),files=files,archive_sha256=ARCHIVE_SHA,
        index_or_ref_mutated=False,arithmetic_repeated=False,live_tree_touched=False,
        numerical_search_started=False,original_or_mask_credit=0)
    path=OUTPUT/'GIT_EXPORT_RECEIPT.json'
    with path.open('x')as f:json.dump(receipt,f,indent=2);f.write('\n')
    print(json.dumps(dict(status=receipt['status'],files=len(files),
        receipt_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),archive_sha256=ARCHIVE_SHA)),flush=True)

if __name__=='__main__':main()
