#!/usr/bin/env python3
"""Independent streaming byte audit of the selected B recovery transport.

This imports no archive producer, proof checker, or numerical dependency. It
checks exactly the selected regular-file members and published prerequisites.
It does not extract files or claim a fresh arithmetic or portable proof replay.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import tarfile

def sha_file(path):
    digest=hashlib.sha256()
    with Path(path).open('rb')as stream:
        for chunk in iter(lambda:stream.read(65536),b''):digest.update(chunk)
    return digest.hexdigest()

def verify(directory,expected_manifest_sha256):
    directory=Path(directory).resolve()
    manifest_path=directory/'MEMBER_MANIFEST.json'
    assert sha_file(manifest_path)==expected_manifest_sha256
    manifest=json.loads(manifest_path.read_text())
    assert manifest['schema']=='B_recovery_exact_selected_member_transport_v1'
    assert manifest['selected_members']==185 and len(manifest['members'])==185
    assert manifest['arithmetic_replayed']is False and manifest['standalone_portable_proof']is False
    assert manifest['new_original_cells']==manifest['new_masks']==0
    selection_path=directory/'PUBLICATION_FILE_SELECTION.json'
    assert sha_file(selection_path)==manifest['selection_sha256']
    selection=json.loads(selection_path.read_text())
    assert selection['file_count']==185 and selection['live_tree_or_log_files']==0
    expected={e['member']:dict(sha256=e['sha256'],bytes=e['bytes'])for e in selection['files']}
    assert len(expected)==185 and expected==manifest['members']
    dependencies=directory/'REQUIRED_PUBLISHED_ANCESTRY.json'
    assert sha_file(dependencies)==manifest['required_published_ancestry_sha256']
    dep=json.loads(dependencies.read_text())
    assert dep['standalone_portable_proof']is False and dep['new_original_cells']==dep['new_masks']==0
    assert len(dep['archives'])==8
    archive_name=manifest['archive']['file']
    assert Path(archive_name).name==archive_name
    archive=directory/archive_name
    assert archive.stat().st_size==manifest['archive']['bytes']
    assert sha_file(archive)==manifest['archive']['sha256']
    seen=set();total=0
    with tarfile.open(archive,mode='r|xz')as stream:
        for member in stream:
            name=member.name;rel=PurePosixPath(name)
            assert member.isfile() and not member.issym() and not member.islnk()
            assert not rel.is_absolute() and '..'not in rel.parts
            assert name in expected and name not in seen
            assert member.uid==member.gid==member.mtime==0
            assert member.mode==0o644 and member.uname==member.gname==''
            assert member.linkname=='' and member.size==expected[name]['bytes']
            payload=stream.extractfile(member);assert payload is not None
            digest=hashlib.sha256();count=0
            for chunk in iter(lambda:payload.read(65536),b''):
                digest.update(chunk);count+=len(chunk)
            assert count==expected[name]['bytes'] and digest.hexdigest()==expected[name]['sha256']
            seen.add(name);total+=count
    assert seen==set(expected) and total==selection['bytes']==manifest['raw_member_bytes']
    return dict(status='PASS_EXACT_185_MEMBER_B_RECOVERY_TRANSPORT',
        archive_sha256=manifest['archive']['sha256'],member_manifest_sha256=expected_manifest_sha256,
        selection_sha256=manifest['selection_sha256'],members=185,raw_member_bytes=total,
        required_published_archives=8,regular_files_only=True,canonical_transport_metadata=True,
        no_extraction_performed=True,arithmetic_replayed=False,standalone_portable_proof=False,
        new_original_cells=0,new_masks=0)

def main():
    if not __debug__:raise RuntimeError('Exact assertions must be enabled')
    parser=argparse.ArgumentParser();parser.add_argument('directory',type=Path)
    parser.add_argument('--expected-manifest-sha256',required=True)
    parser.add_argument('--report',type=Path,required=True)
    args=parser.parse_args();assert not args.report.exists()
    report=verify(args.directory,args.expected_manifest_sha256)
    report['checker_sha256']=sha_file(__file__)
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)

if __name__=='__main__':main()
