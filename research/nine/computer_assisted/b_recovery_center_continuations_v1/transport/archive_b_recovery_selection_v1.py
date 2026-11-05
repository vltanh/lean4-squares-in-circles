#!/usr/bin/env python3
"""Deterministic xz transport of the exact 185-file selection, with no raw tar."""
from pathlib import Path
import argparse
import hashlib
import io
import json
import lzma
import shutil
import tarfile

HERE=Path(__file__).resolve().parent
SELECTION=HERE/'publication_selection_v2/PUBLICATION_FILE_SELECTION.json'
SELECTION_SHA='859dbc1a1433f10fa31a3f76a5445f7779977211e403497614d63dd70c5a0edc'

def sha(path):
    digest=hashlib.sha256()
    with Path(path).open('rb')as stream:
        for chunk in iter(lambda:stream.read(1<<20),b''):digest.update(chunk)
    return digest.hexdigest()

class CheckedRead:
    def __init__(self,source):self.source=source;self.digest=hashlib.sha256();self.count=0
    def read(self,n=-1):
        result=self.source.read(n);self.digest.update(result);self.count+=len(result);return result

def main():
    if not __debug__:raise RuntimeError('Exact assertions must be enabled')
    parser=argparse.ArgumentParser();parser.add_argument('output',type=Path);args=parser.parse_args()
    assert sha(SELECTION)==SELECTION_SHA
    selection=json.loads(SELECTION.read_text())
    assert selection['file_count']==len(selection['files'])==185 and selection['live_tree_or_log_files']==0
    assert len({e['member']for e in selection['files']})==185
    output=args.output.resolve();output.mkdir(parents=True,exist_ok=False)
    entries=sorted(selection['files'],key=lambda e:e['member'])
    for e in entries:
        path=Path(e['source']);assert path.stat().st_size==e['bytes'] and sha(path)==e['sha256']
    archive=output/'b_recovery_center_continuations_v1.tar.xz'
    with lzma.open(archive,'xb',preset=1)as compressed:
        with tarfile.open(fileobj=compressed,mode='w|',format=tarfile.PAX_FORMAT)as tar:
            for entry in entries:
                info=tarfile.TarInfo(entry['member']);info.size=entry['bytes']
                info.mode=0o644;info.uid=info.gid=info.mtime=0;info.uname=info.gname=''
                with Path(entry['source']).open('rb')as stream:
                    checked=CheckedRead(stream);tar.addfile(info,checked)
                    assert checked.count==entry['bytes'] and checked.digest.hexdigest()==entry['sha256']
    for entry in entries:
        assert Path(entry['source']).stat().st_size==entry['bytes'] and sha(entry['source'])==entry['sha256']
    shutil.copyfile(SELECTION,output/'PUBLICATION_FILE_SELECTION.json')
    prerequisites=Path(selection['required_published_ancestry']['path'])
    assert sha(prerequisites)==selection['required_published_ancestry']['sha256']
    shutil.copyfile(prerequisites,output/'REQUIRED_PUBLISHED_ANCESTRY.json')
    shutil.copyfile(__file__,output/'archive_b_recovery_selection_v1.py')
    shutil.copyfile(HERE/'verify_b_recovery_transport_v1.py',output/'verify_b_recovery_transport_v1.py')
    manifest=dict(schema='B_recovery_exact_selected_member_transport_v1',
        selected_members=185,raw_member_bytes=selection['bytes'],selection_sha256=SELECTION_SHA,
        required_published_ancestry_sha256=sha(prerequisites),
        archive=dict(file=archive.name,bytes=archive.stat().st_size,sha256=sha(archive),compression='xz preset1'),
        members={e['member']:dict(sha256=e['sha256'],bytes=e['bytes'])for e in entries},
        deterministic_member_order=True,normalized_file_mode='0644',normalized_uid_gid_mtime=0,
        raw_tar_intermediate_created=False,all_expanded_source_bytes_rehashed_before_and_after=True,
        arithmetic_replayed=False,standalone_portable_proof=False,new_original_cells=0,new_masks=0)
    (output/'MEMBER_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
    manifest_sha=sha(output/'MEMBER_MANIFEST.json')
    readme='''# B recovery and accepted-center continuation checkpoint

This deterministic archive preserves exactly 185 immutable selected files:
the complete 45-node B16a I21/I22 OPEN seed, complete 37-node B7c OPEN seed,
five newly attached original-quarter proof wrappers, the local accepted-center
weighted fixture, source code, diffs, hand attachments, exact receipts, source
bindings, and independent/root reviews. It contains no live run tree, log, or
software-only callback fixture. The expanded source files were hash-checked
before, during, and after streaming compression and remain unchanged.

The B16a evidence accounts for fourteen complete original quarters and the
remaining OPEN I21/I22 pair. B7c and the local B580 center fixture remain OPEN.
The new center-enabled atomic driver has not been launched by this preparation.
No original-cell, mask, positional-root, or roadmap register is changed.

`PUBLICATION_FILE_SELECTION.json` binds every raw source/member name, size, and
SHA256. `MEMBER_MANIFEST.json` independently enumerates every logical regular
tar member and the compressed archive hash. The archive uses sorted member
names, mode0644, zero UID/GID/mtime, empty owner names, and xz preset1. It was
streamed directly: no uncompressed tar intermediate was created.

The existing published bulk ancestry is referenced, not recopied.
`REQUIRED_PUBLISHED_ANCESTRY.json` binds eight existing proof/policy archives,
the committed source recovery archive, the accepted center weighted-use packet,
and the original-definition comparison register. The selected native receipts
give the committed Git blob identities and archive/member audits. The archive
is a source-bound continuation/recovery checkpoint, not a standalone portable
proof. Reproduction of arithmetic still requires those exact accepted ancestors
and the ordinary physical/domain/coverage checks. Saved PASS labels are not
substitutes for those checks.

The independent streaming checker hashes every regular member without
extracting it and rejects missing/extra/duplicate/special members, changed
metadata, changed source selection, or changed prerequisite binding. Run:

```
python -B -S verify_b_recovery_transport_v1.py . --expected-manifest-sha256 MANIFEST_SHA --report FRESH_TRANSPORT_REPLAY.json
```

Expected manifest SHA256: `MANIFEST_SHA`.

That command checks byte transport only. It does not rerun arithmetic or grant
proof credit. The separately retained fresh exact reports identify their own
scopes and observed process results. No Lean, Lake, CI, or optimization search
was run by this packaging step.
'''.replace('MANIFEST_SHA',manifest_sha)
    (output/'README.md').write_text(readme)
    receipt=dict(status='ARCHIVE_WRITTEN_INDEPENDENT_BYTE_REPLAY_PENDING',
        selected_members=185,raw_member_bytes=selection['bytes'],archive=manifest['archive'],
        member_manifest_sha256=manifest_sha,selection_sha256=SELECTION_SHA,
        exact_expanded_sources_preserved=True,raw_tar_intermediate_created=False,
        archiver_sha256=sha(__file__),checker_sha256=sha(HERE/'verify_b_recovery_transport_v1.py'),
        readme_sha256=sha(output/'README.md'),new_original_cells=0,new_masks=0)
    (output/'ARCHIVE_WRITTEN.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)

if __name__=='__main__':main()
