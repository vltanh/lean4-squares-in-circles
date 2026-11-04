"""Prepare the source-reviewed, freshly replayed OPEN Cd402 checkpoint."""
from pathlib import Path
import hashlib
import json
import shutil

HERE = Path(__file__).resolve().parent
WORK = HERE.parent.parent
DEST = WORK / 'repo/research/nine/computer_assisted/a2_00100_cd402_fresh_original_checkpoint_v1'
FRESH = Path('/tmp/cd402_checkpoint_fresh_replay_20261104')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def copy(source, target):
    source, target = Path(source), Path(target)
    assert source.is_file() and not source.is_symlink()
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    assert sha(target) == sha(source)


def main():
    assert not DEST.exists()
    receipt = json.loads((FRESH / 'PORTABLE_RECEIPT.json').read_text())
    assert receipt['status'] == 'PASS_FRESH_PORTABLE_CD402_WHOLE_ORIGINAL_OPEN_CHECKPOINT'
    assert receipt['new_original_cells'] == receipt['new_masks'] == 0
    assert sha(FRESH / 'PORTABLE_RECEIPT.json') == '7dd4ff783f9d388ad3b92479bcaf2bc7e1f80649e469ea4b5c6e5046f2854096'
    for entry in receipt['exact_reports'].values():
        assert sha(FRESH / entry['path']) == entry['sha256']
    audit = json.loads((HERE / 'ARCHIVE_BYTE_AUDIT.json').read_text())
    archive = HERE / audit['archive']
    assert sha(archive) == audit['archive_sha256']
    assert audit['regular_members'] == 40 and audit['all_sources_unchanged'] is True
    DEST.mkdir(parents=True)
    copy(archive, DEST / archive.name)
    for name in ('ARCHIVE_BYTE_AUDIT.json', 'ROOT_PORTABLE_CHECKPOINT_ACCEPTANCE.md',
                 'archive_cd402_checkpoint_delta.py', 'prepare_publication.py'):
        copy(HERE / name, DEST / name)
    copy(HERE / 'delta/DELTA_MANIFEST.json', DEST / 'DELTA_MANIFEST.json')
    for path in sorted(FRESH.rglob('*')):
        if path.is_file():
            copy(path, DEST / 'fresh_replay' / path.relative_to(FRESH))
    reviews = WORK / 'global_work/cd402_complete_cover_review'
    for name in ('INDEPENDENT_PHYSICAL_SCOPE_AND_TRAVERSAL_REVIEW.md',
                 'INDEPENDENT_SOURCE_REVIEW.json', 'PORTABLE_TRANSPORT_SOURCE_REVIEW.md',
                 'PORTABLE_TRANSPORT_SOURCE_REVIEW.json'):
        copy(reviews / name, DEST / 'reviews' / name)
    for name in ('CD402_FRESH_ORIGINAL_MODEL_HAND_PROOF.md',
                 'CD402_WHOLE_ORIGINAL_CONTINUATION_HAND_PROOF.md',
                 'CD402_COMPLETE_COVER_ATTACHMENT_CONTROLS.json'):
        copy(WORK / 'd_work/cd402_work' / name, DEST / name)
    readme = '''# C d402: certified whole-original OPEN checkpoint

This package gives a fresh original-domain reconstruction and three exact
bound rounds for `negative-d4021ade840b985c` of mask `001/00`, followed by a
complete one-node OPEN continuation seed. It does **not** exclude the
original or close its mask. The fixed ledger remains **220/231 original
cells and 8/32 masks closed**; no positional-root or roadmap credit is added.

The caller retains all nine original unit squares, all 36 corners and
physical pairs, all five marked cones, actual AB/BC/EF/FG, strictly weak CD,
and the unchanged registered path. The initializer starts with independently
reconstructed analytic bounds and no borrowed Cartesian or diagonal
intervals. No C887 or Cb882 height consequence is used.

## Verified evidence

| Check | Result |
| --- | --- |
| Fresh initial static attachment | 46,584 reconstructed rows; 12 changed callers rejected |
| Whole-original bound proof | 3 rounds; 556 deductions; 948 premise rows; OPEN |
| Four-product corner uses in that proof | 64 exact occurrences |
| Continuation attachment | Complete seed and 4/8/2 OPEN fixtures; 12 damaged covers rejected |
| Fresh portable replay | Bound and complete OPEN seed, each with original reconstruction |
| Portable inventory | 2,054 inputs; every input rehashed at completion |
| Delta archive | 40 regular members, every member byte-checked |

The two hand documents state the literal original path, physical meaning,
exact residual arithmetic, complete-cover induction and remaining acceptance
gates. Independent scope/source reviews and root acceptance are included.
The numerical driver is prepared for continuation; its scheduling choices
add no physical premise. All actual future proof records need ordinary exact
replay before any complete-original claim.

## Reproduce the portable proof

Use Python 3.12 with assertions enabled and `-B -S`. First reconstruct the
published C source packet using
[`c_original_height_consequences_v1`](../c_original_height_consequences_v1/README.md)
from commit `8e842e98a4f31fa9e0a2d8ece42bc2661a2783c2`. Its input manifest
must be `06115f494173bc344821932525d7a8522df8ea2ed80b400f735f3b68d4a1b58b`.
Those existing immutable sources supply dependencies only; the Cd402 proof
does not invoke either other original's height theorem.

Extract `cd402_fresh_original_checkpoint_v1_delta.tar.xz`; its archive root
is `cd402_checkpoint_delta`. The archive SHA256 is
`ac370a5d945796f2566263d0733ce330eaabc7c816a2043ae5128750697de650`.
With `base` and `delta` set to those two extracted directories, run:

```sh
python3.12 -B -S "$delta/materialize_cd402_checkpoint.py" \\
  --base "$base" --delta "$delta" --output /tmp/cd402-proof-packet
python3.12 -B -S /tmp/cd402-proof-packet/replay_portable_cd402_checkpoint.py \\
  --packet /tmp/cd402-proof-packet --output /tmp/cd402-proof-output
```

Use fresh output directories. The assembled input manifest must be
`ac8b7793e1c69242c8df85a28596e3143b1f54e605368c097198444e8002f51c`.
The final receipt must report
`PASS_FRESH_PORTABLE_CD402_WHOLE_ORIGINAL_OPEN_CHECKPOINT` with zero new
originals and masks. It freshly checks the whole original, then checks the
complete OPEN seed; it does not trust the archived PASS reports.

The unchanged C transport operates only in isolated-worker mode. It blocks
old-workspace reads, unlisted packet reads, packet mutations and numerical
imports. Its generic child receipts retain their legacy C887/Cb882 label;
those labels identify the inherited transport, not the invoked Cd402 proof.
The actual Cd402 reports and the outer receipt bind the exact Cd402 ID and
path. Raw source/certificate bytes and mathematical strings are unchanged.

`fresh_replay/` contains the complete cold-run outputs. Native attachment
controls and the numerical provenance remain in the delta. The earlier
failed raw-tuple static diagnostic is preserved: seven explicit zero
coefficients were canonicalized by the existing exact arithmetic core;
no row value or mathematical rule was changed. No Lean, Lake or CI ran.
PR11 remains draft and unmerged.
'''
    (DEST / 'README.md').write_text(readme)
    files = {str(path.relative_to(DEST)): sha(path) for path in sorted(DEST.rglob('*')) if path.is_file()}
    (DEST / 'PUBLICATION_MANIFEST.json').write_text(json.dumps(dict(
        schema='Cd402_fresh_original_OPEN_checkpoint_publication_v1', files=files,
        original_id='negative-d4021ade840b985c', original_status='OPEN',
        archive_sha256=audit['archive_sha256'], portable_receipt_sha256=sha(FRESH / 'PORTABLE_RECEIPT.json'),
        new_original_cells=0, new_masks=0, new_positional_roots=0, new_roadmap_gates=0,
        original_cells_closed=220, original_cells_total=231, masks_closed=8, masks_total=32,
        lean_lake_ci_run=False), indent=2) + '\n')
    print(json.dumps(dict(status='PREPARED_CD402_OPEN_CHECKPOINT_PUBLICATION',
        files=len(files) + 1, archive_bytes=archive.stat().st_size,
        publication_manifest_sha256=sha(DEST / 'PUBLICATION_MANIFEST.json'))), flush=True)


if __name__ == '__main__':
    main()
