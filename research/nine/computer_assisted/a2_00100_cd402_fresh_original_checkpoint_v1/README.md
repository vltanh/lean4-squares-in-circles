# C d402: certified whole-original OPEN checkpoint

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
python3.12 -B -S "$delta/materialize_cd402_checkpoint.py" \
  --base "$base" --delta "$delta" --output /tmp/cd402-proof-packet
python3.12 -B -S /tmp/cd402-proof-packet/replay_portable_cd402_checkpoint.py \
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
