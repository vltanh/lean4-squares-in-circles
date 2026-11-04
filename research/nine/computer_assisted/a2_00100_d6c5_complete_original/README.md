# Complete original D6c5 proof packet

This packet excludes the entire unchanged original cell
`positive-6c5f13d07e5538df` of mask 001/00. Read `HAND_PROOF.md`,
`ROOT_PHYSICAL_REVIEW.md`, the separate independent structural review,
and `COMPLETE_TERMINAL_TABLE.md`.

The accepted prior proof excludes fifteen original I rectangles. This
packet excludes the sixteenth, I22, using a complete H2-by-4 cover,
five I-angle covers, twenty D-angle covers, thirty-seven direct D
contradictions and forty-three complete physical SAT trees. All closed
faces and contact cases are retained. It adds exactly one original-cell
closure and no whole-mask closure.

## Required published prior archive

Use the twelve ordered parts in the repository directory

```
research/nine/computer_assisted/a2_00100_d6c5_I23_complete_H_checkpoint/
```

Their concatenation is `d6c5_I23_H_supplement_v3.tar.xz`, SHA-256
`c58aedd5dd0d5efc3dbc0422703ced905f31667e77de303387ce4b377c34993d`.
The prior packet's published part manifests specify every part hash.
The current packet manifest also pins the prior source manifest and the
779-file exact core manifest.

## Fresh portable replay

Extract both archives under one new dedicated directory. The new packet
root is `d6c5_complete_original_packet`, and the prior root is
`d6c5_I23_H_supplement_v3`. With assertions enabled, run:

```
python -B -S d6c5_complete_original_packet/replay_complete_d6c5_packet.py \
  --prior d6c5_I23_H_supplement_v3 \
  --output fresh_complete_replay
```

The output directory must not already exist. Use a fresh prior extraction
too, since its unchanged composition checker preserves its earlier
reports rather than overwriting them. The wrapper authenticates every
input, permits only explicit hash-checked historical file-name bindings,
and rejects old-workspace reads. It imports no numerical producer or
optimizer. Only ordinary standard-library Python is needed; no Lean,
Lake or CI is used.

The replay repeats all new I22 arithmetic and complete unions, recomposes
the already accepted fifteen-I proof, and assembles the whole original.
It deliberately does not repeat the prior fifteen-I weighted arithmetic.
Success produces `PORTABLE_RECEIPT.json` with status
`PASS_FRESH_PORTABLE_COMPLETE_ORIGINAL_D6C5` and the full source-bound
`COMPLETE_ORIGINAL_REPLAY.json`.

`original_audits/` preserves the initial complete exact checks.
The fresh portable reports and their publication receipt are supplied
beside this archive. `INPUT_MANIFEST.json` binds all frozen arithmetic
inputs; `RELEASE_MANIFEST.json` additionally binds the physical hand proof,
complete table, independent structural review and literal accounting.
The repository publication manifest binds the archive parts, these
manifests and the fresh portable receipt.

The full current mask still requires its other unchanged original cells.
This packet is a computer-assisted exact physical hand/table proof and
does not claim human or Lean-kernel verification.
