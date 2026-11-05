# A-c744 I64: fresh exact native replay

The newly executed native gate passes seven exact rounds, 813 deductions and
1,941 printed premises. It reconstructs both I64 row occurrences and all 131
universal center literals. A fresh separate scalar run checks 28 domains,
121 leaves and 15,125 exact Bernstein coefficients, with no frontier.

The certificate retains one OPEN narrowed domain: the original A-c744 old
component 3 intersected with the I64 height condition. The stronger source
was recovered byte-for-byte; this is a new replay, not the lost earlier receipt.
Four old source-provider proofs are explicitly reused after complete identity
checks. Their older A1 arithmetic is not described as freshly repeated.

`FRESH_REPLAY_SUMMARY.json` gives a compact view of the result. The complete
raw report, recovered source record, all new gate sources, controls, execution
receipt and exact dependency map are inside the 95-member archive. The root
checked every included byte, all 1,146 mapped native dependencies, and the 36
repository dependencies against a published commit. Fresh archive extraction
preserved all members. The archive contains 14,353,868 uncompressed file bytes.

Extract into a new directory with:

```sh
python -B -S native_checkpoint_transport_v2.py extract \
  i64_fresh_gate_native_v1.tar.xz ARCHIVE_MANIFEST.json /absolute/new/output
```

Extraction checks bytes only and installs no native aliases. Follow
`NATIVE_GATE_README.md` and `DEPENDENCIES.json` for the explicit native replay
dependencies. This is not a new cold replay of every historical source proof.

Whole-original endpoint transport is separate and is not installed here.
No original or mask closes in this checkpoint. The missing 235-node consumer
and its receipt are not recreated. No numerical solve, Lean, Lake or CI.
