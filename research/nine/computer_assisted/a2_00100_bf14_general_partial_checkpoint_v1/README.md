# Bf14 exact partial checkpoint

This packet preserves a complete cover of the registered original
`negative-f14f5bc4eafdf50d`. It **does not close that original**: 15 leaves remain
OPEN. It contributes zero new original cells and zero masks. The fixed ledger
remains 222/231 closed, with 9 original cells open.

The frozen tree has 349 nodes, 221 excluded leaves and 15 open leaves. Its 113
complete internal covers comprise 52 four-way inset covers, 58 two-way angle
covers and 3 eight-way physical separation covers. All shared closed faces are
retained. Every original square, corner, pair predicate, center cone and actual
AB/BC/EF/FG link remains in the model; the strict weak CD condition is retained.
All 231 original definitions were compared against the frozen original register.

## Exact replay

The native full-domain replay and a fresh portable replay both passed. The
portable checker uses the Python standard library, forbids reads outside its
dedicated packet/prior workspace, checks every bound and complete cover, and
rehashes every input at completion. It does not import numerical discovery
modules. No Lean, Lake, compilation or CI was run.

The replay checked 143 local bound rounds, 27,688 deductions and 95,238 printed
row occurrences. These include 12,990 universal center disk rows, 166 incircle
distance chord rows, 200 narrow rotating center cone rows and 59 general center
cone rows. The hand proofs and independent literal decoders are included in the
archive. A successful partial replay establishes the exclusions and the retained
OPEN remainder; it is not a proof that the whole original is impossible.

## Reproduction

Concatenate the three archive parts in `ARCHIVE_MANIFEST.json` order and verify
the resulting archive SHA256:

`773d06284bc4a96815ee948c714bae563a661c93c29098d6b2a07c03345ea5de`.

Extract `f14_general_partial_packet_v1` alongside the prior directory
`b16a_I32_complete_H_checkpoint`. The prior is the already published archive
identified completely by `PUBLISHED_PRIOR.json`; its archive SHA256 is
`c6e8dfc170a3d88366a6cd6f0955302ca5f664c626790ca91387f84c42502cb6`.
Use a fresh output directory in the same dedicated workspace:

```sh
python -B -S f14_general_partial_packet_v1/code/replay_registered_b_general_cone_packet.py \
  --prior b16a_I32_complete_H_checkpoint \
  --output fresh_bf14_partial_replay
```

Expected result: `PASS_PORTABLE_OPEN_PROTOTYPE`, `complete: false`,
`whole_original_proved: false`, 15 OPEN leaves and zero ledger credit.

The archive was read back after compression: all 732 regular members matched
their frozen hashes. `COMPLETE_TERMINAL_TABLE.md` lists the entire leaf frontier,
including its OPEN entries. `ORIGINAL_PROOF.json` records the unchanged original
path and the exact attachment to the fixed register. The word “complete” in the
table filename refers to listing the entire frontier, not to proof completion.

The active search continues from a later retained checkpoint. This publication
banks the independently verified work without changing the acceptance gate for
a future whole-original closure.
