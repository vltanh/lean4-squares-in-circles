# C-family exact partial checkpoint: 224/231 unchanged

This checkpoint preserves four complete partial covers of three unchanged
originals in mask `001/00`. Every cover has a matching fresh independent
rational replay, and every unresolved alternative remains explicit. It grants
**zero original-cell and zero mask credit**. The fixed register remains
**224 CLOSED / 7 OPEN**, and the mask ledger remains **8 CLOSED / 24 OPEN**.

| Cover | Immutable original | Processed | Excluded leaves | OPEN |
| --- | --- | ---: | ---: | ---: |
| C887 main | `negative-887236b78100baf3` | 259 | 135 | 43 |
| Cd402 opposite-boundary continuation | `negative-d4021ade840b985c` | 507 | 351 | 13 |
| C887 scalar alternative | `negative-887236b78100baf3` | 189 | 115 | 24 |
| Cb882 two ABID neighborhoods | `negative-b882d8ade0cf9ea0` | 138 | 67 | 25 |

The two C887 covers overlap and are alternatives; their counts cannot be
added. Processed counts omit pending graph domains. The C887 scalar cover
has 24 pending domains, and the Cb882 cover has 13 pending plus 12 stopped
domains. Pending and stopped both mean OPEN.

## Physical scope of the preserved exclusions

The C887 main cover retains the completed scalar component at domain 162
and the accepted sharp central neighborhood at domain 201, including every
outer angle complement. Its deep-cylinder helper has no actual terminal use.

The Cd402 continuation covers domain 43 by six closed adjacent-height cuts
on original row A,H,I,D. The central domain 505 has total height variation
at most `3/16 < 23/100`; the incoming state proves the original horizontal
orders and opposite A/D signs. The accepted full-angle opposite-endpoint
theorem, its complete scalar certificate, and the original strict-CD equality
blocker are freshly checked. One outer domain, 503, closes by an ordinary
exact positive reserve. Five outer complements and eight old stopped
domains remain OPEN.

The Cb882 continuation applies the same quantified theorem to the literal
original row A,B,I,D at central domains 179 and 193. Original H remains
present with all its original predicates. One caller requires an additional
closed B/I horizontal-order split; both callers retain all six height-cut
complements. The fresh report checks both actual ABID terminal uses and
the unchanged strict-CD equality blocker.

All reports retain all nine unit squares, 36 original corners and pairs,
five marked cones, actual AB/BC/EF/FG links, strictly weak CD, original H/I
frames, complete separator-owner alternatives, and closed shared faces.
The claim remains strict `q < Q = 1105/256`. No global closed-Q theorem or
equality classification follows from these partial covers.

## Exact reports, archive and recovery

The [published checkpoint](computer_assisted/a2_00100_c_finite_frontiers_v2/README.md)
contains the four fresh native reports, verbatim and transported manifests,
hand/source review evidence, dependency maps, and 15 hash-checked archive
parts. The 123,751,936-byte archive has SHA-256
`60c5fef27b403c0312665b4d1e361f671d4fff0cc30aeda92a12de8c76f9ec2f`.
Its audit streamed and rehashed all 1,394 regular members against the
1,393-file inventory and inventory file itself.

This is a native checkpoint with explicit published dependencies. Exactly
994 external input paths map to exact members of four published archives;
all 1,954 members of those archives and their Git blobs were independently
rehashed. Six derived outputs are included instead of remaining external.
The [recovery handoff](computer_assisted/a2_00100_c_finite_frontiers_v2/C_FINITE_FRONTIERS_V2_PUBLICATION_HANDOFF.md)
provides paths, hashes, scoped recovery rules and native replay commands.
The freezer and archive verifier check transport and complete graphs; they
do not repeat arithmetic. A standalone cold arithmetic replay of the
extracted checkpoint is not claimed.

Later Cb882 and C887 continuations are separate from this frozen snapshot.
No Lean, Lake, compilation or CI was run. Continue the seven remaining
whole originals under the current bounded-work directive.
