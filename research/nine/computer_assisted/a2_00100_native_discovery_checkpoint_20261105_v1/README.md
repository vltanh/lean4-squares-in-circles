# Mask 001/00: recoverable native discovery checkpoints

**Status: partial searches, not new exclusions.** The accepted ledger remains
**222/231 original cells CLOSED, 9 OPEN**. Mask `001/00` and reversal `100/00`
remain open. No original definitions or ledger entries are changed here.

These snapshots preserve the complete saved frontiers of the ongoing searches,
including candidate exclusions and all pending alternatives. They are native
recovery material with pinned external ancestry, not standalone portable proofs.
Later search progress is deliberately not inferred from these frozen snapshots.

| Folder | Preserved scope | Nodes in saved covers | Open leaves or pending cases |
| --- | --- | ---: | ---: |
| `root_b` | Bf14 and B7c60 whole covers, plus explicitly conditional searches | 1,483 | 59 |
| `b_family` | B580 whole cover; B16a merged I21/I22 restriction; B462 complete CD8 screen and union hull seed | 820 | 27 |
| `c_family` | Cd402 and C887 whole covers; Cb882 node61 conditional cover | 678 | 69 |
| `a_family` | A-c744 component3, complete H0/H3/H4 covers | 667 | 43 |

Counts include nested conditional searches and must not be treated as disjoint
original-cell counts. Closed candidate leaves have not all received fresh
independent arithmetic replay. Each folder's source receipt specifies its exact
capture time, original identity, scope, source bindings, and external dependencies.

## Remaining immutable originals

| Family | Original IDs |
| --- | --- |
| A | `positive-c744bc031d40ee64` |
| B | `negative-f14f5bc4eafdf50d`, `negative-7c60be8b07a358e9`, `negative-462e78d2e2d8be05`, `negative-16a2fc93c8d133f0`, `negative-580db3624cf4c2e2` |
| C | `negative-887236b78100baf3`, `negative-d4021ade840b985c`, `negative-b882d8ade0cf9ea0` |

## Recovering bytes

Each folder contains independently encoded base64 parts below 1 MB, per-part
and whole-archive SHA-256 hashes, a complete archive-member inventory, and a
standard-library `restore_checkpoint.py`. The script can verify without
extracting, or extract to a new directory. The text-part format was tested by
retrieving a complete part through GitHub's text-fetch interface.

The original archive README and dependency maps describe native restoration.
No path adaptation is permission to alter a proof input: every restored source
and original anchor must match its recorded hash.

## Acceptance gates remain unchanged

Any whole original-cell claim still needs fresh independent rational replay,
an exact attachment to the immutable original domain and complete case cover,
fresh portable replay, archive/member audit, and the hand terminal table.
The nine original squares, 36 corner/pair predicates, five center cones, actual
AB/BC/EF/FG, strict weak CD, and all shared closed faces remain required.
The threshold is the strict `q < 1105/256`; a closed-Q argument must supply the
correct equality blocker.

The optional `continuation_sources` folder preserves prepared drivers and
adapters newer than the large snapshots. Its inventory identifies the exact
source bytes. Readiness or a local weighted-row check does not establish a
whole original exclusion.

No Lean, Lake, compilation, or CI was run. This commit grants **zero original
cells and zero masks** of new proof credit.
