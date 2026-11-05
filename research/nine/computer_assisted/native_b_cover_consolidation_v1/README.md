# Consolidate native B discovery covers with bounded memory

This change joins saved conditional search covers into their corresponding
whole-original covers. It avoids running separate numerical searches for
already partitioned parts of the same original and avoids loading several
complete copies of large proof records into memory.

**No original-cell or mask exclusion is claimed.** These are discovery
assemblies. The accepted mask count remains 222/231 originals closed, 9 open.

| Assembly | Exact state join | Resulting nodes | Open leaves at assembly |
| --- | --- | ---: | ---: |
| B7 node260 conditional | Positive-half root into local node2 | 459 | 1 |
| Whole B7c60 original | Node260 conditional root into original node260 | 895 | 14 |
| Whole Bf14 original | Future-node209 conditional root into original node209 | 683 | 19 |

The assembler retains the original whole-tree parent, original root state,
and every pending case outside the replaced subtree. Each replacement starts
at exactly the old node's final state. All incoming case alternatives remain
present, including OPEN leaves. Reindexing changes only tree references and
depths; the stored proof records are read one at a time. The replaced root
record concatenates the old prefix rounds with the incoming root rounds.

For a complete-case tree, replacing one node's continuation by another complete
cover of its exact final state preserves the remaining proof obligations.
This statement concerns composition of covers. The validity of every numerical
bound and exclusion still requires the independent arithmetic checker.

## Checks performed

The assembler checked input hashes, exact state equality at all three joins,
root identity, complete graph connectivity, and complete stored child counts.
The separate `audit_b_case_slots.py` then checked all expected case choices,
node/record initial-state identity, hashes, parent/depth relations, and candidate
status propagation for both consolidated whole trees:

| Whole cover | Proxy unions | SAT unions | Angle unions | Difference unions |
| --- | ---: | ---: | ---: | ---: |
| B7c60 | 32 | 3 | 258 | 113 |
| Bf14 | 67 | 15 | 147 | 0 |

These are structural checks, **not arithmetic or original-domain replay**.
`JOIN_STATES.json` records the exact common states and native input hashes.
The native input trees remain separate recovery material; this small packet is
not a standalone proof archive.

## Continuation and acceptance

The two whole trees continue with the already checked relative-support chord
family. B7 uses one bound round on difference children; the existing full case
covers and shared closed faces are preserved. The former separate conditional
searches were stopped only after coherent, hash-verified snapshots existed.

`continue_whole_b_after_batch.py` permits one ordinary replacement batch after
the current batch finishes. It starts no additional concurrent numerical job.
Only a complete whole-original candidate triggers the independent rational
checker. A successful native result still requires fresh portable replay,
archive/member audit, the hand terminal table, and a fresh ledger review.

All nine original frames, 36 corner/pair predicates, five cones, actual
AB/BC/EF/FG, strict weak CD, immutable original IDs/paths, and closed split
faces remain obligations. The strict threshold remains `q < 1105/256`.
No Lean, Lake, compilation, or CI was run. No ledger was changed.
