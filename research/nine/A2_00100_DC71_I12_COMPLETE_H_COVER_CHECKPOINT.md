# Dc71: complete original I12 rectangle by its eight H members

## Result and exact scope

All eight closed H rectangles over the fixed I12 rectangle of original
`positive-c71dc2feef1abb0b` are excluded. This closes exactly one member of
the unchanged 4 by 4 I cover. It does not close the complete original or
the mask, and receives zero original-cell or mask credit.

The original path is `angle(3,1); angle_cut([0,0],1);
alternate_four_escape([1,7],[2])`. The whole-original zero-round wrapper
has SHA256 `3d5c6def24cd920103c2a26b81d4f898e135cda0b125a2eea87a8880fee840fa`.
It retains all nine independent original unit frames, every corner and
pair constraint, the original marked cones and strictly weak C-D. Closed
radius Q=1105/256 is only a necessary relaxation of the strict caller.
The original I rectangle is

$$x_I\in[-3107647/4194304,-162069/2097152],\qquad y_I\in[0,91/120].$$

The six-round I parent has SHA256
`5f47f999555be6ac45b0becce96c06ef4c31e3e8f032b33bdbed0cfaf3a01719`.
It is independently replayed from the same original path, retaining all
Cartesian, frame, scalar, difference and correlated-diagonal bounds.
Its proved H rectangle is

$$x_H\in[-1472789/1048576,-162069/2097152],$$
$$y_H\in[-741275/524288,213174581573171/140737488355328].$$

Divide its x interval into two equal closed intervals and its y interval
into four equal closed intervals. Their eight products cover the entire
necessary H rectangle. Each shared face is retained in both adjacent
members; no assumed positive clearance removes a face. Every other
proved bound is retained in every member. The table lists the complete
cover with zero-based H indices.

## Complete literal table

| H member | Exact terminal | Local rounds | Deductions | Premise rows | Terminal rows |
|---|---|---:|---:|---:|---:|
| 00 | Strict difference contradiction after a finished prefix | 1 | 331 | 271 | 0 |
| 01 | Positive rational reserve | 0 | 0 | 0 | 3 |
| 02 | Initial strict difference contradiction | 0 | 0 | 0 | 0 |
| 03 | Empty propagated original-center interval | 0 | 0 | 0 | 0 |
| 10 | Empty correlated-diagonal interval | 0 | 0 | 0 | 0 |
| 11 | Positive rational reserve | 2 | 332 | 475 | 12 |
| 12 | Positive rational reserve | 0 | 0 | 0 | 7 |
| 13 | Positive rational reserve | 5 | 749 | 1167 | 3 |

The local total is eight bound rounds, 1,412 deductions, 1,913 premise
rows and 25 terminal rows. The common six-round I ancestor contributes
522 deductions and 1,162 premise rows once; its whole-original ancestors
are retained and replayed separately. Repeated replay is not counted as
additional mathematical work. The full exact rational multipliers,
residual payments, interval witnesses and certificate hashes are in
`I12_COVER_TABLE.json` and the unchanged raw records.

## Why each terminal is valid

In the four positive-reserve members, every used affine row is rebuilt
from the physical originals. The proof forms a nonnegative rational
combination and pays its entire residual coefficient vector using proved
absolute variable bounds. The remaining positive reserve contradicts
the member. Intermediate bound deductions use the same exact procedure,
followed by exact bound intersections and original unit-frame identities.

In member 03, physical center propagation produces an interval with
lower endpoint above its upper endpoint. In member 10, the original
B/H correlated-diagonal interval has lower endpoint
`9241969230617/140737488355328` and upper endpoint zero. Both contradictions
are strictly positive, so touching squares and touching grid faces are
not lost. These are reconstructed interval contradictions, not accepted
numerical statuses or exception messages.

In members 00 and 02, the original physical center bounds produce a
necessary signed Cartesian pair-difference interval. Intersect it with
the independently proved interval of the same pair and coordinate.
The lower endpoint exceeds the upper endpoint, giving a strict exact
contradiction. The retained witness records display both original
intervals and their positive gap.

Member 00's discovery process stopped while preparing its next round.
The proof uses only its fully printed and replayed first round: all 331
deductions, the derived original frames and the final complete state.
The separate physical difference reconstruction then gives the B/H
horizontal gap `53005578069/35184372088832`. No unfinished next round,
missing final test or numerical exception is used as a premise. The raw
interrupted record remains unchanged.

## Physical premises and reproducibility

The packet retains the complete geometric proof of the three-square
center-energy bound 7/2 and the independent exact row-conversion proof.
The wrapper freshly runs both geometric evaluators and all 1,877 row
identities before the local proofs. No numerical optimizer is imported
by any exact checker.

Run `python -B -S verify_dc71_I12_complete_H_cover.py` from this extracted
packet. It verifies the frozen inputs, freshly reconstructs the initial
H difference contradictions, replays the finished member-00 prefix and
its terminal, replays the other six members, and compares every literal
table entry and exact rectangle endpoint. The common original path,
prefix hash, six-round parent, physical H rectangle and all eight closed
indices are checked before assembly. Every frozen input is rehashed at
the end, and all imported project code is confined to the packet.

The permitted conclusion is the complete exclusion of this original I12
rectangle. The rest of the unchanged original and its mask remain OPEN.
No Lean, Lake or CI execution, human review or kernel verification is
claimed.

## Committed portable evidence

[Archive parts, exact hashes and reviews](computer_assisted/a2_00100_dc71_I12_complete_H_manifest.json) ·
[Fresh root exact replay](computer_assisted/a2_00100_dc71_I12_complete_H_root_replay.json).

Concatenate the two archive parts in their declared order, extract the xz
tar archive, and run `python -B -S verify_dc71_I12_complete_H_cover.py` from
`dc71_I12_complete_H_checkpoint`. The archive contains 392 frozen inputs,
four separate independent review files and all selected fresh outputs.
Every one of its 402 members was byte-checked, including 116 safe internal
hardlinks for exact duplicates. Both the complete outer assembly and the
finished-prefix difference primitive passed independent source reviews.

Together with the separately committed nine direct I exclusions, this
completes ten of the original sixteen I rectangles. The other six I
rectangles remain separate obligations. No original-cell, mask, positional
root or roadmap closure follows from this checkpoint.
