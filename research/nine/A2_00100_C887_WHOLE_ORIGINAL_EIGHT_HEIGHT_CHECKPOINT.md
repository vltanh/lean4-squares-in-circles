# C887: whole-original eight-height reduction and first exact exclusion

November 4, 2026. This is a complete reduction with a partial exclusion table.
The original remains OPEN. There is no new original-cell, mask, positional-root
or roadmap-gate credit.

## Unchanged physical caller

The cell is `negative-887236b78100baf3`, with literal original path

```json
[["angle",3,0],["angle_cut",[0,"0"],1],["alternate_four_escape",[1,7],[1]]]
```

All nine independent unit-square frames, 36 original corners, 36 physical
pair constraints, five marked cone comparisons, actual AB/BC/EF/FG and
strictly weak CD remain in force. The corner disk relaxation is the closed
disk of squared radius `Q=1105/256`. No selected-seven model replaces this
caller, and no I-position or H-position restriction is imposed.

The exact whole-original wrapper has SHA-256
`9a5c4af1e23964ee661e4e1ae427265a29303b2a6f6bd5a65c5ece14177040a3`.
Its unchanged v3 parent has SHA-256
`d7ad68039cefde5580f63db10002a6dcb436381ee20ac04e9955fb5f127a84f0`.
The wrapper has zero rounds and exactly the full original parent state.
Fresh replay reconstructs the 29 earlier coordinate deductions, followed by
364 whole-parent deductions in five rounds. That replay is an OPEN-state
certificate, not an original-cell exclusion.

## Whole-original theorem attachment

The replayed parent proves

| Required quantity | Certified interval |
|---|---|
| `x_H-x_A` | `[26355/1048576,83/30]` |
| `x_I-x_H` | `[0,2785067/1048576]` |
| `x_D-x_I` | `[434432029724121/5000000000000000,3064161/1048576]` |
| original A slope | `[0,21144313723523/140737488355328]` |
| original D slope | `[-1,0]` |

Consequently AHID is weakly ordered from left to right and the two endpoint
slopes have opposite signs. The full-angle opposite-endpoint four-row
theorem applies to these four original squares and the actual original EFG
chain. It excludes total height variation

`V=|y_H-y_A|+|y_I-y_H|+|y_D-y_I| <= 23/100`.

Its equality analysis is essential: equality in its closed-Q estimate would
force the selected row to be aligned, and the original AB/BC links then
force the remaining main alignment that contradicts strictly weak CD.
Endpoint zero slopes and the middle horizontal equality are retained.
The theorem needs no small-angle or shoulder-height guards.

The packet includes and freshly replays the entire independent theorem:
80 sign/owner domains, 1,405 finite leaves, 878,125 exact integer Bernstein
checks and no frontier. Its aligned equality faces are supplied by the
corresponding hand proof. The theorem's full caller and equality conditions
are checked before the following finite cover is used.

## Complete eight-member closed cover

Write `d1=y_H-y_A`, `d2=y_I-y_H`, `d3=y_D-y_I`. The maximum of
`e1*d1+e2*d2+e3*d3` over all eight independent signs is exactly `V`.
Since the preceding theorem excludes `V<=23/100`, every surviving physical
state lies in at least one of the eight closed domains

`e1*d1+e2*d2+e3*d3 >= 23/100`.

The eight children restrict the same whole original independently. No child
inherits complements of earlier siblings. Equality faces may overlap and
are never removed. The table below uses lexicographic sign order.

| Branch | Signs `(e1,e2,e3)` | Completed local rounds | Exact bound deductions | Current result |
|---:|---|---:|---:|---|
| 0 | `(-1, -1, -1)` | 3 | 464 | OPEN: certified bounds only |
| 1 | `(-1, -1, 1)` | 3 | 229 | OPEN: certified bounds only |
| 2 | `(-1, 1, -1)` | 3 | 228 | OPEN: certified bounds only |
| 3 | `(-1, 1, 1)` | 3 | 230 | OPEN: certified bounds only |
| 4 | `(1, -1, -1)` | 3 | 226 | OPEN: certified bounds only |
| 5 | `(1, -1, 1)` | 3 | 235 | OPEN: certified bounds only |
| 6 | `(1, 1, -1)` | 3 | 225 | OPEN: certified bounds only |
| 7 | `(1, 1, 1)` | 1 | 321 | EXCLUDED: positive rational reserve |

The table contains 22 completed local rounds and 2,158 exact deductions.
The verifier reconstructs 3,159 premise-row occurrences and 22 terminal
rows. The common original prefix is counted once, not once per child.

## Hand reconstruction of the terminal

For branch 7, the added physical restriction is `y_D-y_A>=23/100`.
Every printed row is independently reconstructed from the unchanged
original geometric constraints and that one restriction. The saved
nonnegative rational multipliers give a weighted inequality `c dot z<=b`.
The same replay proves exact absolute bounds `|z_k|<=M_k`, so feasibility
would imply

`0 <= b + sum_k M_k*|c_k|`.

The complete table in `data_recovered/branch_07.json` instead gives the
strict positive reserve `-b-sum_k M_k*|c_k|` equal to

```
15869209246401873521914324377755564069017227814101604545385221671/20527871390165956302177374641535837989744498811549553051054794342400
```

This excludes all of branch 7, including its closed height face. The other
seven branches remain OPEN; their valid bound inductions are preserved for
continuation and carry no exclusion credit.

## Independent recovery and reproducibility

An identical numerical search had already finished in a concurrent
workspace. The duplicate local search was stopped after its first finished
three-round record. Only completed immutable foreign records were copied;
their workspace and active processes were untouched.

The raw bytes are preserved in `raw_recovered/`. A lossless adapter changes
only schema, scope, conditional-row metadata and source provenance to fit
the independently written component checker. It preserves every path,
round, final state, terminal and arithmetic field. The independent
translation review reconstructs all eight converted files byte for byte and
checks 15 damaged controls. Separate reviews check the whole-parent loader,
eight-member union, module confinement, source binding and OPEN semantics.

Run `python -B -S verify_checkpoint.py` in the extracted packet. The wrapper
hash-checks every frozen input, freshly replays the opposite-endpoint
theorem, replays the full original ancestor and all eight child records,
then checks all input hashes again. It imports no numerical solver or
discovery row generator. Only the Python standard library is needed.

The earlier direct screen and older restricted I21 checkpoint remain
historical evidence. They are not the entry point of this whole-original
checkpoint and are not promoted to complete original-cell proofs.

## Fixed accounting

The same 231 original cells in `001/00` remain **217 CLOSED / 14 OPEN**.
The same 32 masks remain **8 CLOSED / 24 OPEN**. The 7,915 positional roots
and 15 roadmap IDs are unchanged. The whole `001/00` mask, its reversal,
A.2, unrestricted lower bound and global equality classification remain
OPEN. No Lean, Lake or CI was run; no human or kernel verification is claimed.

## Committed evidence

[Complete portable packet](computer_assisted/a2_00100_c887_whole_eight_checkpoint.tar.xz) ·
[Archive, source and member hashes](computer_assisted/a2_00100_c887_whole_eight_manifest.json) ·
[Root exact replay](computer_assisted/a2_00100_c887_whole_eight_root_replay.json).

Extract the archive and run `python -B -S verify_checkpoint.py` from
`c887_whole_eight_checkpoint_package`. All 482 archive members were checked
against their original bytes, including 162 exact duplicates represented
by safe internal hardlinks. The packet has 479 frozen inputs and contains
the independent source, scope, cover and lossless-translation reviews.
