# Complete inward-row child 8 from one shared original-center terminal

November 3, 2026. This proof excludes exactly the unchanged original cells
`positive-2dcf3464c0e0dafb` and `positive-3bf14a18887cabaf` of `001/00`.
They are the last two OPEN registered originals under inward-row child 8
for positive D and nonpositive A. Their complete proofs therefore finish
that existing 26-original domain, with no new case split.

The incoming fixed register has 193 CLOSED and 38 OPEN originals. This
packet contributes two distinct full-original exclusions, giving 195 CLOSED
and 36 OPEN before any independent continuation is combined. It does not
close the entire A family, `001/00`, its reversal, or another mask. The
whole-mask ledger remains 8 CLOSED and 24 OPEN. No Lean, Lake or CI.

## 1. Exact original predicates and whole-parent induction

Both paths have the unchanged three-step prefix

```text
angle(3,1)
angle_cut(0,0,0)
inward_row_escape(7,8,[8])
```

The final path step is respectively `alternate_four_escape(1,7,[1])` or
`alternate_four_escape(1,7,[2])`. Original labels are A through I in order,
with indices 0 through 8. Every original square, frame, corner, physical
pair, marked center-cone comparison, actual AB/BC/EF/FG bit and strictly
weak CD bit remains attached to the same original predicate at every
`q < Q = 1105/256`. Closed boundaries of the fixed cover are retained.

Each proof starts from that exact original path and its recorded coordinate
prefix. Six simultaneous rounds then derive bounds on the same original
coordinates, frames and pair differences. A round uses only the preceding
proved state. Every deduction is a nonnegative rational combination of
necessary physical rows; all residual coefficients are paid for by recorded
absolute variable bounds before outward rounding. Original unit-frame
identities are reapplied only after that round's bounds are installed.

| Original | Prior coordinate deductions | Whole-parent round deductions | Printed rows, including terminal |
| --- | ---: | --- | ---: |
| `positive-2dcf3464c0e0dafb` | 46 | 165, 113, 164, 193, 203, 209 | 1,612 |
| `positive-3bf14a18887cabaf` | 35 | 167, 118, 166, 195, 205, 211 | 1,727 |
| Total | 81 | 2,109 | 3,339 |

The earlier five-round states were OPEN. They are preserved with their
hashes, but are not assumptions of this proof: their complete deductions
are replayed from the original paths. One additional round closes each
entire parent. No center tile, orientation subdivision or child predicate
is introduced.

The independent physical row and arithmetic checkers are byte-identical
to the accepted original-center capacity packet. All used row guards,
source bindings, simultaneous updates, original-frame inferences and exact
weighted sums are checked again. The accepted local geometric statements
are the original frame/inset perspective, original point/incircle coupling,
owner-free directional support, and three-original strip and altitude
capacity theorems already supplied by that packet.

## 2. The common geometric terminal

The key capacity row uses the original triple A, H, I. Put
`m = c_H-c_A`, `n = c_I-c_H`, and `d = c_I-c_A`.
For both full parents, the last proved pair intervals give positive
projection guards `m·d > 0` and `n·d > 0`. The bound on the perpendicular
altitude of H above the line AI is below `7/40`, hence below
`sqrt(2)-1`. The accepted all-orientation square-plus-disk slice theorem
therefore gives the exact endpoint requirement

\[
\lVert c_I-c_A\rVert\ge 2.
\]

For completeness, the exact guarded altitude data are:

| Original | Both projection lower bounds | Endpoint distance lower bound | Determinant upper bound | Altitude upper bound |
| --- | --- | --- | --- | --- |
| `2dcf` | `132491752543/68719476736` | `555845853952787/281474976710656` | `23529888949/68719476736` | `96378425135104/555845853952787` |
| `3bf1` | `66245079179/34359738368` | `277922868931641/140737488355328` | `188242102125/549755813888` | `16063326048000/92640956310547` |

Every displayed altitude is less than `7/40`, checked as a rational
inequality. A secant upper bound on the two coordinate squares of `d`
turns this endpoint lower distance into the printed necessary linear row
`original_stronger_altitude_capacity_0_7_8`.

The terminal combines that A-H-I capacity with the physical I/G
point-incircle row, G's folded unit-frame arc, and two directional
support rows for D/I and G/I in direction `(9/41,40/41)`. The remaining
rows retain the original chain, width, cap, containment and proved
coordinate constraints. These are statements about the same originals;
no LP point is substituted for a physical square.

## 3. One small integer-weight table for both originals

Write each terminal row as `a_r · z <= b_r`, using the exact row printed
in its original certificate. The following single table works for both
original parents. Its weights are the listed positive integers divided
by `65536`. The two certificates use their own independently proved
interval endpoints, so their exact row coefficients can differ slightly;
the row rules and the integer weights are the same.

| Row | Reconstructed physical rule | Weight numerator |
| ---: | --- | ---: |
| 1 | `bound_lo_17` | 9282 |
| 2 | `abs_equal_neg` | 1965 |
| 3 | `arc_chord` | 1025 |
| 4 | `corner_support` | 1776 |
| 5 | `arc_chord` | 3279 |
| 6 | `width_lower` | 2102 |
| 7 | `abs_neg` | 67 |
| 8 | `arc_chord` | 6606 |
| 9 | `chain` | 2102 |
| 10 | `chain` | 2102 |
| 11 | `contact_original_corner_support` | 7 |
| 12 | `contact_original_corner_support` | 159 |
| 13 | `contact_original_corner_support` | 404 |
| 14 | `accepted_left_width_toll_cap` | 136 |
| 15 | `signed_left_cap` | 20 |
| 16 | `certified_difference_upper` | 1868 |
| 17 | `certified_difference_lower` | 918 |
| 18 | `original_stronger_altitude_capacity_0_7_8` | 3153 |
| 19 | `original_point_incircle_6_8_8_-1/2_-1_0_1` | 15423 |
| 20 | `physical_folded_arc_chord_G` | 10327 |
| 21 | `directional_support_gap_3_8_3_11_1_1_0` | 2636 |
| 22 | `directional_support_gap_6_8_8_11_1_1_0` | 179 |

The repeated row-rule names denote different printed original rows;
the source-bound certificates identify their indices and all exact
coefficients. In the folded G-arc row, each parent's own proved endpoint
interval is used. The complete literal rows and their order are retained
in `certificates/positive-2dcf3464c0e0dafb.json` and its `3bf1` counterpart.

Let

\[
A=\sum_r\frac{w_r}{65536}a_r,\qquad
B=\sum_r\frac{w_r}{65536}b_r,\qquad
C=\sum_k M_k|A_k|,
\]

where `|z_k| <= M_k` are the already proved absolute bounds. Necessary
rows imply `A·z <= B`, while the absolute bounds imply `A·z >= -C`.
Exact addition gives, separately for each whole parent,

\[
-B-C>\frac1{200}>0.
\]

Thus both have a contradiction. The exact reserves and full residual
vectors appear in `shared_terminal.json` and the fresh replay output
`new_reviews/shared_terminal_replay.json`. No coefficient residual is
rounded away. The original recorded duals also independently have fully
paid reserves greater than `7/1000`; the smaller common table is an
additional direct hand/table terminal.

## 4. Complete existing-domain assembly

The incoming 193/38 register has exactly 26 unchanged paths beginning
with the displayed inward-child-8 prefix. Twenty-four are already CLOSED,
and the only two OPEN IDs are the two excluded above. The packet's
`scope.json` lists all 26 exact IDs and their incoming statuses, and the
portable replay checks that literal prefix map against both frozen
registers. The already accepted baseline terminal descendants outside
the fixed unresolved register remain part of the certified full cover.

Consequently every original predicate under that existing prefix is
excluded. There are two new whole-cell proofs, two complete terminal
domains, one completed existing prefix and zero new internal case splits.
The other inward-row children remain separate original obligations.

## 5. Evidence and precise verification scope

Run `python inward_child8_checkpoint/verify_all.py` after extracting the
portable packet. Its mathematical checker uses Python's standard library
and imports no discovery producer or numerical optimizer. It reconstructs
and checks every used physical row, all six rounds for each parent,
original frame identities, both original exact terminals, the shared
small-integer table, source hashes and the complete existing-prefix map.

The unchanged historical checker uses the original 174/57 register to
identify fixed predicates. The delivered `input_current_register.json`
records their 193/38 statuses immediately before this continuation. Their
231 identifiers and paths are compared exactly; their accounting roles
are kept distinct.

This is an exact original-domain hand/table argument with independent
rational replay. No human or proof-kernel verification is claimed. No
whole-mask, positional-root or roadmap-gate count is advanced by these
two original exclusions alone.
