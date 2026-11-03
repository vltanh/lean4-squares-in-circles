# Complete high-F A original and the inward-child-7 macro

## Statement and unchanged domain

The entire original cell `positive-b4a9a3bc15e37620` is empty. Together
with the 15 previously closed original cells under the same first three
path predicates, this completes the existing inward-row child 7 for
positive D and nonpositive A. This is one new original-cell closure and
one completed existing macro; it does not establish the whole A family
or the whole A2/00100 mask.

The literal original path is:

```text
angle(3,1)
angle_cut(0,0,0)
inward_row_escape(7,8,[7])
position_cut(11,1/2,1)
```

Originals use the fixed order A through I. Thus the last predicate is
the original high-F branch, including its boundary `y_F = 1/2`. All
original strict bits and marked comparisons remain those of the fixed
predicate. The proof retains nine independent physical unit squares,
all 36 original corners and all 36 original pairs. It introduces no
new path predicate, center tile, angle split, or branch node.

## 1. Whole-parent bound induction

Start with the original predicate and replay its 36 earlier coordinate
deductions. Four further rounds prove bounds on original center
coordinates, physical frame variables, and original pair differences.
All proposals in one round are derived from that round's old state;
only after all proposals are checked are their conclusions intersected
with the next state. Physical frame identities are then reapplied.

| Round | New exact bound deductions | Printed physical rows |
| --- | ---: | ---: |
| 1 | 163 | 259 |
| 2 | 122 | 227 |
| 3 | 196 | 246 |
| 4 | 210 | 289 |
| **Total before terminal** | **691** | **1,021** |

Each bound is a nonnegative rational combination of necessary physical
rows. Its residual coefficients are paid for using explicit absolute
variable bounds, and the resulting endpoint is rounded outward. The
independent replay rebuilds every printed row from its named rule and
checks every guard using only the preceding proved state.

The shared additional rules are proved in
[the original point/incircle coupling argument](ORIGINAL_POINT_INCIRCLE_FRAME_COUPLING_HAND_PROOF.md),
[the perspective and directional support argument](ORIGINAL_FRAME_PERSPECTIVE_AND_DIRECTIONAL_SUPPORT_HAND_PROOF.md),
[the support-height argument](ORIGINAL_SUPPORT_HEIGHT_PAIR_HAND_PROOF.md),
[the three-original altitude argument](THREE_ORIGINAL_ALTITUDE_CAPACITY_HAND_PROOF.md),
and [the sharp strip argument](THREE_ORIGINAL_SHARP_STRIP_CAPACITY_HAND_PROOF.md).
All remain statements about the original physical squares and frames.

## 2. The D, I, H capacity used at the terminal

The terminal's three-original altitude row concerns endpoints D and H
with middle original I. The final proved pair intervals give both
projection guards strictly positive:

\[
(c_I-c_D)\mathbin{\cdot}(c_H-c_D)
\ge \frac{1088466194997}{549755813888}>0,
\qquad
(c_H-c_I)\mathbin{\cdot}(c_H-c_D)
\ge \frac{542385989611}{274877906944}>0.
\]

The projection of I therefore lies on the segment from D to H. The
same old-state bounds give

\[
\|c_H-c_D\|\ge
\frac{558613608688841}{281474976710656},
\qquad
|\det(c_I-c_D,c_H-c_I)|\le
\frac{283048496379}{1099511627776}.
\]

Consequently the perpendicular altitude is at most

\[
\delta\le
\frac{72460415073024}{558613608688841}<\frac{7}{10}.
\]

The three-original slice theorem supplies

\[
\|c_H-c_D\|\ge
\min\left(2,\frac{280}{99}-2\delta\right)=2.
\]

Secant bounds for the two endpoint coordinate squares convert this
necessary distance into the terminal row named
`original_stronger_altitude_capacity_3_8_7`. Its guard and coefficients
are independently rebuilt from the proved state. The terminal also
uses the folded physical unit-arc chord of E on the proved interval

\[
\frac{5041}{1048576}\le |\beta_E|\le
\frac{140898281193473}{281474976710656}.
\]

This preserves E's original frame relation rather than treating its
frame coordinates as independent numbers. These two rows join the
original chain, width, disk, corner-support, and coordinate rows in a
single contradiction.

## 3. Exact sixteen-row contradiction

Write each selected necessary row as `a_j . z <= b_j`. The terminal
uses the following positive weights `w_j / 2^40`; row indices refer to
the printed source-bound terminal table, which contains every exact
coefficient and right-hand side.

| Row index | Reconstructed row rule | Weight numerator `w_j` |
| --- | --- | ---: |
| `20` | `bound_up_10` | `134766516679` |
| `31` | `bound_lo_15` | `189128087072` |
| `605` | `abs_equal_pos` | `8251442458` |
| `638` | `arc_chord` | `3132961485` |
| `787` | `abs_pos` | `372411434` |
| `964` | `width_lower` | `77068594475` |
| `1703` | `chain` | `144451852814` |
| `1706` | `chain` | `9685336136` |
| `1834` | `all_pair_cap` | `434286445` |
| `2006` | `signed_right_cap` | `283145861` |
| `2345` | `original_inset_disk_secant` | `245965985778` |
| `7360` | `contact_original_corner_support` | `475196752` |
| `7379` | `contact_original_corner_support` | `3734661894` |
| `7387` | `contact_original_corner_support` | `4479484761` |
| `13451` | `original_stronger_altitude_capacity_3_8_7` | `12023290917` |
| `18187` | `physical_folded_arc_chord_4_5041/1048576_140898281193473/281474976710656` | `265258372814` |

Let `L = sum_j (w_j/2^40) a_j` and
`B = sum_j (w_j/2^40) b_j`. Let `M_k` be the recorded absolute bound for
variable `z_k`. Exact addition of the printed rational rows gives

\[
B=-\frac{1961630627147181294711945036209187434659806440871435624021494751777}
{128686996092729110768923343620913288423208588433874123783358021369856},
\]

and the complete residual allowance is

\[
C=\sum_k M_k|L_k|
=\frac{32707013329702388664148477}
{308898325277929154914189708193955840}.
\]

Every point satisfying the selected physical rows would have
`-C <= L . z <= B`. But the exact positive reserve is

\[
-B-C=
\frac{29424459202821666528812861469463573991128076261196856167468096798703}
{1930304941390936661533850154313699326348128826508111856750370320547840}
>\frac{3}{200}>0.
\]

This is impossible. Residuals are explicitly included; no floating-point
objective, rounding tolerance, or assumption of exact numerical
cancellation enters the contradiction.

The proof has one terminal domain: the entire unchanged original
predicate. Its four rounds and terminal contain 1,037 printed rows in
all, with 691 new deductions after the 36 earlier coordinate deductions.

## 4. Completed existing macro

The frozen original register contains exactly 16 cells whose paths
start with

```text
angle(3,1)
angle_cut(0,0,0)
inward_row_escape(7,8,[7])
```

Fifteen of those cells were already closed in the immutable input
register; `positive-b4a9a3bc15e37620` was its sole remaining open cell.
The complete proof above therefore finishes that whole existing
inward-child-7 prefix, including all its earlier descendants and closed
boundary faces. No new descendant family is created by this assembly.
Other inward-row children remain separate obligations.

## 5. Certificate and independent replay

The source-bound whole-parent certificate is
`positive-b4a9a3bc15e37620.json`, with SHA-256

```text
87ca898b7670d2ebebd8bf38e850181b478dffd52400ed5e1c2af1fb6bdfa50c
```

Its earlier coordinate prefix has SHA-256

```text
8e872a55126b731a4823a32ef9773f5609c6d2760be9dd4f00c1e965b1ca0f9c
```

The canonical independent replay uses `verify_joint_original.py` and
`independent_all_rules.py`. It accepts no optimizer or producer status
as a proof. It reconstructs the original path, replays the coordinate
prefix and every bound round, checks physical frame refinements and
row guards, and recomputes the complete rational terminal sum. Fresh
replays, including the root review, returned
`PASS_COMPLETE_ORIGINAL_PARENT`.

The frozen certificate, exact row tables, independent checker, and
source bindings accompany the six-original shared-center remainder
checkpoint. The acceptance scope is one complete original cell and the
existing macro described above. The global mask ledger receives no
new mask closure from this result alone. No Lean, Lake, or CI execution
is part of this proof packet.
