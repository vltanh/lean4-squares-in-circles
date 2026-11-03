# C60b: complete fixed H-center cover of one original cell

This certificate closes exactly the unchanged original cell
`negative-60b1043c8c722dd5` of mask `001/00`. It adds one original-cell closure
to the incoming ledger: **192/231 becomes 193/231, with 38 originals still
OPEN**. The whole mask remains OPEN.

## 1. Exact original scope

The complete recorded path is

```json
[
  ["angle", 3, 0],
  ["angle_cut", [0, "0"], 1],
  ["alternate_four_escape", [1, 7], [7]],
  ["alternate_four_escape", [1, 8], [6]]
]
```

The identifier and path are unchanged. The original packing predicate,
circle threshold `q < 1105/256`, all nine original squares, all original
corner-containment and pair-disjointness conditions, and the original
normalizations are retained. In particular, H is original index 7 and I is
original index 8; the condition `x_H <= x_I` is retained without exchanging
their labels.

The three-step prefix ending at H-alternate child 7 contains **29 fixed
originals**. After this closure it still contains the OPEN originals
`negative-6181e7007bf6714b`, `negative-95371f658da581d0`, and
`negative-573078fc944ce553`. This note does not close that broader prefix,
the C family, or another mask.

## 2. Replayed canonical parent and complete center cover

The source is the complete canonical v3 parent certificate
`negative-60b1043c8c722dd5.json`, schema
`whole_parent_sharp_altitude_support_frame_pointdisk_v3`, SHA256
`cce07c27965d6b507b4365b47003a961f57c43d01008eea13b167cc4bfbdd643`.

Its 31 inherited coordinate deductions and all 457 deductions in five v3
rounds are replayed from the original path. Its declared final arrays are
checked against the reconstructed state before they are used. The proved
H-center rectangle is

\[
X_H=\left[\frac{44173}{131072},\frac{750011}{1048576}\right],\qquad
Y_H=\left[-\frac{62219}{131072},\frac{507815}{524288}\right].
\]

Write these intervals as \([a,b]\) and \([c,d]\). For \(0\le i,j<8\), define

\[
T_{8i+j}=
\left[a+\frac{i(b-a)}8,a+\frac{(i+1)(b-a)}8\right]
\times
\left[c+\frac{j(d-c)}8,c+\frac{(j+1)(d-c)}8\right].
\]

These are closed rectangles. Their union is exactly the complete proved
H-center rectangle, including every shared face. Every other original
variable retains its complete proved parent domain on each subcase. This
is a cover of possible original centers, not a test of finitely many
sampled placements.

The static pass left tiles `[16,17,24]` pending. The proof uses the full
Cartesian rectangle containing them:

\[
R=T_{16}\cup T_{17}\cup T_{24}\cup T_{25}
=\left[\frac{1810163}{4194304},\frac{1103395}{2097152}\right]
\times
\left[-\frac{62219}{131072},-\frac{238813}{2097152}\right].
\]

Tile 25 is included in this complete rectangle even though its static
certificate was already available. It is **not counted again** among the
outside static domains. The final cover therefore has exactly **60 outside
static rectangles plus one complete rectangle R**, accounting for all 64
original grid tiles.

## 3. Exact contradictions on every covered domain

For each of the 60 outside rectangles, the packet contains an exact
positive-reserve linear certificate made only from necessary physical
rows for the same nine original squares. The checker independently
reconstructs every used row and its guards.

The arithmetic rule is the following. If the necessary rows are
\(A_r\cdot v\le b_r\), choose printed rational weights \(w_r\ge0\), and
let \(A=\sum_r w_rA_r\), \(B=\sum_r w_rb_r\). The proved absolute
variable bounds \(|v_k|\le M_k\) imply a contradiction whenever

\[
\varepsilon=-B-\sum_k M_k|A_k|>0.
\]

All weights, coefficients, residual corrections, and reserves are checked
as exact rationals. An optimizer status or floating-point margin is not a
proof premise.

On the complete rectangle R, one additional simultaneous bound round
proves 172 deductions. Every round retains and intersects the canonical
parent's pair-difference bounds. A 22-row terminal then has exact reserve

\[
\varepsilon_R=
\frac{5283512421120557506042076705291435193452955731}
{731236325925402703819613889626112000000000000000}
>\frac7{1000}.
\]

Thus the entire rectangle R is impossible. No further subdivision of it
or of the fixed grid is used. The least positive terminal reserve across
the 60 outside rectangles and R is greater than \(1/1000\).

Combining the 60 static contradictions with the complete contradiction on
R excludes every H-center allowed by the replayed canonical parent.
Consequently this one original cell is closed.

## 4. Verification record and adapter scope

The complete exact replay checks:

| Part | Bound deductions | Printed row occurrences |
| --- | ---: | ---: |
| Inherited coordinate prefix | 31 | Replayed in the inherited prefix |
| Complete canonical v3 parent, five rounds | 457 | 1,241 |
| Sixty outside static terminals | 0 | 336 |
| Complete rectangle R, one bound round | 172 | 216 |
| Rectangle R terminal | 0 | 22 |

The parent and cover tables contain **1,815 checked printed row
occurrences**. There are 31 inherited deductions plus 629 new deductions,
61 terminal domains, and all 64 grid tiles are accounted for.

The separate adapter `verify_fixed_h_canonical_v3_parent.py` is derived
from the immutable accepted `verify_fixed_h_parent.py`. Its only changes
are explicit canonical-v3 source/schema checks, report metadata, and CLI
defaults. Physical row reconstruction, exact arithmetic, bound induction,
the original H target, and complete Cartesian coverage are unchanged.

The adapter's SHA256 is
`417dd8fb48479e8d3c278f31f6d473cd61184b961b2cd44f4b4ea2697ca4f17a`;
the full diff's SHA256 is
`588584b13b0ec8dd3209e58c91c931e96d38a46d5349b188b1bab8c732ed59bd`.
The complete rectangle certificate's SHA256 is
`cb98871b0b58c45d276936030786fda8a924a451684cabeb0be3ebc6d06817da`.
Independent replay and a separate fresh root replay both returned
`PASS_COMPLETE_ORIGINAL_PARENT` with the totals above.

This is an exact physical hand/table certificate. No Lean, Lake, or CI
execution is claimed. The separate 13-parent C/D screen contributes no
closure credit for its partial tile certificates; C60b is the sole
complete original produced by that screen.
