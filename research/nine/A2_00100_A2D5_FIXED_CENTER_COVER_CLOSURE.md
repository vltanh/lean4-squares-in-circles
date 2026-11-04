# Original A2d5: complete fixed-center-cover contradiction

November 4, 2026. This is one of the two complete original-cell proofs in the
[204 CLOSED / 27 OPEN assembly](A2_00100_A2D5_B79_FIXED_CENTER_CLOSURES.md). The original mask remains OPEN.

## Scope and unchanged original caller

This proof concerns the single original cell
`positive-2d5aba857f2f7602` in the `001/00` frontier. Its full path is

```json
[["angle",3,1],["angle_cut",[0,"0"],0],["inward_row_escape",[7,8],[2]]]
```

All nine original physical unit squares A through I remain present, with
their independent physical frames, all 36 original corners in the common
circle, and all 36 physical pairwise nonoverlap conditions. The marked
actual links, center-cone comparisons, strict weak bit, original signs,
and complete inward-row escape remain in the caller. No interior tile is
promoted to an original cell and no reflection transfers the H/I order.

The inherited exact bound record is
`global_capacity/continued/positive-2d5aba857f2f7602.json`, SHA-256
`69752cc296bae257cab29744fcdbcee3208c13fb27f9675725c7f1e87266018a`.
Its independent replay reconstructs the unchanged original path, the
coordinate prefix, and all 17 subsequent bound rounds. These rounds are
premises only through their checked nonnegative rational combinations
of independently reconstructed physical inequalities.

The new proof is a complete finite cover of this certified original
state, followed by exact interval or affine contradictions. The portable
packet is `a_2d5_fixed_cover_package`; its executable entry point is
`verify_a_fixed_cover.py`. A successful final replay closes this original
cell only. It does not close an entire mask. No Lean, Lake, or CI is used.

## 1. Complete closed rectangles

Both original extras H and I have the certified center rectangle

\[
[l_x,u_x]\times[l_y,u_y]
=\left[-\frac{152823}{131072},\frac54\right]
\times\left[-\frac{1574899}{1048576},\frac{91}{60}\right].
\]

For an interval [l,u], define its m consecutive closed pieces by

\[
J_{m,j}(l,u)=
\left[l+\frac{j}{m}(u-l),\;l+\frac{j+1}{m}(u-l)\right],
\quad 0\le j<m.
\]

Their union is exactly [l,u], including every common endpoint. First
cover I by the 16 products of its x and y quarters. Nine products have
direct physical interval contradictions. For each of the other seven,
retain every product of the two H x-halves and four H y-quarters. Thus
the complete original state is covered by 9+7·8=65 closed members.

Every rectangle is an additional guard inside the same original caller.
The fixed H/I order and all inherited difference intervals are retained
in every member. Shared boundary faces appear in adjacent rectangles,
which is harmless for an exclusion proof.

The following table is the complete coarse cover. Each H subcover has
all eight members; an interval entry means an independently reconstructed
accepted physical interval terminal, and an affine entry means a checked
positive exact reserve.

| I quarter (x,y) | Direct interval terminals | H subcover interval terminals | H subcover affine terminals |
|---|---:|---:|---:|
| (0,0) | 1 | 0 | 0 |
| (0,1) | 1 | 0 | 0 |
| (0,2) | 1 | 0 | 0 |
| (0,3) | 1 | 0 | 0 |
| (1,0) | 0 | 6 | 2 |
| (1,1) | 0 | 3 | 5 |
| (1,2) | 0 | 4 | 4 |
| (1,3) | 0 | 5 | 3 |
| (2,0) | 1 | 0 | 0 |
| (2,1) | 0 | 2 | 6 |
| (2,2) | 0 | 4 | 4 |
| (2,3) | 0 | 4 | 4 |
| (3,0) | 1 | 0 | 0 |
| (3,1) | 1 | 0 | 0 |
| (3,2) | 1 | 0 | 0 |
| (3,3) | 1 | 0 | 0 |
| Total | 9 | 28 | 28 |

## 2. Physical rows and exact bound induction

The affine variables are the existing 54 original variables: 18 center
coordinates, nine alpha components, nine signed beta components, nine
physical absolute-beta components, and nine physical inset halfwidths.
Every used row is reconstructed from its literal physical rule and the
current certified intervals. No optimizer-generated row is accepted
from its printed coefficients alone.

The accepted row families include the original corner and inset
inequalities, owned-axis and relative-support consequences, physical
frame bounds, strip and altitude capacities, point/incircle inequalities,
and the unconditional original-nine central-capacity rows. New universal
four-center energy and physical square-area moment secants are rebuilt
separately by their independent rational formulas when used. No
conditional central near-original row is promoted to an unconditional
row.

Suppose a current collection contains rows a_r·z≤b_r and the certified
absolute coordinate bounds |z_k|≤M_k. For nonnegative rational weights
w_r, write

\[
a=\sum_r w_r a_r,\qquad b=\sum_r w_r b_r.
\]

For a requested linear objective c·z, the same physical configuration
must satisfy

\[
c\cdot z\le b+\sum_k M_k|a_k-c_k|.
\]

The right side is evaluated exactly. Rounding its upper bound upward
to the declared rational grid preserves validity. The resulting bound
can therefore be intersected with the existing state. Frame inferences
are separately checked against the original unit-frame identities.
Induction proves every bound in every subsequent round within the same
fixed rectangle. There is no additional geometric subdivision.

Seven of the affine members need this induction. Their complete local
round counts and exact weighted deductions are:

| I x,y; H x,y | Local rounds | Bound deductions |
|---|---:|---:|
| 1,2; 0,0 | 1 | 75 |
| 1,3; 0,0 | 1 | 136 |
| 2,1; 0,2 | 2 | 131 |
| 2,2; 0,0 | 5 | 492 |
| 2,2; 0,1 | 2 | 180 |
| 2,2; 0,2 | 3 | 267 |
| 2,3; 0,0 | 1 | 91 |
| Total | 15 | 1372 |

The other 58 members require no new bound round. In particular, the
previously difficult (2,2;0,0) member closes on the same rectangle after
five rounds. Its 15-row final affine certificate has strictly positive
exact reserve; its full numerator and denominator are retained in the
packet.

## 3. Exact terminals

Thirty-seven members close by an accepted physical interval terminal:
either the propagated original center interval is empty, or all four
necessary original inset-separation alternatives of a physical pair
are impossible. The independent checker reconstructs that same physical
terminal from the original path and guarded state; a text label alone
is not a proof.

For each of the other 28 members, the final nonnegative weighted sum
has exact reserve

\[
\eta=-b-\sum_k M_k|a_k|>0.
\]

The assumed physical configuration would imply a·z≤b, while its
absolute bounds imply a·z≥−Σ_k M_k|a_k|=b+η, a contradiction. All 28
computed reserves exceed the exact rational lower bound 1/1024. The
independent replay checks every weight, reconstructed row, residual
coefficient, absolute bound, and reserve in rational arithmetic.

## 4. Whole-original assembly and reproducibility

The final assembly first checks the byte-frozen source bindings and
freshly replays the full original bound state. It then proves every
listed rectangle and verifies the exact cover: every one of the 16
I quarter products must have either one direct terminal or all eight
H half-by-quarter terminals. Duplicate or missing members fail the
check. Every member must carry the same unchanged original path and
the same certified parent source.

The verifier imports independent physical arithmetic only. Numerical
solvers and producer modules are absent from its import graph. Historical
absolute paths are resolved to explicitly bound bytes inside the packet,
and the strict replay rejects workspace reads or imports outside the
packet. The
portable report records the original path, all 65 terminal members,
source bindings, local deductions, and the complete coverage check.

The computer-assisted search found the nonnegative weights and useful
bounds. Their numerical discovery history, including a separate
numerical pose-graph UNSAT result, is not a premise of this proof.
The complete fixed cover and exact rational contradictions suffice.
