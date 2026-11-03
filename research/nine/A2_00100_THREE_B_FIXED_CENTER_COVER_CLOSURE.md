# Three complete B originals from fixed center covers

## Statement and scope

The three original A2/00100 cells listed below are empty. Each proof retains
all nine physical unit squares, their original independent frames, every
corner constraint, and all inherited pair and routing predicates. The proof
covers each entire original cell, including its closed equality faces.

| Original cell | Existing F-height side | Existing H escape | Existing I escape |
| --- | --- | --- | --- |
| `negative-f92d74e712afa6be` | `y_F <= 1/2` | 6 | 5 |
| `negative-b8e4f47ec1258e16` | `y_F >= 1/2` | 6 | 4 |
| `negative-1de449e714cf90dd` | `y_F >= 1/2` | 6 | 5 |

All three share the original path predicates `angle(3,0)` and
`angle_cut(0,0,0)`, namely the existing nonpositive D and A angle sectors.
The complete literal paths are recorded in their certificates and checked
against their original identifiers. The escape numbers in the table refer
to the original routing definition, not to newly selected separation
branches.

The first and third rows together remove the F-height restriction from
the shared H-escape-6, I-escape-5 routing: the two closed halfspaces
`y_F <= 1/2` and `y_F >= 1/2` cover every possible height, including their
common face. This is a complete two-cell macro closure. This document
does not declare the whole A2/00100 mask, another routing, or all masks
closed.

## 1. Whole-parent premises

First derive the complete source-bound parent state for each original.
The source-bound induction is part of the proof; its final interval arrays
are not independent assumptions. Every bound proposal is an exact
nonnegative combination of reconstructed physical inequalities, with an
explicit absolute-variable remainder.

| Original suffix | Earlier coordinate deductions | New whole-parent deductions | Whole-parent printed rows |
| --- | ---: | ---: | ---: |
| `f92d74e712afa6be` | 31 | 224 | 651 |
| `b8e4f47ec1258e16` | 38 | 521 | 945 |
| `1de449e714cf90dd` | 39 | 527 | 976 |

These parent states alone are open. Their only use below is as proved
premises for the finite center cover. The independently replayed parent
interface returns actual rational intervals for all positions, frame
variables, and relational differences, together with the original path
and separation choices. A saved success report is not used as a premise.

Write the proved rectangle for the ninth original center as
`I_x in [a,b]`, `I_y in [c,d]`. Its exact endpoints are:

| Original suffix | `[a,b]` | `[c,d]` |
| --- | --- | --- |
| `f92d74e712afa6be` | `[-245887/1048576, 5/4]` | `[-91/60, 59887/1048576]` |
| `b8e4f47ec1258e16` | `[-25333/131072, 5/4]` | `[-91/60, 97757/65536]` |
| `1de449e714cf90dd` | `[-25333/131072, 5/4]` | `[-91/60, 135983/1048576]` |

Every other variable retains its full proved parent range. No numerical
point, selected frame, or guessed center is substituted for a physical
square.

## 2. A fixed rational cover, with every face retained

For `0 <= p,q < 8`, define the closed tile

\[
T_{8p+q}=
\left[a+\frac{p(b-a)}8,\ a+\frac{(p+1)(b-a)}8\right]
\times
\left[c+\frac{q(d-c)}8,\ c+\frac{(q+1)(d-c)}8\right].
\]

These 64 closed rectangles cover the entire parent rectangle. Adjacent
tiles share their exact rational boundary, so no open seam or rounding
gap occurs. The fixed grid was declared before the per-tile tests. There
are no adaptive subdivisions and no additional bound rounds within an
individual tile.

Most tiles are excluded by one static exact dual or by a frozen original
interval/inset terminal. The remaining tiles are contained in one full
rectangle. That rectangle is treated by one complete bound induction;
there is no further subdivision.

| Original suffix | Initially pending tiles | Entire covering rectangle in tile indices | Static tiles used outside it |
| --- | --- | --- | ---: |
| `f92d74e712afa6be` | `0, 8` | `0, 8` | 62 |
| `b8e4f47ec1258e16` | `0, 8` | `0, 8` | 62 |
| `1de449e714cf90dd` | `0, 8, 10` | `0, 1, 2, 8, 9, 10` | 58 |

For the third row, tiles 1, 2, and 9 already have static exclusions. The
rectangle deliberately includes them to obtain a full Cartesian product.
Their static certificates are unnecessary for that assembly. Overlap
causes no logical problem; each point is covered at least once.

The exact three covering rectangles are:

| Original suffix | I horizontal interval | I vertical interval |
| --- | --- | --- |
| `f92d74e712afa6be` | `[-245887/1048576, 573059/4194304]` | `[-91/60, -166087423/125829120]` |
| `b8e4f47ec1258e16` | `[-25333/131072, 87841/524288]` | `[-91/60, -8970253/7864320]` |
| `1de449e714cf90dd` | `[-25333/131072, 87841/524288]` | `[-91/60, -22631257/25165824]` |

The checker recomputes these endpoints from the verified parent rectangle
and tile formula. It also checks that the declared covering tile set is
exactly the entire Cartesian rectangle bounding the pending tiles.

## 3. Physical inequalities and exact table arithmetic

The geometric inputs are the original corner/disk inequalities, all
original pair inequalities, the physical unit-frame identities, and the
previously proved support/inset, altitude, strip, and point-incircle
inequalities. Their hand proofs are:

- [Original frame bounds](A2_00100_ORIGINAL_FRAME_BOUND_HAND_PROOF.md).
- [Disk inset and diamond separation](DISK_INSET_AND_DIAMOND_SEPARATION_HAND_PROOF.md).
- [Physical frame perspective and directional support](ORIGINAL_FRAME_PERSPECTIVE_AND_DIRECTIONAL_SUPPORT_HAND_PROOF.md).
- [Original support-height pairs](ORIGINAL_SUPPORT_HEIGHT_PAIR_HAND_PROOF.md).
- [Three-original altitude capacity](THREE_ORIGINAL_ALTITUDE_CAPACITY_HAND_PROOF.md).
- [Three-original narrow-strip capacity](THREE_ORIGINAL_NARROW_STRIP_CAPACITY_HAND_PROOF.md).
- [The sharper three-original strip inequality](THREE_ORIGINAL_SHARP_STRIP_CAPACITY_HAND_PROOF.md).
- [Original point-incircle and frame coupling](ORIGINAL_POINT_INCIRCLE_FRAME_COUPLING_HAND_PROOF.md).

Every additional physical row is reconstructed independently from its
named rule and exact current guard bounds. The checker rejects an
unrecognized rule rather than accepting its printed coefficients.

For clarity, the exact arithmetic principle used throughout the tables
is elementary. Suppose the current physical rows are
`r_j . z <= b_j` and `|z_k| <= M_k`. Given nonnegative rational weights
`w_j`, put `A = sum_j w_j r_j`, `B = sum_j w_j b_j`. Then

\[
-\sum_k M_k|A_k|\le A\cdot z\le B.
\]

Consequently the positive reserve

\[
\rho=-B-\sum_kM_k|A_k|>0
\]

is a contradiction. Likewise a proposed objective bound `v . z <= U`
follows whenever

\[
B+\sum_k M_k|v_k-A_k|\le U.
\]

The tables contain the rational rows, nonnegative weights, coefficient
sums, absolute bounds, and reserve or proposed bound. Arithmetic uses
exact rational numbers. Floating-point optimization discovers possible
weights but is not part of the proof.

The original interval/inset terminals are checked by rebuilding their
underlying physical alternatives. An empty propagated interval is a
literal inequality of rational endpoints. An inset-pair terminal means
all four valid original inset separation options are impossible on that
entire tile, not merely that one option failed.

## 4. The static exclusions

| Original suffix | Positive-reserve static tiles | Original geometric static tiles | Total outside rectangle |
| --- | ---: | ---: | ---: |
| `f92d74e712afa6be` | 29 | 33 | 62 |
| `b8e4f47ec1258e16` | 29 | 33 | 62 |
| `1de449e714cf90dd` | 24 | 34 | 58 |

Each tile uses the parent frame and relational premises with only the
closed I-center tile restriction added. All corners and pairs remain in
the reconstructed physical system. Each positive-reserve table is
checked separately; neither candidate counts nor approximate feasibility
statuses imply an exclusion.

## 5. The three complete rectangle inductions

For each covering rectangle, begin again from the independently derived
whole-parent state and intersect only I's center intervals with that
rectangle. At every round, retain and re-establish all original parent
relational bounds. Intersect new proved position, scalar, and difference
bounds simultaneously. Then derive the permitted angle refinements from
the physical frame identities and intersect with the corresponding
analytic frame bounds. All inferences are implications on the whole
rectangle.

| Original suffix | Exact new deductions by round | Total rectangle deductions | Terminal |
| --- | --- | ---: | --- |
| `f92d74e712afa6be` | `133, 194, 211` | 538 | 19-row positive reserve |
| `b8e4f47ec1258e16` | `124, 208` | 332 | Empty physical D-frame interval |
| `1de449e714cf90dd` | `112, 207` | 319 | 30-row positive reserve |

### 5.1 The f92 rectangle

After its three rounds, the exact final reserve is

\[
\frac{
13208044509950935186734389875284714559093445966701877107135567986001
}{
1415343433165560989603636752692960332062449102144404777748320468598784
}>\frac1{110}>0.
\]

The 19-row contradiction holds for the full two-tile rectangle, including
its upper and right boundaries. Combined with its 62 static exclusions,
it proves the entire f92 original empty.

### 5.2 The b8e rectangle: a short physical terminal

Both induction rounds are necessary. After all 332 exact deductions, the
physical D-frame variables satisfy

\[
\alpha_D\le\frac{500885}{524288},\qquad
g_D\ge\frac{423149}{1048576}>\frac25.
\]

For the canonical square frame, put `m=|t_D|`, so `0 <= m <= 1`,
`alpha_D=1/sqrt(1+m^2)`, and

\[
g_D^2=\frac{1+m^2}{4(1+m)^2}.
\]

The upper bound on `alpha_D` implies `m > 17/55`, since

\[
3025\,(524288)^2-3314\,(500885)^2=70182897950>0.
\]

The function `(1+m^2)/(4(1+m)^2)` decreases for `0 <= m <= 1`.
Therefore

\[
g_D^2\le\frac{1657}{10368}<\frac4{25},\qquad
\frac4{25}-\frac{1657}{10368}=\frac{47}{259200}>0.
\]

This gives `g_D < 2/5`, contradicting its proved lower bound. The lower
bound itself exceeds `2/5` by `18593/5242880`.

The independent interval replay also witnesses the contradiction
directly. Its proved interval for variable 48, which is `g_D`, begins at
`423149/1048576`; its physical upper endpoint is
`14064758533227/35184372088832`. Their positive gap is
`133765813141/35184372088832`.

The final certificate arrays retain the last complete state before this
empty physical intersection. The checker treats them only as that prior
state: it replays every deduction in the closing round and computes the
actual empty intersection. No stale saved array supplies the terminal.
The full rectangle and all 62 remaining static tiles are therefore
excluded.

### 5.3 The 1de rectangle

After its two rounds, the exact final reserve is

\[
\frac{
586840828235344364334719702826160780918791066275519
}{
297108047703684636048042820959984453018421446888652800
}>\frac1{510}>0.
\]

The 30-row contradiction holds on the entire six-tile rectangle. Its
58 outside static exclusions cover the rest of the original center
rectangle. Thus the complete 1de original is empty.

## 6. Complete proof accounting and replay

Across these three originals, the proof consists of 108 earlier
coordinate deductions, 1,272 new whole-parent deductions, and 1,189 new
covering-rectangle deductions. The printed-row counts are 2,572 for the
whole-parent inductions and 1,923 for the center covers, or 4,495 in all.
The final cover uses 182 static domains and three complete rectangles.
It accounts for every one of the 192 original fixed tiles.

The frozen first checker, `verify_fixed_i_parent.py`, proves the f92
assembly. The separate generic checker, `verify_fixed_i_parent_v2.py`,
proves b8e and 1de and also retains the f92 case. Neither imports the
grid producer, the rectangle producer, an optimizer, or a point-search
routine. Both call `verify_joint_original.replay` for the independently
checked whole-parent state and use the separately implemented physical
row rules for the new steps. Root review and fresh independent replays
accepted all three complete-original assemblies.

The packet binds every producer source, additional source, original
parent certificate, grid manifest, tile record, and rectangle record to
its SHA-256 digest. Portable replay resolves the original source paths
through the packet's explicit `source_bindings.json` map; it does not
require trusting a source's original absolute location.

Six deliberately damaged f92 controls were rejected: a missing tile,
a shifted shared face, a negative multiplier, a false physical row,
an unjustified induction bound, and a missing rectangle face. These
controls concern the cover and inference checks, not the soundness of a
numerical discovery procedure.

No Lean, Lake, or CI run is used or claimed. The deliverable is the
complete physical hand/table argument, its exact rational tables, and
an independently implemented replay. Other still-open originals and
whole-mask obligations retain their prior status.
