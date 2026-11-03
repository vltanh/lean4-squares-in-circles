# Complete F-H routing child 5 from two original H-center covers

## Statement and original scope

The two entire original cells `negative-daf08b7f35b70b9a` and
`negative-99f578b7bbedf013` are empty. Together they exclude the existing
F-H routing child 5 under the common original prefix

```text
angle(3,0)
angle_cut(0,0,0)
```

These are the closed nonpositive D and A angle sectors. The original
nine squares, their independent physical frames, all 36 corner conditions,
all 36 physical pairs, marked cones, strict CD bit, and strict-radius
caller are retained. The actual originals H and I are never exchanged.
In particular, the inherited order `x_H <= x_I` remains in force.

The full literal paths differ only at the existing F-height cut:

| Original | F-height child | Remaining routing step |
| --- | --- | --- |
| `negative-daf08b7f35b70b9a` | `y_F <= 1/2` | `f_side_escape(5,7,[5])` |
| `negative-99f578b7bbedf013` | `y_F >= 1/2` | `f_side_escape(5,7,[5])` |

The routing step retains the closed inequalities

\[
x_F\le x_H,\qquad
2y_H\le y_F+y_D-\frac35,\qquad
y_F-y_D\le\frac35.
\]

The two closed F-height children cover every possible F height, with the
face `y_F=1/2` retained in both. Therefore the conclusion concerns the
whole existing child-5 routing under the common prefix. Other F-H
routings, the whole family B, and the whole mask are not closed by this
argument.

## 1. The center-cover rule applies to any original

Let `j` be any fixed original square and let its proved center rectangle
be `[a,b] x [c,d]`. For `0 <= p,q < 8`, define

\[
T_{8p+q}=
\left[a+\frac{p(b-a)}8,\ a+\frac{(p+1)(b-a)}8\right]
\times
\left[c+\frac{q(d-c)}8,\ c+\frac{(q+1)(d-c)}8\right].
\]

These 64 closed rectangles cover the full proved center rectangle.
Every shared face has the same exact rational endpoint in both adjacent
tiles. If all tiles are excluded, the original parent is empty. It is
equally sufficient to exclude each tile outside a full Cartesian
rectangle and then exclude that entire rectangle in one implication
proof. Overlap with already excluded tiles is harmless.

This is a set-cover argument for the center of the selected original;
it does not depend on whether that original is named H or I. Each
physical implication still refers to the same nine actual squares.
Here `j=7`, so the restricted position coordinates are exactly 14 and 15.
The I-center proofs elsewhere use coordinates 16 and 17. The H checker
requires target 7 in the manifest, every tile, the rectangle record,
its prior, and its additional predicate, and checks the original order
predicates through the unchanged physical reconstruction.

## 2. Whole-parent premises and the fixed H covers

The complete parent inductions are replayed before any tile restriction.
Saved final arrays and discovery statuses are not premises.

| Original suffix | Earlier coordinate deductions | New parent deductions | Parent printed rows |
| --- | ---: | ---: | ---: |
| `daf08b7f35b70b9a` | 30 | 222 | 671 |
| `99f578b7bbedf013` | 38 | 472 | 957 |

The resulting whole-parent H rectangles are

| Original suffix | H horizontal interval | H vertical interval |
| --- | --- | --- |
| `daf08b7f35b70b9a` | `[-245887/1048576, 5/4]` | `[-91/60, 59887/1048576]` |
| `99f578b7bbedf013` | `[-25333/131072, 5/4]` | `[-91/60, 190107/1048576]` |

Apply the fixed closed eighth grid to each rectangle. In the first grid,
tiles 0 and 8 remain for the complete rectangle proof. In the second,
tiles 0, 8, and 10 lie in the complete 2 by 3 rectangle containing tiles
0, 1, 2, 8, 9, and 10. The checker proves only the static tiles outside
that rectangle; already closed tiles inside it are unnecessary.

| Original suffix | Complete covering rectangle | Static tiles used outside it |
| --- | --- | ---: |
| `daf08b7f35b70b9a` | `[-245887/1048576, 573059/4194304] x [-91/60, -166087423/125829120]` | 62 |
| `99f578b7bbedf013` | `[-25333/131072, 87841/524288] x [-91/60, -22144141/25165824]` | 58 |

The first static part has 27 exact positive-reserve contradictions and
35 original geometric contradictions. The second has 21 exact
positive-reserve contradictions and 37 original geometric contradictions.
Every static exclusion applies to its complete closed tile, with all
other original variables retaining their proved parent domains.

## 3. Complete rectangle inductions

Each rectangle proof starts again from its independently checked parent.
At every round it retains the parent scalar and pair-difference bounds,
reconstructs the physical rows and their guards, and installs all newly
proved bounds simultaneously. Physical frame refinements are checked
against the exact original frame identities.

| Original suffix | New deductions by rectangle round | Rectangle deductions | Final rows |
| --- | --- | ---: | ---: |
| `daf08b7f35b70b9a` | `132, 191, 205` | 528 | 19 |
| `99f578b7bbedf013` | `93, 201` | 294 | 30 |

For physical rows `r_k . z <= b_k`, nonnegative weights `w_k`, and proved
absolute variable bounds `|z_l| <= M_l`, the exact reserve is

\[
-\sum_k w_k b_k-
\sum_l M_l\left|\sum_k w_k r_{k,l}\right|.
\]

A positive reserve contradicts the physical rows on the entire domain.
Every printed coefficient, multiplier, residual, and guard is replayed
as a rational number.

The first rectangle has exact positive reserve

\[
\frac{
13208044509950935186734389875284714559093445966701877107135567986001
}{
1415343433165560989603636752692960332062449102144404777748320468598784
}.
\]

The second rectangle has exact positive reserve

\[
\frac{
20945921394195644124343387487324055948318642834611003
}{
11765150264671215026774762778464619570948581806728806400
}.
\]

Thus both covering rectangles are excluded, including every boundary.
Together with their static tiles, each proof covers its whole original
parent.

### An exactly cancelled alternative for the daf terminal

The corrected auxiliary table `daf_nineteen_row_exact_terminal_v2.json`
assigns 19 strictly positive rational multipliers to the same 19
independently reconstructed terminal rows. All 21 occurring variable
coefficients cancel exactly. The weighted right-hand side is

\[
-\frac{
10097575511680489073266167496518465126478505017997380175649396568473179953834486886416170819091532897
}{
17318634111378535821175801463922538716341845123879053931021975223862141152851512559635563621331763200
}< -\frac{29}{50}.
\]

Adding the weighted inequalities gives `0 <= negative_constant < 0`,
a contradiction. The original bound and rectangle records
are unchanged. Only the corrected v2 auxiliary table is delivered; the
earlier auxiliary decimal RHS is not used.

## 4. Independent replay and complete accounting

`verify_fixed_h_parent.py` imports the accepted original geometry and
the independently implemented joint physical-row checker. It imports no
H-grid producer, H-rectangle producer, or optimizer. The checker replays
every parent deduction, every required static tile, each complete
rectangle round, and the final positive terminal. It also binds the
grid manifest and summary, parent and rectangle records, and every
recorded source and additional-source digest.

Together these two original proofs contain 68 prior coordinate
deductions, 1,516 new deductions, and 3,068 checked printed rows. Their
finite cover has 120 static domains and two complete rectangles, and
accounts for all 128 fixed closed tiles. The rectangles require five
bound rounds in total and no internal subdivisions.

The literal path audit, frozen original register, and independently
replayed complete proofs give the F-height union stated above. No new
original ID, mask, or mandatory child gate is introduced. No Lean, Lake,
CI, or proof-kernel verification is used or claimed.
