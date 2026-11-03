# An exact v=1 boundary control for the closed-weak full-nine relaxation

November 3, 2026. This is an exact feasible control for the **closed
relaxation** of the weak bit. It is not a counterexample to the original
strict `001/00` statement. It explains why a compact positive-reserve-only
LP forest cannot by itself finish the current bulk target.

## 1. Nine unchanged physical originals at Q

Every square below is axis aligned with side length one. Put
`Q=1105/256`. Labels H,I are chosen so that `x_H<=x_I`, as in the bulk
search.

| Original | Center x | Center y | Largest corner norm squared |
|---|---:|---:|---:|
| A | -3/2 | -1/16 | 1105/256 |
| B | -1/2 | -1/16 | 337/256 |
| C | 1/2 | -17/16 | 881/256 |
| D | 3/2 | -1/16 | 1105/256 |
| E | -1 | 15/16 | 1105/256 |
| F | 0 | 15/16 | 593/256 |
| G | 1 | 15/16 | 1105/256 |
| H | -1/2 | -17/16 | 881/256 |
| I | 1/2 | -1/16 | 337/256 |

The table proves containment in the closed disk of squared radius Q.
It is a relabeling of the canonical aligned four-plus-three-plus-two-row
equality construction. In each row, distinct centers differ horizontally
by at least one. The three row heights differ by at least one. Thus
every pair of original interiors is disjoint. The companion exact
checker verifies all 36 corners and all 36 physical pairs separately.

## 2. The marked links and their actual bit

Each marked horizontal gap is exactly one. Their transverse gaps are

\[
y_B-y_A=0,\quad y_C-y_B=-1,\quad y_D-y_C=1,
\quad y_F-y_E=0,\quad y_G-y_F=0.
\]

All five original cone comparisons hold, including the two diagonal
equalities. The first two main links and both short links are actual
projection separations, as required by `001/00`. However, C,D also have

\[
d=x_D-x_C=1=h_C+h_D,
\qquad v=y_D-y_C=1.
\]

Their **strict** weak comparison `d<h_C+h_D` is false. The true mask is
`000/00`; only the closed relaxation `d<=h_C+h_D` accepts the control.
Its transverse gap is one, so the issue persists after upgrading the
low-gap exclusion from `5/8` to `2/3`.

The same physical collection has an alternate actual four-chain
`A,B,I,D` and the actual short chain `E,F,G`. The original actual-chain
theorem gives the expected nonstrict lower bound `R^2>=Q` at this
boundary point. This observation alone does not prove a neighborhood
terminal: nearby original configurations must retain whatever alternate
cone, bit or span conditions that terminal requires.

## 3. Consequence for the current proof search

A family of closed necessary inequalities that includes this assignment
is feasible. It therefore cannot have a strict positive Farkas
contradiction. Subdivision into closed angle and position boxes does not
alter this fact at boxes containing the exact point.

Consequently the remaining strict problem needs a step that preserves
the strict weak comparison, excludes an analytic neighborhood by a
proved alternative witness, or proves a nonstrict sharp inequality whose
equality conditions contradict that strict bit. A positive-reserve-only
cover of the entire closed-weak relaxation is an impossible target.
Existing strict leaves remain valid partial exclusions; a nonempty
frontier is not a complete certificate.

This does not refute the strict original mask theorem. In addition to
the explicit failure of its weak bit here, the independently established
all-frame boundary sanity lemma shows that this aligned collection has
no strict `001/00` or `100/00` witness in any frame or labeling.

## 4. Exact control versus floating matrix diagnostic

`computer_assisted/weak_outer_numeric_relaxed_boundary_control.py`
uses only exact fractions and verifies the original geometry, all marked
comparisons, the failed strict weak bit and the alternate actual chain.
It contains the complete control; no optimizer output is a premise.

The frozen historical diagnostic in
`computer_assisted/weak_outer_dense_boundary_snapshot/weak_outer_numeric_bulk_boundary_matrix_probe.py`
inserts the same original assignment into the floating bulk matrix,
choosing a physical owned normal for all 28 nonimplied original pair
branches and assigning every McCormick product its actual product value.
The recorded dense-matrix probe had 7,959 rows, 222 variables and maximum
row violation zero. Its nearest dense corner support plane still had
slack about `0.0004300`. This is a diagnostic of that finite outer
relaxation, not a substitute for the exact geometry check or a proof of
the strict original predicate. The snapshot includes every numerical
source dependency, its source manifest, and the reproduced
`diagnostic.json`. Its producer SHA-256 is
`855ef40405fe8fd136c1c37ca2c9d8da323f0a5e83a016bd68f4688a566cf3ba`.
Later strict-predicate terminals are not retroactively inserted into this
historical closed-relaxation diagnostic.
