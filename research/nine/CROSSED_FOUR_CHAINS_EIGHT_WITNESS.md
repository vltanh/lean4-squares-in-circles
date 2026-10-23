# n=9 C3.3: exact crossed-four-chain falsification and a saturated 8-square skeleton

**Status:** Exact constructive and no-extension hand lemmas; **NOT**
the full five-square complement theorem. This is a guard against the
false shortcut "a horizontal and a vertical four-chain cannot coexist
below the proposed n=9 radius." They **can** coexist.

## 1. Eight genuine squares in the record disk

Fix the disk center at the origin and the following eight
**axis-aligned** unit square centers, all distinct:

\[
\begin{aligned}
M&=\{(-3/2,0),(-1/2,-1/2),(1/2,1/2),(3/2,0)\},\\
N&=\{(0,-3/2),(1/2,-1/2),(-1/2,1/2),(0,3/2)\}.
\end{aligned}\tag{1}
\]

The four M squares have pairwise disjoint horizontal projection
interiors (the horizontal centers are -3/2,-1/2,1/2,3/2).
The four N squares have pairwise disjoint vertical projection
interiors (vertical centers -3/2,-1/2,1/2,3/2).
The chains M and N are disjoint as sets of squares.

Every pair of *all eight* centers has
\[
 \max(|x_i-x_j|,|y_i-y_j|)\ge1. \tag{2}
\]
This is clear among the four central centers
\((\pm1/2,\pm1/2)\), since their x or y coordinates differ by 1.
Each outer axial center \((\pm3/2,0),(0,\pm3/2)\) differs
by at least 1 in x or y from every central center;
outer axial pairs are separated even more.
Thus the eight closed squares have pairwise disjoint
open interiors.

For an axis-aligned unit square of center (x,y), its farthest
corner squared norm is
\[
 (|x|+1/2)^2+(|y|+1/2)^2.
\]
The four outside axial squares attain \(4+1/4=17/4\),
while the four central squares attain \(1+1=2\).
Therefore these eight squares fit **exactly** in the disk of
squared radius
\[
                  17/4=4.25<1105/256=4.31640625. \tag{3}
\]

Consequently the assertion that *two disjoint perpendicular
four-chains cannot coexist under q≤1105/256* is FALSE, even
with all square frames axis aligned. Any strategy using it must
be rejected rather than refined by numerical thresholds.

## 2. Saturation under common-coordinate separability

**Theorem 2.1 (no ninth square with x/y separation in this frame).**
There is no *additional*, independently oriented unit square T
contained in the disk of squared radius \(Q=1105/256\) whose
open projections are separated from **every** square of (1)
in at least one of the two original coordinate axes.

*Proof.* Every such T has center c=(x,y) with
\[
 \|c\|<\rho:=61/40, \tag{4}
\]
by the exact universal farthest-corner inequality
\(\|c\|^2+\|c\|+1/2\le Q\).
In the chosen coordinate frame the projection halfwidth
of any unit square is at least \(1/2\).
Thus, for T to be separated by x or y from an axis-aligned
square with center d, it is necessary that
\[
             |x-d_x|\ge1\quad\text{or}\quad
             |y-d_y|\ge1. \tag{5}
\]

We show some one of the eight listed centers has
**both** coordinate differences strictly less than 1.

If \(|x|<3/2\) and \(|y|<3/2\), choose the central center
\(d=(\operatorname{sgn}_*(x)/2,\operatorname{sgn}_*(y)/2)\),
where \(\operatorname{sgn}_*(0)\) is arbitrarily \(+1\).
Then \(|x-d_x|<1\) and \(|y-d_y|<1\).

If instead \(x\ge3/2\), (4) implies
\[
 0\le x-3/2<1/40,\qquad
 |y|<\sqrt{\rho^2-(3/2)^2}=11/40.
\]
Hence the axial center \(d=(3/2,0)\) has
\(|x-d_x|<1,\ |y-d_y|<1\).
For \(x\le-3/2\), use \((-3/2,0)\).
For \(|y|\ge3/2\), use \((0,\pm3/2)\)
and the symmetric argument.

Every center in the disk (4) is covered. This
contradicts the necessary coordinate-separation condition (5),
so no T can be added in the common coordinate frame. \(\square\)

The argument never assumes that T is axis-aligned. It **does**
use that the original eight squares are axis-aligned and that the
proposed ninth square is separable from each in one of those **two
specific** coordinate projections. An oblique-only separating axis
is outside this theorem's scope.

## 3. What this changes in the deep roadmap

- **C3.3 (4,1) complement is not closed.** This calculation is for
  **one exact saturated eight-square skeleton**, not every crossed
  four-chain packing with nine squares. Prove a stability/covering
  statement for the entire quantified (4,1) branch, or find an
  exact physical counterexample to an overstrong version.
- **No false shortcut:** The parent theorem cannot be
  "two disjoint four-chains never fit"; equation (1) refutes it.
- **Promising invariant:** Four central squares with centers near
  \((\pm1/2,\pm1/2)\) cover nearly all center locations by their
  unit \(\ell^\infty\) exclusion boxes. In any nine-square
  *coordinate-separable* packing, quantify exactly how the
  central holes/boundaries could escape this coverage, using
  actual square projection widths and the circle corner
  inequality—not center-radius alone.

The theorem above is a hand proof with exact fractions; no
Lean execution or unrestricted n=9 optimum is claimed.
