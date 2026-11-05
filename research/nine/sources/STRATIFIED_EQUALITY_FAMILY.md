# n=9: complete equality domain in the rotated-stratified class

**Status (2026-10-22): complete necessary-and-sufficient *conditional*
hand classification.** This covers **every** radius-\(R_*=\sqrt{1105}/16\)
packing admitting the orientation-free horizontal stratification of
[ROTATED_STRATIFIED_NINE.md](ROTATED_STRATIFIED_NINE.md).
It does **not** assert that all unrestricted equality packings admit
a stratification. In particular,
[NO_GLOBAL_ORTHOGONAL_FRAME.md](NO_GLOBAL_ORTHOGONAL_FRAME.md)
is an equality packing **outside** the stratified class in *every*
frame: any orientation-free horizontal stratification makes *all*
pairs separable along one of its two coordinate axes, whereas the
exact witness has no globally separating orthogonal frame.

The classification is an explicit at-most-nine-dimensional parameter
domain with only three scalar slider bounds, two corner-containment
inequalities, one upper-pair projected-separation inequality, and two
upper-to-row inequalities. It does not restate the original 36
pairwise separating-axis disjunctions.

## 1. Fixed seven-square skeleton

Put
\[
 Q=\frac{1105}{256}, \qquad
 L_M=\frac{\sqrt{849}}{16}-\frac12,\qquad
 L_B=\frac12-\frac{\sqrt{1041}}{16}.
\]

Take four axis-aligned middle squares at centers
\[
 (-3/2,1/16),\quad(-1/2,\alpha),\quad
 (1/2,\beta),\quad(3/2,1/16)
 \tag{1}
\]
and three axis-aligned lower squares at centers
\[
 (-1,-15/16),\quad(0,\gamma),\quad(1,-15/16).
 \tag{2}
\]

Their **exact admissible slider range** is
\[
 \boxed{
 \frac1{16}\le\alpha,\beta\le L_M,
 \qquad
 L_B\le\gamma\le-\frac{15}{16}.}
 \tag{3}
\]

To see this, horizontal projections of distinct squares in either
group have disjoint interiors, independent of their heights.
The middle group lies entirely above the lower group if
\(\alpha,\beta\ge1/16\) and \(\gamma\le-15/16\).
The farthest corner of an axis-aligned square centered at (x,y) has
squared norm \((|x|+1/2)^2+(|y|+1/2)^2\).
For the two inner middle squares this gives
\(1+(\alpha+1/2)^2\le Q\), and likewise for \(\beta\);
for the center lower square it gives
\(1/4+(1/2-\gamma)^2\le Q\). These are exactly (3).
The four outer anchors automatically fit, with equality \(Q\).

Thus (3) is necessary *and sufficient* for the seven-square
skeleton to satisfy all internal pairwise disjointness and
disk-containment constraints.

## 2. Two independently rotated squares above the skeleton

For i=1,2, choose any center \(c_i=(x_i,y_i)\) and
any orthonormal unit side frame \((u_i,v_i)\), with
\(v_i\) perpendicular to \(u_i\). Define the
coordinate halfwidth
\[
 h_i=\tfrac12\bigl(|u_i\cdot(1,0)|
                 +|v_i\cdot(1,0)|\bigr)
     =\tfrac12\bigl(|u_i\cdot(0,1)|
                 +|v_i\cdot(0,1)|\bigr),
 \tag{4}
\]
and the exact corner radius functional
\[
 D_i=x_i^2+y_i^2+\frac12+
               |c_i\cdot u_i|+|c_i\cdot v_i|.
 \tag{5}
\]

Put
\[
             H=\frac12+\max\{\alpha,\beta,1/16\}
              =\frac12+\max\{\alpha,\beta\}.
 \tag{6}
\]

Require **only** the following constraints for the two added squares:
\[
 \boxed{
 D_1\le Q,\quad D_2\le Q,\qquad
 |x_1-x_2|\ge h_1+h_2,\qquad
 y_1-h_1\ge H,\quad y_2-h_2\ge H .}
 \tag{7}
\]

All upper-square disk vertices satisfy the containing radius because
(5) is the maximum squared norm over four vertices; convexity gives
containment of the whole square. Their horizontal projection
intervals have disjoint open interiors by the third condition
in (7), so they have disjoint open interiors. Their lowest
vertical coordinates exceed or equal the highest point of
any middle/lower anchor by the last two conditions, so neither
upper square overlaps any of the other seven. This proves
**sufficiency** of (3) and (7).

## 3. Complete conditional equality theorem

**Theorem 3.1 (exact necessary-and-sufficient stratified equality
family).** Let nine independently rotated unit squares fit in the
disk of squared radius \(Q\), with an orientation-free horizontal
stratification into nonempty layers. Then, up to isometry of the
plane and relabeling, their configuration is exactly of the form
(1)--(2) plus two squares parametrized by (4)--(7). Conversely
**every** choice of parameters satisfying (3), (4)--(7) is a packing
with squared minimal containing radius exactly \(Q\).

The reflected configuration, with two squares below the middle
four and three above, is included up to isometry; if the equivalence
notion permits rotations but *not reflections*, list that mirror
as a separate branch.

*Proof.* The stratified theorem
[ROTATED_STRATIFIED_NINE.md](ROTATED_STRATIFIED_NINE.md), Theorem 3.1,
shows that any stratification at \(q=Q\) has exactly three layers
of cardinalities 3,4,2 or 2,4,3.
Reflect vertically if needed to arrange 3 below, 4 middle, 2 above.
The seven-anchor equality corollary
[ORIENTATION_STABLE_SEVEN_ANCHOR.md](ORIENTATION_STABLE_SEVEN_ANCHOR.md),
Corollary 4.2, forces the seven squares in the two lower layers
to be axis-aligned in the chosen frame, with exactly the x-coordinates
and outer heights of (1)--(2). Their remaining heights are
precisely the three sliders \(\alpha,\beta,\gamma\).
The layer separation and disk constraints are equivalent
to (3), as calculated in Section 1.

The remaining top two squares are independent unit squares,
so they have free centers and orientations (4).
Their disk containment is exactly (5), and the
stratification definition gives their projected
horizontal nonoverlap and complete vertical separation from
the middle layer. These are exactly (7), so
**necessity** holds.

Sufficiency was checked in Section 2. Finally the outer
corners of the four pinned anchors lie on the circle
\(\|z\|^2=Q\). Thus no circle about the stipulated center
with smaller radius can contain the configuration, even though
the universal optimality assertion for *all* configurations
has not been proved. \(\square\)

## 4. The parameter domain has genuine nine-dimensional interior

The three slider parameters in (3) can be varied into an open
three-dimensional corner of their ranges, while keeping
the two upper squares of
[NO_GLOBAL_ORTHOGONAL_FRAME.md](NO_GLOBAL_ORTHOGONAL_FRAME.md)
at their explicit centers and a small fixed rotation **after**
increasing their horizontal separation enough that (7) holds.
For example, use the following exact upper squares:
\[
 c_1=(-3/5,19/16),\quad c_2=(3/5,19/16),\qquad
 u_i=(99/101,20/101),\quad v_i=(-20/101,99/101).
 \tag{8}
\]
They have horizontal center gap \(6/5\),
full horizontal projection width \(119/101\), and
\[
 \frac65-\frac{119}{101}=\frac{11}{505}>0 .
\]
Both are at vertical distance \(29/808>0\) above the
highest point of the anchored rows with
\(\alpha=\beta=1/16\).
The corner-radius slacks, obtained by exact substitution into (5),
are respectively (33167/80800>0) at (x=-3/5) and
(14367/80800>0) at (x=3/5).

Therefore a small open neighborhood of the six upper
center/orientation parameters remains feasible at the
base slider values. Simultaneously, \(\alpha,\beta\) may
increase slightly and \(\gamma\) decrease slightly, preserving
(3), (7). Consequently the conditional equality family
contains a genuine local nine-dimensional set of parameters
(3 sliders, 4 upper center coordinates and 2 upper angles).
This is a statement about the explicit **stratified**
equality family, not a global classification of all n=9
extremizers.

## 5. Formalization interfaces (future)

The Lean equality type for this branch can store only
three real sliders and two UnitSquare values. Its
Admissible predicate is the eleven scalar inequalities
in (3) and (7) (plus unit-frame conditions already
stored by UnitSquare). No nine-way pairwise Packing
hypotheses are needed in the parameter predicate.

The global n=9 equality theorem must first
establish G2 structural coverage. Without that theorem,
this finite parameterization is a **conditional terminal
classification**, not the public optimalPackings 9.
