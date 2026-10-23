# Fixed-ceiling capture at S <= 3/200 transfers to the original packing

## 1. The precise remaining global input

Set
\[
 q_L=19577/5000=3.9154,\qquad
 Q_1=1957767069/500000000=3.915534138,\qquad
 Q_0=9789/2500.
\]
The table-free stationary existence theorem gives
\[
                     5/2<q_L<q_*<Q_1<Q_0<4.
\tag{1}
\]
Only these broad comparisons are needed. No narrow stationary-root
bracket or distance-to-candidate estimate is used.

The remaining **global capture input** is the following assertion about
every admissible seven-square boundary neighbor cycle at squared radius
Q1: G0--G5 supply the surviving candidate roles, all earlier signed
tangent cuts, the already proved zero owners, and S <= 3/200.
The earlier owner hypotheses here have their actual geometric meaning;
they are not fitted boundary labels or a choice of a preferred witness.

Under this input, the forward chain in
`TABLE_FREE_GEOMETRIC_HAND_ROADMAP.md`, Section 4, supplies all original
quarter and mixed owners and the owner-frame tilt
\[
                   1/10<\tau<4/25.
\tag{2}
\]
Here the selected ED witness is chosen once, d0 is its physical owner
frame, and tau = theta_H - d0. This is the frame used by
`HAND_OWNER_GAUGE_SHARP_TERMINAL_AT_THREE_TWO_HUNDREDTHS.md`.

**Transfer theorem.** If the stated global capture input holds, every
actual eight-square packing has squared containing radius at least q*.
Every packing attaining q* belongs, up to isometry and relabeling, to
the complete weak five-parameter family in
`HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md`.

This proves the transfer implication, conditional on global capture.
It does not establish any missing G3 cut or G4--G5 mismatch bound.
In particular, no contraction to S <= 1/1000 remains in this implication.

## 2. Fix the original signed witnesses before any translation

For a hypothetical packing below q*, replace only the containing disk
by one of squared radius
\[
                         \bar q=\max(q,q_L)<q_*.
\tag{3}
\]
The squares do not move. The existing central-core theorem applies
below Q0. Its seven exterior squares avoid the open radius-1/12 disk.
Order their centers cyclically and select one actual signed SAT witness
on each consecutive pair, including the closing pair.

The proof of `../CYCLIC_RADIAL_BOUNDARY_REDUCTION.md` preserves these
same seven witnesses throughout the entire construction. To see this,
when moving one square use the two initially selected incident SAT
halfplanes. They still contain its center by induction. Their normals
are fixed because no square frame has changed. The intersection of two
halfplanes has a nonzero recession direction: use the sum of their inward
unit normals unless they are opposite, in which case use a perpendicular
direction. Move along that direction until the first outer-circle or
core-boundary contact. Every selected SAT inequality remains valid.

The uniform angular separation argument in that reduction preserves
the cyclic order. After at most seven moves every square lies on one
of the two radial boundaries at qbar. Frames and the selected signed
normals are unchanged. Individual center rays and canonical tangents
are allowed to change during this step; they are not used as invariants.
The construction uses only consecutive nonoverlap, as required by the
boundary neighbor relaxation.

## 3. Expand only the outer radii to Q1

From this boundary cycle, fix each center ray and each physical frame.
For an outer square of relative angle alpha, its radius r(x) solves
\[
 r^2+B r+1/2=x,\qquad
 B=\cos\alpha+|\sin\alpha|\in[1,\sqrt2].
\]
For 5/2 <= x <= 4,
\[
 4/5<r<3/2,\qquad 1/4\le r'(x)\le1/3.
\tag{4}
\]
A core radius is fixed and below 4/5. These are the elementary bounds
proved in `../OUTER_RADIUS_MONOTONICITY_AND_SHARP_PULLBACK.md`.

For clarity, preservation holds for **every initially feasible signed
axis**, not just an axis newly selected after expansion. Its support
width is fixed and at least one. On an outer--outer pair its projection
is P = u r_A + v r_B, with |u|,|v| <= 1. When both coefficients are
nonnegative and P >= 1, (4) gives P' > 1/6. When one is negative,
write P = u r_A - s r_B. Feasibility implies
\[
 u>2/3+(8/15)s,\qquad 0\le s<5/8,
\]
and therefore
\[
 P'\ge u/4-s/3>1/6-s/5>1/24.
\tag{5}
\]
Both coefficients cannot be nonpositive. On a core--outer pair,
P = u r_O + v r_C >= 1 forces u > 2/15, hence P' > 1/30.
A core--core projection is constant. Continuity and these strict
derivative bounds at every feasible value exclude a downward crossing
of the fixed support threshold.

Thus expansion from qbar to Q1 preserves all selected original witnesses,
every physical frame, every center ray, every signed tangent, every
quarter offset, the cyclic order and S. Apply the assumed global
G3--G5 capture and the completed downstream owner and tilt chain at Q1.
Their owner exclusions cover every feasible original signed witness,
including ties. In particular, they cover the seven witnesses fixed
before the translations in Section 2.

## 4. Return to the previously constructed boundary cycle

Restore the outer centers to their positions at qbar. No reverse
monotonicity claim is required: the restored cycle and its fixed
witnesses were already feasible there before the expansion.

Between that cycle and its expansion, rays and frames were fixed.
Consequently the captured candidate roles and signed tangent cuts,
all frame differences and S, and the selected original physical normals
are identical. The selected ED owner is the same square with the same
frame d0, so the actual tau in (2) is identical as well. Core avoidance
and containment hold for the restored cycle by its construction.
Every earlier terminal hypothesis has therefore been supplied at qbar.

Apply the owner-frame terminal in this same gauge:
\[
 \bar q\ge q_*+\mu_H M(q_*,\tau)
 +\sum_{i=A,B,D,E,H}\mu_i
   \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
 +\frac{S}{5000}\ge q_*.
\tag{6}
\]
This contradicts (3). Neither a bound on center travel nor conversion
from tau to the older A/G tilt occurs in the argument.

## 5. Reapply the stationary identity to the original centers at equality

For an actual packing of squared radius q*, repeat Sections 2--4 with qbar = q*.
The nonnegative terms in (6) imply S = 0 and M(q*,tau) = 0. The
stationary existence theorem gives the unique zero tau = t*.
Thus the original A/B/T/D/E physical frames form one cluster, and
H/G form the other at the stationary tilt: no frame changed during
either construction. The seven initially selected normals have their
stationary directions. At S = 0, either allowed owner on a tied aligned
edge supplies the same physical normal.

Now discard the translated centers and use the actual original centers.
For their seven initially selected nonnegative signed gaps g_e, the
stationary weights satisfy lambda_e > 0, mu_i > 0 and sum mu_i = 1.
The exact zero-error force identities give
\[
 F_i=-2\mu_i(p_i^*+o_i)\quad(i=A,B,D,E,H),\qquad
 F_G=F_T=0.
\]
Consequently their stationary dual has the identity
\[
 \mathcal D:=\sum_i\mu_i|p_i+o_i|^2-\sum_e\lambda_e g_e
 =q_*+\sum_i\mu_i|p_i-p_i^*|^2.
\tag{7}
\]
This is the completion in `../EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md`,
Section 3, with the table-free stationary weights. Containment gives
\[
 q_*-\mathcal D
 =\sum_i\mu_i(q_*-|p_i+o_i|^2)+\sum_e\lambda_e g_e\ge0.
\tag{8}
\]
Equations (7)--(8) force the five original anchor centers and all seven
original gaps to be stationary. No original slider-coordinate bound
or original canonical tangent cut is needed: both slider forces vanish
exactly. In particular, no assertion that the initial translations
preserved those coordinates is hidden in the equality argument.

The remaining two exterior slider coordinates and the central square's
two translations and rotation obey exactly the necessary and sufficient
weak domain in `HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md`.
That theorem proves the complete family and its converse. This transfer
therefore preserves all five freedoms and adds no equality branch.

## 6. Effect on the active roadmap

The fixed-ceiling/original-center implication now matches the completed
S <= 3/200 owner-frame terminal. The older transfer note's S <= 1/1000
input and its older tilt/terminal references are unnecessary for this
route. All upstream assumptions remain explicit: the universal global
G3 tangent cuts and G4--G5 capture at Q1 are still to be proved.
No Lean source, historical table, compilation or CI run is involved.
