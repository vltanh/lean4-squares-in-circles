# Unrestricted structural hand continuation

November 2, 2026. **The unrestricted lower bound and global equality
classification remain OPEN.** This checkpoint proves four new statements
without imposing a coordinate cover or limiting the number of exceptional
pairs. The complete orthogonal one-exception theorem remains available.

Throughout, put

\[
Q=\frac{1105}{256},\qquad r=\sqrt Q.
\]

## 1. A global two-order reduction

The main new structural source is
[UNRESTRICTED_FIVE_PROXY_CHAIN_HAND_PROOF.md](UNRESTRICTED_FIVE_PROXY_CHAIN_HAND_PROOF.md).
For each physical square and each orthonormal frame, let

\[
h\in[1/2,1/\sqrt2],\qquad g=\frac1{4h}.
\]

The square contains its concentric coordinate-aligned square of halfwidth g.
The new unary estimate is

\[
|x|-g<\frac{17}{16},\qquad |y|-g<\frac{17}{16}.
\]

Keep all actual physical x- and y-projection comparisons. For every pair
uncovered by both actual orders, add a comparison in the coordinate with
the larger absolute center gap. Resolve equality in either coordinate.
The inscribed squares guarantee that the selected gap is at least the sum
of the two g values. These additions are already transitive: any two-step
path has an actual comparison between its extremes, since

\[
g_S+2g_T+g_U\ge\sqrt2\ge h_S+h_U.
\]

**Both completed orders have height at most four.** A hypothetical
five-chain would force its three internal halfwidths above 45/64 and its
outer halfwidths below 49/80. The first pair would then have center distance
strictly greater than 144/125 by its relative physical orientations. But
the selected-coordinate rule and the exact center bands would bound that
same distance by 13sqrt(2)/16, which is less than 23/20 and hence less than
144/125. This is a physical contradiction, not an enumeration of poses.

Greene's cited finite-poset theorem now gives an **unconditional**+nine-square disjunction:

1. All nine squares fill a three-by-three array of completed chain-ending
   ranks. Each row is a completed x-chain and each column a completed
   y-chain; the two outer squares of each row or column have an actual
   comparison in that coordinate.
2. Seven squares form two disjoint completed projection chains of lengths
   four and three in one coordinate direction.

All added edges remain marked as nonphysical comparisons. The old physical
4+3 theorem cannot be applied to an arbitrary completed 4+3 pair of chains.
The argument does not infer a geometric grid from a Greene partition.

## 2. A sharp physical cap for three whole squares

[THREE_SQUARE_SHARP_HALFPLANE_CAP_HAND_PROOF.md](THREE_SQUARE_SHARP_HALFPLANE_CAP_HAND_PROOF.md)
proves the following new terminal:

> Three independently oriented unit squares lying wholly in the half-plane
> e·x >= 7/16, with disjoint open interiors, require squared containing
> radius at least Q.

The statement is sharp: take aligned centers (-1,15/16), (0,15/16), and
(1,15/16), in a frame with e vertical. The two outer upper corners have
squared norm Q.

The proof establishes a closed two-point capture statement. Every individual
Q-contained square whose lower edge is at least 7/16 contains at least one
of (-1/2,7/6) and (1/2,7/6). Larger halfwidths use the independently proved
center cap below; smaller halfwidths have a complete four-case owned-side
argument. The two shallow cases compare an actual corner directly with
(3/2,23/16), retaining nonnegative squared increments.

The points may be shared on boundaries at equality. For q<Q, a slight common
expansion of the three centers preserves the half-plane condition, keeps
all units in the Q-disk, and makes every pair of closed squares disjoint.
Three disjoint closed squares cannot each contain one of two fixed points.
This supplies the required strict-counterexample contradiction without an
incorrect claim that the half-unit markers are always interior points.

Consequently, in any hypothetical q<Q nine-square packing, every direction
has at most two whole squares beyond each of the two lines at signed
distance 7/16. At least five squares meet the intervening central strip.
No argument yet forces a prohibited triple from this necessary condition.

## 3. A universal three-center cap and a stronger normalized guard

[THREE_SQUARE_DIRECTIONAL_CAP_21_OVER_20_HAND_PROOF.md](THREE_SQUARE_DIRECTIONAL_CAP_21_OVER_20_HAND_PROOF.md)
proves that every Q-contained unit with center height at least 21/20
contains one of the points (±499/1000,7/6) in its interior. Thus, for every
three physical units and every unit direction e,

\[
\min_i e\cdot c_i<\frac{21}{20}.
\]

This is an unconditional physical inequality; its rational constant is not
asserted sharp. The proof uses the exact length of a horizontal section,
actual owned side normals, and one displayed degree-eight polynomial. Every
coefficient is specified by a single square-expansion identity. Positivity
on the full interval follows from derivative bounds and one rational
anchor, with no sampled orientation cover.

Every triangle of three centers therefore meets the open central disk of
radius 21/20. In the existing exact normalized boundary-square domain, the
selected boundary square contains (7/6,499/1000) in its interior. Any other
unit with x-center at least 21/20 must contain (7/6,-499/1000) instead.
There can be at most one such additional unit. Hence at least seven of the
eight other centers satisfy x<21/20. The earlier sharp x<H guard on all
eight remains valid simultaneously.

## 4. An actual four-chain controls every physical outsider

[UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md](UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md)
removes the coordinate-cover premise from the outsider strip bound.
For any actual horizontal four-chain in the Q-disk, every additional
physical unit has center

\[
|x|<\frac{13}{12}.
\]

The endpoint argument now retains the tilt reserve

\[
|y_0|+|y_3|+\frac{37}{50}(h_0+h_3-1)\le\frac18.
\]

It implies g_E-|y_E|>221/600 for each endpoint. Replacing the endpoint
only by its contained g-square and retaining the outsider's full physical
square gives an exhaustive separating-axis inequality. An outsider with
|x|>=13/12 would then have an actual corner outside the Q-disk. The scalar
orientation bound is proved continuously and has a printed rational reserve.

Thus, if an unrestricted nine-square packing has an actual four-chain,
all five outsiders lie in this strip. Their coordinate comparisons and
their five-body capacity are still to be established; they are not imported
from the earlier one-exception argument.

## 5. Remaining original goal and method record

The remaining unrestricted geometry is now concrete: settle the completed
three-by-three branch and the completed four-plus-three branch, retaining
all physical pairs and both additional squares. Available exits include
the physical 4+3 terminal, the sharp three-square half-plane cap, the proved
one-exception theorem, and the earlier two-strip terminal. This document
does not claim that every completed chain is physical or that one of those
exits has already been forced.

The same 15 roadmap IDs and 7,915 canonical root IDs are retained. No new
whole-root transfer is proved here: the published tally stays **5,838
excluded / 2,077 open**. The earlier archive-only 312 exclusions remain
separate. A.2, unrestricted equality, and the final complete manuscript stay
open.

All four accepted proofs have complete hand derivations and independent
agent hand review. Two numerical direction experiments occurred across the
current continuation: the earlier 48-start three-square-cap exploration and
a later 48-start four-square side-strip exploration. Neither experiment is
a proof input or a certificate; their results do not close any case. No
mathematical proof program, Lean, Lake, or CI was run. Text and JSON handling
is used only for editing and publication.
