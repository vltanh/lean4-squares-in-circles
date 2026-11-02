# Independent review of the own-half upper-side reduction

November 2, 2026. This review concerns Sections 1–5 of
`WEAK_MIDDLE_OWN_HALF_ABOVE_SIDE_EXTRA.md`. It verifies the physical
reduction to the three-variable finite table. Arithmetic acceptance is
separate, and this local exclusion alone does not close 010/11.

## Original caller and localization

Horizontal reflection covers both choices of the selected P's half.
At xP=0 either choice is valid. The three originals C,S,P keep independent
signed frames. R is a fourth, distinct original; it is used only in the
localization and vertical-order arguments. No new cone comparison
between P and S or between S and R is imposed.

The original P–R cone and their centered radius-1/2 disks give
xR−xP>707/1000. Thus xR>707/1000, and the accepted endpoint-inset
localization of a shoulder below 3/5 forces yR≥3/5. Both R and S have
centers in the closed right side strip, so the original two-square
9/16 side-center cap gives yS<9/16.

The 3/4 physical clearance lemma applies to C,S on the full interval
1/2≤hC≤13/20. The horizontal-gap calculation is valid in both
directions; hC−gC≤69/260<3/10 is sufficient. Together with the original
outer-cone lower bound yC>−6/5, it gives yS>−9/20. Hence the vertical
distance from S's center to the original endpoint inset is less than
233/1200. The inset extends beyond xS on its outer side, since its
right edge exceeds 937/480 while xS<13/12. Avoidance of its interior
by the centered radius-1/2 disk therefore proves xS<147/250.

The final strict rational localization reserve is exactly

\[
 1/4-(233/1200)^2-(503/480-147/250)^2
 =111739/144000000>0.
\]

## The original vertical order

The hypothesis gives C below S. If P were below S, both horizontal
gaps P–S and S–R would be less than 3/5, and their sum would be less
than 13/12. At least one gap is therefore below 13/24. The two
center-disk inequalities force the corresponding vertical gaps above
21/25 and 4/5, using

\[
 1-(13/24)^2-(21/25)^2=359/360000>0.
\]

Thus yR−yP>41/25. But the original center radius and xR>707/1000
give yR<671/500, with squared reserve 4817/9000000. The independent
own-half 909/1000 clearance, applied to original C,P, gives
yP>−291/1000. The resulting upper bound yR−yP<1633/1000 contradicts
the lower one by 7/1000. Equal P,S heights are separately impossible
because their horizontal gap is below 147/250<1. Consequently
C<S<P is exhaustive.

## Exact signed clearances and horizontal vertices

For a frame (a,sb), the two upward versions of its side axes are
(sa,b) and (−sb,a). The common sum of the two original-square supports
on any of their four owned axes is

\[
 \sigma=(1+|f\cdot g|+|\det(f,g)|)/2\ge1.
\]

The P–S horizontal gap has absolute value below 147/250. On the
entire proposed main-coordinate box, the two directions of the C–S
gap are bounded above respectively by 57183/260000 and 1993/60000,
which are also below 147/250. Thus a nonpositive vertical component
cannot separate either original pair, because its directed projection
is at most the absolute horizontal gap and is below sigma.

Every upward-axis numerator is positive. Replacing its vertical
component by max(ny,1/20) lowers the necessary threshold. At a zero
vertical component the axis was impossible in the first place; adding
its clipped threshold to a minimum is still a valid weakening. This
retains all aligned frames and all independent sign families.

For clarity, the sharper main-coordinate box can be reconstructed
without importing an unstated near-aligned bound. The actual right
outer link and xD<3/2+delta give xC<1+delta−hC. The actual left
outer link gives xB+gB>etaB−delta. The retained middle-cone inset
comparison xC−xB≥gB+gC then gives
xC>gC+etaB−delta≥gC−delta. These are exactly the two endpoints used
by the proposed table, with delta=331/20000.

For fixed frames each pair threshold is a minimum of affine functions
of the directed horizontal gap. It is therefore concave. The sum for
C–S and S–P is jointly concave in (xC,xP,xS). Its value anywhere in
the physical rectangular box is at least the minimum of its values at
the eight vertices. No maximum with a disk-distance bound, and no
change of frame between the two pair clearances, enters this step.
The possible inverted main interval at nonphysical h values is not
used by this implication; proving the displayed scalar there is merely
a stronger arithmetic target.

The main lower function Ymin(h) follows from the original endpoint
reserve and actual outer cone. Its minimum on each h interval is
reconstructed from

\[
Y(h)=32h/9+41/(36h)-32/9-199/120,
\qquad h_{\rm crit}=\sqrt{41/128}.
\]

The physical reduction, exact coordinate domains, complete sign union,
and concavity step pass this independent review.

## Complete independent arithmetic acceptance

The standalone `verify_ownhalf_above_side.py` independently reconstructed
the complete forest, all eight physical coordinate vertices, and every
signed-frame family. It imports no producer or producer arithmetic.
All 46,886 strict leaves in 93,764 nodes passed, with maximum depth 21,
eight roots, and no frontier. The largest independently enclosed scalar
upper bound is strictly below −1/100000; the exact rational is retained
in `ownhalf_above_side_cover_independent_replay.json`.

The certificate SHA256 is
`3a631f728e166fce940b2c69d7435c0ca9e191e9b8e5eab927268e12db56a6f3`.
The standalone checker SHA256 is
`a0541942633d3991a1c8fceff3db59f678c696feefc2208fc610d015b04d63b8`.
Arithmetic uses exact Fraction interval operations and independently
bounded 90-bit square roots. All eighteen damaged or false proof
objects were rejected; the separate evidence is
`ownhalf_above_side_rejection_controls.json`.

Thus the local own-half upper-side exclusion is accepted by this
independent physical and exact arithmetic review. No original extra
can lie above its own assigned main in the side strip on P's half,
under the displayed original 010/11 and selected bad-floor hypotheses.
This local consequence does not by itself close the mask.
