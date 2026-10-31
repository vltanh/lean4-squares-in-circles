# An occupied actual channel cap forces a low transmitter center

Date: October 26, 2026.

**Status: accepted complete geometric reduction after fresh full-source and
original-domain reviews in REVIEW_CHANNEL_CAP_OCCUPANCY_AND_FIVE_DIAMETER_ROOT_2026_10_26.md
and REVIEW_CHANNEL_CAP_OCCUPANCY_AND_FIVE_DIAMETER_C6_2026_10_26.md.**
It covers both actual one-transmitter widths,
every side-transmitter mean, arbitrary endpoint degrees and physical masks.
The final five-load C6 consequence is a necessary whole-family center bound,
not a completion exclusion.

Put
\[
Q=\frac{1105}{256},\qquad M=\frac{91}{60},\qquad m=\frac{89}{60}.
\]

## 1. Complete local statement

Let X,U,Y be actual interior-disjoint unit squares in the concentric disk
D_(sqrt(Q)). Suppose U is an original unloaded degree-two normal transmitter.
After one common rigid rotation and a left/right relabelling, its unchanged
endpoint applications and their support relations are
\[
P_X=(l,h),\qquad P_Y=(l+w,h),\qquad h>0,
\]
\[
X\subseteq\{x\le l\},\qquad
Y\subseteq\{x\ge l+w\},\qquad w\in\{1,\sqrt2\}.
\tag{1}
\]
No degree or force restriction is imposed on X or Y beyond these actual
support equations. They need not have the same physical circle mask or
equal circle weights.

Suppose an additional actual unit E, disjoint in open interior from U,
is wholly in the outward half-plane
\[
E\subseteq D_{\sqrt Q}\cap\{y\ge h\}.
\tag{2}
\]
In a physical channel application, a separate actual crosscut/routing theorem
must establish (2). It is not inferred from E's center alone.

**Theorem.** The unchanged transmitter center satisfies
\[
\boxed{|c_U|<\frac{89}{60}.}
\tag{3}
\]

The proof does not move E or U, does not choose an application mean, and
does not remove any endpoint force.

## 2. Elementary center and horizontal bounds

For any contained unit with center radius rho and own frame angle phi,
one of its corners gives
\[
\rho^2+\rho(|\cos\phi|+|\sin\phi|)+\frac12\le Q.
\]
Since the parenthesis is at least one,
\[
|c|<M.
\tag{4}
\]
The strict comparison at the fixed endpoint is
\[
M^2+M+\frac12-Q=\frac{31}{57600}>0.
\]

Write c_U=(x,y). For either actual width, x=l+w/2.
Every unit has projection halfwidth at least one half, so (1) implies
\[
(c_X)_x\le l-\frac12
=x-\frac{w+1}{2},\qquad
(c_Y)_x\ge l+w+\frac12
=x+\frac{w+1}{2}.
\]
Together with (4), this gives
\[
|x|<M-\frac{w+1}{2}\le M-1=\frac{31}{60}.
\tag{5}
\]
These bounds use upper bounds for actual center coordinates, not any
converse inferred from the reserve lower bound.

The whole-square cap inclusion (2) gives, for c_E=(X_E,Y_E),
\[
Y_E\ge h+\frac12,\qquad |c_E|<M.
\tag{6}
\]
Thus the existence of E implies h<M-1/2=61/60.

## 3. Every actual side-transmitter mean

If w=1, the complete unchanged transmitter is
\[
U=[l,l+1]\times
[h+\sigma-\tfrac12,h+\sigma+\tfrac12],
\qquad-\frac12\le\sigma\le\frac12.
\tag{7}
\]
In particular y=h+sigma>-1/2, and (6) gives Y_E>=y.

Suppose contrary to (3) that x^2+y^2>=m^2. From (5),
\[
y^2>m^2-(31/60)^2>(11/8)^2,
\]
where the last difference is 41/960. Since y>-1/2, the negative
square-root branch is impossible. Therefore
\[
y>\frac{11}{8}.
\tag{8}
\]

Whole-square containment of the actual axis-aligned U is stronger than
its center bound:
\[
x^2+y^2+|x|+|y|+\frac12\le Q.
\]
Using the supposed lower radius and (8),
\[
|x|+y\le Q-\frac12-m^2<\frac{13}{8},
\tag{9}
\]
with exact reserve
\[
\frac{13}{8}-\left(Q-\frac12-m^2\right)
=\frac{511}{57600}>0.
\]
Hence |x|<1/4.

The actual cap center has Y_E>=y>11/8. Thus
\[
|X_E|^2<M^2-(11/8)^2<(2/3)^2,
\]
whose final squared reserve is 167/4800. Moreover
\[
0\le Y_E-y<M-\frac{11}{8}=\frac{17}{120}.
\]
Consequently
\[
\begin{split}
|c_E-c_U|^2
&<\left(\frac23+\frac14\right)^2+
  \left(\frac{17}{120}\right)^2\\
&=\left(\frac{11}{12}\right)^2+
  \left(\frac{17}{120}\right)^2
=1-\frac{2011}{14400}<1.
\end{split}
\tag{10}
\]
Every actual unit contains the open radius-one-half disk about its
center. Two such squares with center distance less than one have
intersecting open interiors. Equation (10) contradicts the physical
U/E nonoverlap.

This proves (3) for the full side-mean interval (7), including both
original endpoints.

## 4. The entire diagonal-transmitter alternative

If w=sqrt(2), the two applications are opposite vertices of the actual
diagonal transmitter, so its center is exactly
\[
c_U=(l+w/2,h).
\]
Equations (5)--(6) give
\[
|c_U|^2<
(31/60)^2+(61/60)^2
<m^2,
\tag{11}
\]
with exact last reserve 3239/3600.

No endpoint concurrence or circle mask was used, and no diagonal
transverse application was set to a new value. The entire original
diagonal alternative is covered.

## 5. Whole five-load bare-C6 center-diameter consequence

Now let the entire selected positive component be the original bare
six-cycle
\[
U-S_1-S_2-S_3-S_4-S_5-U,
\tag{12}
\]
with exactly S_1,...,S_5 carrying positive total circle load and U
the true unloaded degree-two transmitter. Keep all five actual load
vectors, every physical circle mask and individual weight, every
selected normal and mean, and all three further physical squares.
Work throughout the original radius window
79/40<=R<=sqrt(1105)/16.

SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md and
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md apply to this entire original
component. They give the positive actual channel height and all
premises (1). Their full routing makes all four direct boundary-pair
pockets empty. CONTACT_RING_HOLE_AREA.md bounds the whole central
free union by 3sqrt(3)/2<3. Consequently at least one of the original
three extras lies wholly in the sole actual S_5--U--S_1 channel cap.
This supplies (2) for an actual E, so the complete original nine-square
domain satisfies (3).

**Corollary.** Every pair of the six actual core centers has distance
strictly less than three.

Here is the complete pair cover.

* U versus any S_i: (3)--(4) give
  |c_U-c_i|<=|c_U|+|c_i|<89/60+91/60=3.
* Two boundary bodies at path separation one or two on
  S_1--...--S_5: their actual physical contact path gives center
  distance at most sqrt(2) or 2sqrt(2), respectively, both below three.
  Each actual touching pair has center distance at most sqrt(2),
  because an actual common point lies within 1/sqrt(2) of each center.
* The boundary pairs (S_1,S_4) and (S_2,S_5): the complete physical
  three-edge boundary-path theorem
  BOUNDARY_THREE_EDGE_PATH_DIAMETER.md applies to their four actual
  circle-touching path bodies and gives distance less than three.
* The remaining boundary pair (S_1,S_5): use its real two-contact
  path S_1--U--S_5. The same center-to-common-point bound gives
  |c_1-c_5|<=2sqrt(2)<3. This pair is not placed under the
  three-edge boundary-path theorem, and its upper bound is not
  inferred from a channel reserve lower bound.

These alternatives cover all fifteen pairs. The corollary retains the
whole five-load force problem, both channel widths, every radial-mask
endpoint and all three original extras.

## 6. Exact limit of the result

The local theorem is degree-free at both channel endpoints. It may be
used in other components only after an actual whole extra in the stated
outward cap has been proved. Without such occupancy the transmitter
radius conclusion is not asserted.

The five-load corollary is a uniform necessary bound for every original
nine-square completion of (12). By itself it does not prove central
capacity one, channel-cap capacity one, or the impossibility of that
completion. A transfer of an inner-pair theorem must separately retain
its whole central localization and every geometric hypothesis.

All displayed comparisons are elementary exact rational inequalities.
No numerical pose, parameter grid, new coefficient certificate, Lean
compilation or CI is used.

