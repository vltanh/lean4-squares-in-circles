# Complete (2,2,1) closure when the full-side main is at the bottom

November 2, 2026. Complete original-nine hand caller. The scalar inputs
have exact rational arithmetic audits; the two-low-mains input and the
widened five-square terminal have complete independently replayed finite
tables. No Lean or CI.

Put

\[
 Q=1105/256,\quad l=29/60,\quad u=13/12,
 \quad\rho=91/60,\quad J=23/150,\quad A_0=18911/59520.
\]

## 1. Exact scope and normalization

Suppose a strict counterexample \(q<Q\) has nine original physical
unit squares, four of which form both an actual horizontal projection
chain and a horizontal center-cone chain. Suppose its five outsider
column counts are \((L,C,R)=(2,2,1)\), and the left inner main M1
is below both original left-side outsiders. The left/right-reflected
statement treats \((1,2,2)\); vertical reflection treats a full-side
main above both outsiders.

Common expansion of all original centers, with the frames retained,
normalizes the largest squared corner norm to Q and yields closed-disjoint
original squares with strict adjusted endpoint span

\[
                       D=x_3-x_0-h_0-h_3>2.
 \tag{1}
\]

Both original left outsiders and the original right outsider stay in
their side bands. A central outsider cannot enter the full left column,
since each side has outsider capacity two. If either enters the right
column, the resulting count is \((2,1,2)\), already excluded by
`ACTUAL_FOUR_FULL_SIDE_OCCUPANCY_CLOSED_HAND_PROOF.md`. Both cannot enter,
by the same side capacity. Therefore it suffices to work with normalized
count \((2,2,1)\), with the same full-side marker order. No unproved
count invariance is assumed at a central/side boundary.

Write S,H for the lower and higher original left outsiders, R for the
original right outsider, and F,G for the two central outsiders. All five
are retained in the argument. The full-side extreme-main theorem gives

\[
                            y_1<-3/5.
 \tag{2}
\]

`ZERO_SIDE_PROXY_EDGE_AND_TOP_HAND_PROOF.md` gives

\[
 l\le Z=-x_S<\zeta=2211/4000,\quad -113/600<y_S<7/16,
\]

\[
 Z-g_S<J,\qquad y_S+g_S>A_0,
 \qquad y_H>367/600>3/5.
 \tag{3}
\]

The original central units are each above both inner main centers or below
both; the actual-cone-four central routing theorem excludes every between
placement. The right outsider has a strict vertical order relative to M2
by its same-half-plane clearance.

Our terminal is always the accepted widened five-square cap: choose three
distinct original squares L,U,V such that

\[
 x_L\le0\le x_V,\quad |x_U|\le l,
 \quad y_L,y_V\ge3/5,\quad y_U-h_U\ge1/10.
 \tag{4}
\]

Together with the original endpoints, the cap gives D<=2, contradicting
(1). It does not require V to be a side-column outsider, or require a
selected short-chain edge or separator owner.

## 2. A basic central-count exclusion

There cannot be two central outsiders below both inner mains. Section 2
of `ACTUAL_FOUR_MIXED_FULL_SIDES_LOWER_CENTRAL_EXCLUSION.md`, applied to
each one with (2), gives for their vertically reflected centers

\[
                       1/3<X\le l,\qquad
                       3/5+15/31<Y<\rho.
\]

Thus their squared center distance is strictly below

\[
 (l-1/3)^2+(\rho-3/5-15/31)^2
       =(3/20)^2+(161/372)^2<1.
 \tag{5}
\]

Their original open radius-one-half disks would overlap. Consequently the
two central outsiders are either both upper, or one upper and one lower.
This uses both original units, with no virtual replacement.

## 3. The right outsider is below its inner main

Suppose \(y_R<y_2\). The one-sided main-height theorem gives

\[
                              y_2>-7/20.
 \tag{6}
\]

Section 6 of `ACTUAL_FOUR_MIXED_FULL_SIDES_LOWER_CENTRAL_EXCLUSION.md`
uses (2), the retained main cone comparison, and this original right lower
outsider R to exclude every central unit below the left main. Thus both
F and G are upper.

For each of F and G separately, the shared-frame floor argument in
Sections 5.1--5.4 of
`ACTUAL_FOUR_FULL_SIDE_OCCUPANCY_CLOSED_HAND_PROOF.md` applies to the same
left zero S and the actual M2 inset. That argument requires only (3), the
correlated M2 horizontal bounds, (6), and the central unit above M2. In
particular, its use of the opposite main height is solely the lower bound
\(y_2+g_2>83/620\); no upper bound on y2 or second right outsider is
used in that floor argument. It proves

\[
                         y_F-h_F>1/10,
                         \qquad y_G-h_G>1/10.
 \tag{7}
\]

Their center heights consequently exceed three fifths. The accepted
upper-column separation theorem gives horizontal center gap greater than
l. Because both centers are in \((-l,l)\), they must have opposite
strict horizontal signs. Denote them by Cminus and Cplus in this order.
Taking L=H, U=Cminus, V=Cplus supplies (4), and the terminal contradiction
closes the entire right-below branch.

## 4. The right outsider is above its main but below three fifths

Suppose \(y_R>y_2\) and \(y_R<3/5\). The application in Section 4 of
`TWO_LOW_MAINS_CENTRAL_EXCLUSION_HAND_TABLE.md` uses (2) and the original
R to exclude every central outsider below both mains. Thus both central
units are upper.

For any one of them with x<=0, apply
`LOW_SIDE_UNIT_FORCES_SAME_SIDE_CENTRAL_FLOOR.md` to the original left
helper S, after horizontal reflection. Its premises hold by (3) and the
full-side bottom order. For one with x>=0, apply the same theorem to the
original low right-side R. Each central unit therefore has whole floor
strictly above one tenth. As in Section 3, upper-column separation forces
them to opposite horizontal sides, and L=H, U=Cminus, V=Cplus supplies (4).
This closes the entire low-right branch, including either sign of either
central center and x=0.

## 5. The right outsider is at least three fifths high

It remains that \(y_R>y_2\) and \(y_R\ge3/5\). We already have both
high shoulders H,R of opposite horizontal signs. It suffices to find one
original upper central unit whose whole floor exceeds one tenth.

### 5.1. Both central units are upper

If either upper central unit has x<=0, the left low-side extraction with
S proves the required floor immediately.

Otherwise both central units have positive x-coordinates in (0,l), so
their horizontal gap is below l<1/2.
`UPPER_CENTRAL_PAIR_HALF_WIDTH_REPLACEMENT_HAND_PROOF.md` then gives the
higher original central unit's whole floor above

\[
                        2807/24000>1/10.
\]

Taking that unit as U and H,R as the two shoulders gives (4). Equal central
heights would already violate the two original radius-one-half disk
constraints and are covered by the replacement theorem.

### 5.2. One central unit is upper and the other is lower

Write F for the upper central and G for the lower central. If xF<=0,
the left low-side extraction with S again gives the required floor.
Suppose xF>0. The lower central unit G and (2), through the complete
two-low-mains theorem, force

\[
                            y_2>-119/310.
 \tag{8}
\]

The physical central clearance and \(g_2>15/31\) imply

\[
 y_F>y_2+59/60>223/372,
 \qquad y_2+g_2>1/10.
 \tag{9}
\]

Assume its whole floor were at most one tenth. The complete original-square
exclusion
`LOW_FLOOR_RIGHT_CENTRAL_AND_HIGH_RIGHT_SHOULDER_EXCLUSION.md` applies to
S,F,M2,R, with (3), (9), and the present high-right assumption. Its exhaustive
physical separator argument rules this out. Thus F's floor is above one
tenth, and H,F,R supply (4).

Section 2 excluded the only other central height pattern. This completes
the high-right branch and the full original-nine theorem.

## 6. Exhaustiveness and dependency boundary

The right outsider is either below M2, above M2 below three fifths, or above
M2 at least three fifths. Those three complete alternatives are Sections
3--5. Within the last alternative, Section 2 reduces the central heights
to the two patterns treated in Section 5. Every central horizontal sign
and every shared boundary is retained. The final contradiction in each
case concerns the same original endpoint span (1).

The proof does not use either designated short-cone edge. It therefore
excludes the whole strict actual-cone-four family with outsider count
(2,2,1) whose full-side main is lowest, and its reflected highest/full-right
versions. The full-side-middle family is a separate caller. No whole-mask
closure beyond this stated occupancy scope is asserted here.

The new hand inputs are the low-floor right-central exclusion and the
recovered universal half-width replacement theorem. Each has a companion
exact standard-library arithmetic checker and saved PASS report. The
accepted two-low-mains theorem has its complete 308-leaf certificate and
independent dyadic replay. The accepted widened terminal and all prior
side/main-height, low-side, upper-column, and full-side inputs retain their
own independent review and replay records. The two additional rational
comparisons in (5) and l<1/2 are checked by
`verify_full_side_bottom_221_arithmetic.py`.
