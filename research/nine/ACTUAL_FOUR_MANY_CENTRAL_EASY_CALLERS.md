# Complete many-central occupancy callers already supplied by the accepted caps

November 2, 2026. Hand case selection for an actual cone four-chain and
a selected outsider horizontal cone three-chain. This document proves
the complete cases listed below; it does not label the remaining
two-upper/one-lower or three-upper/one-lower cases closed.

## 1. Normalized setting and common inputs

Suppose a strict counterexample is expanded to the closed Q-disk as in
the accepted actual-four normalization. The four original main squares
retain their actual horizontal chain and consecutive horizontal cone
comparisons. Their adjusted endpoint span is

\[
                     D=x_3-x_0-h_0-h_3>2.
\]

Count outsiders in the left side \(x\le-l\), central strip
\(|x|<l\), and right side \(x\ge l\), where \(l=29/60\).
The side-capacity theorem allows at most two outsiders in each side.
Counts in this proof refer to this normalized physical configuration.

Write the selected cone triple as \(L<_cP<_cR\). The common routing
theorem permits one vertical reflection after which P is above both
inner mains, L is above the left main and R above the right main.
Every central outsider is either above both inner mains or below both.
If R is central then L is a genuine left-side unit and

\[
              x_P<0<x_R,\qquad y_L>27/40>3/5.   \tag{1}
\]

All reflected statements are available. We repeatedly apply the widened
five-square cap to three distinct original upper outsiders A,U,B with

\[
 x_A\le0\le x_B,\quad |x_U|\le l,
 \quad y_A,y_B\ge3/5,\quad y_U-h_U\ge1/10.     \tag{2}
\]

That cap gives \(D\le2\), contradicting the normalized span. Original
pairwise nonoverlap and corner constraints are inherited by the chosen
three outsiders and original two endpoints.

Two additional accepted inputs are used exactly in their stated scopes:

* The upper-column theorem: two original units with centers at heights
  at least \(3/5\) have horizontal center gap strictly greater than l.
* The upper-central half-width replacement theorem: two upper central
  outsiders with horizontal center gap at most \(1/2\) have a higher
  member whose whole floor is greater than \(2807/24000>1/10\).

Call a central unit **good** if its whole floor is greater than \(1/10\).
A good upper unit has center height strictly greater than \(3/5\).

## 2. At most two upper central units in either closed half-plane

Every upper central outsider has center height strictly above

\[
                  -139/120+59/60=-7/40,
\]

by the original main cone bound and its own-half-plane central clearance.
Its height is strictly below \(91/60\). The total available center-height
span is therefore less than \(203/120\).

Three centers in one closed horizontal half of the central strip have
pairwise horizontal gaps at most l. Order them by center height. Their
two adjacent vertical gaps are each at least \(\sqrt{1-l^2}\), by
the original disjoint radius-one-half disks. But

\[
 1-l^2-(203/240)^2=587/11520>0
\]

would make their total vertical span exceed \(203/120\), a contradiction.
Thus there are at most two upper central units in either closed
half-plane. For three upper central units, at least one is strictly
negative and at least one strictly positive. For four, exactly two
are strictly negative and two strictly positive.

Three upper central units always include a good one: order their
horizontal coordinates. One adjacent horizontal gap is at most
\(l<1/2\), so apply the half-width replacement theorem. Two upper
central units in the same closed half-plane also supply a good higher
member by that theorem.

## 3. Count (1,4,0): two complete vertical splits

The selected triple must use the sole left-side outsider L, a negative
central P and a positive central R. Both selected central units are
upper, and (1) supplies a high left shoulder.

### 3.1. Two upper and two lower central outsiders

The central singleton-floor theorem applied to either upper unit and the
two lower originals shows that both upper units are good. In particular
P is good and R is a high right shoulder. The original triple L,P,R
satisfies (2), closing this entire split.

### 3.2. Four upper central outsiders

Section 2 gives exactly two central units on each strict horizontal side.
Choose the higher negative unit U and the higher positive unit B. Both
are good by the half-width replacement theorem. The original L from
(1), U and B satisfy (2). This closes this entire split.

The split of three upper and one lower central unit is not claimed here.
The mirror count (0,4,1) is covered by horizontal reflection.

## 4. Count (2,3,0): all three central outsiders upper

There is no right-side outsider. Thus the selected R is central, P is
negative central and L is a high left-side shoulder by (1). The full
left side's main is either bottom or middle, since its selected L is
above that main.

If the main is bottom, its original zero-side outsider S is above the
main and has \(y_S<7/16<3/5\). The low-side floor theorem makes
every upper central unit with nonpositive x good. In particular P is
good. The upper-column theorem permits at most one such unit, so the
other two central originals are strictly positive.

If the main is middle, \(y_1>-7/20\). Every upper central unit
with nonpositive x has center height greater than
\(-7/20+59/60=19/30>3/5\). Again there is at most one, namely P.
The cone gap to the central R gives
\(x_P+g_P\le l-g_R<2/15<J\), so the accepted coupled cone-loss
theorem makes P good.

In either case the two other central outsiders are positive. Their
higher member B is good by the half-width replacement theorem. Then
L,P,B satisfy (2). This closes the entire all-upper central split for
this occupancy, and its horizontal reflection.

## 5. Count (1,3,1): all three central outsiders upper

Let A and B be the sole left and right side outsiders. At least one is
above its own main, since the selected cone triple must meet a side.

### 5.1. Both side outsiders above their respective mains

If both side centers are at least \(3/5\), choose any good central
unit from Section 2. Then A,U,B satisfy (2).

Otherwise reflect horizontally so \(y_A<3/5\). The low-side floor
theorem makes every nonpositive central unit good. By upper-column
separation, there is at most one such unit. Section 2 now forces exactly
one strictly negative central unit N and two strictly positive ones.
N is good, and the higher positive unit H is good by replacement.

B must have center height at least \(3/5\): if it were low, both
positive central units would be good by the right low-side theorem,
contradicting upper-column separation. Thus N,H,B satisfy (2), with N
as the negative shoulder, H as the central unit and B as the positive
shoulder. The units are distinct originals.

### 5.2. One side outsider below its main

Reflect horizontally so A is above M1 and B below M2. Common routing
shows that B is not a selected endpoint. Therefore the selected endpoint
on the right is central and A=L. Equation (1) gives \(y_A>27/40\).

The one-sided main-height theorem applied to B gives
\(y_2>-7/20\). Every nonnegative upper central unit therefore has
height greater than \(19/30>3/5\). Upper-column separation permits
at most one, while Section 2 forces at least one. Thus there are exactly
two negative upper central units and one positive, the latter being the
selected R. The higher negative unit U is good by replacement. The
three originals A,U,R satisfy (2).

Both side outsiders cannot be below their own mains, since some selected
side endpoint is above its own main. This exhausts the all-upper central
split in count (1,3,1).

## 6. Count (1,3,1): one upper and two lower central outsiders

The unique upper central unit is P. Since a selected central endpoint
would also be upper, both selected endpoints must be the two side
outsiders A=L and B=R; both are above their own main.

The central singleton-floor theorem makes P good. Neither A nor B can
have center height below \(3/5\), by
`LOW_SIDE_WITH_TWO_LOWER_CENTRALS_EXCLUSION.md`, applied to the two
original lower central units. Thus A,P,B satisfy (2). This closes the
entire one-upper central split.

The count (1,3,1) split of two upper and one lower central unit remains
outside this document's closure claims.

## 7. Count (0,5,0) is impossible already from the selected cone span

All three selected outsiders would be central. Their horizontal span
would be at most \(29/30\), whereas the two cone gaps give span at
least \(\sqrt2\). This is impossible.

## 8. Scope and arithmetic audit

Every closure above is a caller to complete accepted physical theorems.
No new side-frame restriction or separating-axis owner is introduced.
`verify_many_central_caller_arithmetic.py` reconstructs the finite
rational comparisons used here and in the low-side/two-lower theorem.
The latter theorem uses the separately reviewed complete two-central
height-cap certificate; no sampled optimizer output enters this case
selection proof.
