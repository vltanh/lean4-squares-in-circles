# Independent review: a D leaf and two other near-origin units

Date: October 27, 2026.

**Result: PASS** for the whole physical theorem in
D_LEAF_TWO_DISTINCT_NEAR_ORIGIN_UNITS_EXCLUSION.md, after correcting
the small epsilon=0 wording noted below. This is an independent
full-source mathematical review, not Lean verification.

The reviewer read the complete candidate, the full original radial-leaf
classification in RADIAL_BRIDGE_AND_LEAF_REDUCTION.md, and the complete
two-near-origin quarter argument in
INTACT_PETAL_TWO_DISTINCT_NEAR_ORIGIN_UNITS_EXCLUSION.md.
The new D-leaf witness and every new bound were checked directly.

## Scope and geometry

The genuine D leaf gives a side-interior radial contact on its root H,
hence O in int(H) and the full rectangle
[-s,r] times [a-1,a], 0<a<1. No positive force at H is omitted and
neither of the two other units is assigned a load or a degree.

At epsilon=0, each other unit contains O and immediately overlaps H.
The initial wording 'neither K_i already contains O' was a prose error;
it should say that each contains O and is therefore impossible.

When epsilon>0, the lower radius is genuinely R>sqrt(17)/2. The bounds
129/200<r<2/3 and 1/3<s<71/200 follow with the stated exact squared
comparisons. A chosen point within D_epsilon cannot be in int(H).
Since both horizontal distances exceed epsilon, one vertical side
must be shallow. The other vertical side cannot also be shallow.
After the one allowed global reflection, 0<a<=epsilon and H contains
the whole closed lower semicircle of radius 4/15.

## Quarter arcs and actual separating axes

For each original point x_i in the corresponding actual unit, choosing
each own-axis sign toward the center gives a real half-unit quarter.
The two selected orthogonal directions may be ordered counterclockwise
without changing that quarter. The complete closed arc with endpoint
offset delta=asin(1/16) lies in the unit's open interior because its
own-coordinate lower bound is 1/60-epsilon>0 and its upper bound
is 4/15+epsilon<17/60<1/2.

The arcs avoid the closed lower semicircle and are disjoint. Their
nonwrapping upper-semicircle order gives all three angle bounds (3).
In particular the difference of the two upward directions belongs to
[-2delta,2delta], not merely a one-sided interval. This validates the
cos(2delta)=127/128 and |sin(2delta)|<1/8 estimates used later.

Every actual square separating axis is an own side axis of one square.
Both upward axes are impossible because the two original projection
intervals contain [1/8,1/4] in their interiors. The rightward order on
one of the remaining axes follows from the two actual half-unit
segments: the reverse order would force a positive projection to be
at most a negative projection. Thus (5) retains the original axis,
whether it belongs to K_R or K_L.

The actual point on K_R's left face with the n-coordinate of x_R lies
in the original square. Using it in (5) gives
l_r>=-(144/127)epsilon>-12/635>-1/50. This is not a bound on a rotated
surrogate or a freely moved square. The lower own-coordinate bounds
and the half-unit upward extent give every inequality in (6)--(7).

## The new fixed witness

The original D leaf contains q=(r+1/4,1/5) strictly: its diamond norm
relative to its true center is 1/sqrt(2)-1/20. In the actual right-unit
axes, every projection estimate in (8)--(9) is valid on the whole
theta interval [-delta,3delta]. The lower second-coordinate reserve
is 193/8000-1/60=179/24000>0; the upper first-coordinate reserve is
49/50-229/240=31/1200>0. The remaining upper second-coordinate reserve
is 107/960>0. These strict inequalities put q inside the original
unit intervals in both coordinates.

The D leaf and K_R are distinct physical units because the former has
all norms at least r>epsilon while the latter meets D_epsilon. Hence
the same q lies in two different open square interiors, a contradiction.

## Consequences and limits

The result applies to arbitrary true degrees and physical circle masks
at H and the two near-origin units; it does not require physical contact
between them, common component membership, or a force equation at K_i.
Every genuine S/D leaf root meets D_epsilon, so the stated exclusion of
three distinct leaf roots with at least one D leaf is a valid whole-domain
corollary. It retains every original physical unit and every extra.

The proof does not exclude the all-S three-root family and does not by
itself close a coarse cell. No numerical sampling, scalar certificate,
Lean compilation, CI, new normal selection or reduction of a true degree
is used. No central roadmap or ledger was edited by this review.

