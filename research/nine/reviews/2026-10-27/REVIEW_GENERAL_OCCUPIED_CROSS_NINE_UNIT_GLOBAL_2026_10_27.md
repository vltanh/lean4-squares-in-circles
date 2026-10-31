# Independent review: every actual occupied cross has capacity at most eight

Date: October 27, 2026.
Reviewer: global-closure agent, separate from the source author.

**Decision: ACCEPT the entire theorem and its stated original-geometry
corollaries, without mathematical or exposition corrections.**

Reviewed source:

`GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md`

SHA256:
`c3e0979e5baacda8a117572ad9e337b0ec4e21a56bbcf9bb25f7af33481e92a5`.

I read the complete 597-line source, including all eight exact positivity
tables, and the entire force-free dependency
`CHORDED_HEXAGON_OCCUPIED_CROSS_OPPOSITE_QUADRANT_EMPTY.md`, pinned at
`c824dd96ba8b9505de653248b9bd99bbf429eb706f84f5288d58657db6f9abf7`.
The dependency also has the separate full acceptance recorded in
`REVIEW_OCCUPIED_CROSS_OPPOSITE_QUADRANT_ROOTED_BLOCKS_2026_10_27.md`.

## 1. Exact accepted statement and absence of force hypotheses

For actual closed unit squares with pairwise disjoint open interiors in
one disk with squared radius at most 1105/256, the presence of the five
actual aligned cross squares implies that the entire packing has at
most eight units. The statement imposes no force, load, degree, boundary
arm, genericity, selected-normal, or contact-mean hypothesis. It retains
all orientations and positions of every additional unit.

The proof never uses an equilibrium equation. Its weighted variance is
an identity for three actual points in the containing disk; its weights
are not new physical circle loads or an auxiliary physical stress.
The point evaluations used to bound the variance below are algebraic
relaxations, not motions or assumed additional packings.

## 2. Actual cross, variance, and full separating-axis cover

The stated maximum squared distance from the containing-circle center
to the eight outer cross vertices is exact. Its strict coordinate
bound 31/60 and the strict unit-center radius 91/60 each have the stated
31/57600 reserve against 1105/256. The farthest-corner inequality
r^2+r+1/2 is also valid relative to any fixed actual cross vertex.

I independently expanded the three-point variance: conditional on the
two square corners, their mean is c+n/2+tau*m and their variance is
1/4-tau^2. Combining their total mass 1/2 with the cross vertex of mass
1/2 gives exactly equation (4). Taking the larger of the two signed
choices gives equation (5). Both the signed and absolute-value forms
are strictly coordinatewise increasing on X,Y>=1, including the
absolute-value junction and both tau endpoints.

The SAT reduction covers every actual orientation. In the positive
center quadrant, negative cross axes and southwest own normals cannot
separate. A mixed-sign own separator implies the corresponding ordinary
cross-axis separator by the displayed nonnegative expression; axial
own normals are already ordinary alternatives. The only remaining
own separator has both coordinates strictly positive. The fixed cross
rectangles are actual unions of its units, so any extra is disjoint
from their interiors, including across their internal unit seams.

The point-to-square diameter obstruction applies whenever x>=2 and
y>=1/2, with the coordinates interchanged as required. The weak
endpoint y=1/2 is legitimate in the later algebraic evaluations. The
strict reserves are 53/4-(18/5)^2=29/100 and
347/20-4(1105/256)=27/320.

## 3. Complete upper coordinate bound

For ordinary vertical separation, the actual coordinate lower bounds
give precisely P_tau. The rational parameterization covers the entire
closed orientation interval. The three signed tau choices and their
closed intervals cover it without a gap.

For a genuine positive own separator, the lower rectangle corner has
normal projection strictly below C. The segment from that corner to
the actual point therefore gives a coordinatewise smaller point on
the support line. On that line, the feasible W interval is exactly
the one in (14); minimizing |W| is valid for every variance choice.

For 0<a<=7/8, I checked the derivative and endpoint estimates proving
W_min>0. The evaluation at X=X0 and the conversion to H_tau preserve
the sign of W, so a signed expression is not incorrectly substituted
for the larger absolute-value expression. The transformed parameter
lies in (0,3/5), and the three closed Bernstein intervals exhaust it.

For 7/8<=a<=99/100, concavity and both exact endpoint bounds give
U0>41/10. The reserve is exactly 71/6400 after applying tau=0. For
99/100<=a<1, b<1/7 gives W_max<0, and its endpoint corresponds to
y=1/2, x=3/2+1/(2a)>=2. Equation (7) gives a valid algebraic lower
bound for F_(1/2), so this last case requires no physical square at
the evaluation point. All weak common endpoints are included.

## 4. Complete lower coordinate bound

The horizontal and vertical ordinary separators are already impossible
when 1/2<x<=59/60. For the remaining own separator, the line reduction
at fixed X stays in Y>1. Minimizing over the full closed relaxation
1<=X<=89/60 is therefore legitimate.

The first range a<=1/4 has aC<=15/16 and its lower endpoint evaluation
has squared center displacement at least 53/4. The middle range uses
the two stated strict concavity endpoints; (33/8)^2+1/4=4Q exactly,
and the preceding strict endpoint inequalities supply the required
strict contradiction. The last range uses the exact second derivative
and g'=3/b^5 to obtain aC>=3/2>89/60. Thus W has the stated negative
sign throughout the relaxed interval, and X=89/60 is the correct
minimizing endpoint. The two final polynomial intervals cover the
whole actual transformed range. The harmless closed endpoint z=1
does not erase the positive denominator on any actual orientation.

Coordinate interchange now supplies both lower and upper coordinate
bounds in every strict corner region. Their squared diameter is
5618/5625, with reserve 7/5625 below one, so the incircle separation
really gives capacity at most one per corner.

## 5. All exact polynomial and Bernstein checks

Using exact rational arithmetic, I independently reconstructed the six
numerator polynomials directly from P_tau, H_tau, and G, before
comparing them with the source's coefficient lists. All six identities
match exactly.

I then applied the affine power-basis substitution and the stated
power-to-Bernstein conversion independently on each of the eight
closed intervals. All 60 printed Bernstein coefficients match exactly
and are strictly positive: five each in A.1--A.3 and nine each in
A.4--A.8. These checks certify complete continuous intervals, not a
sample of orientations.

The exact arithmetic also checks 26 strict rational reserves used in
the geometric and parameter splits, plus the three endpoint identities
(33/8)^2+1/4=4Q,
(91/60)^2-(89/60)^2=1/10, and
(2/3)^2+(1/30)^2=401/900.
In particular, both square-root comparisons behind the lower
concavity endpoint and the derivative inequality g(5/12)>1 pass by
strict rational squared comparisons.

The reproducible independent arithmetic script is the scratch file
`GLOBAL_CLOSURE_VERIFY_GENERAL_CROSS.py`. The mathematical proof and
all rational certificates remain completely present in the reviewed
source itself; this review does not replace them by a script result.

## 6. Axial regions and completion count

The incircle distance to the actual solid rectangles proves that an
extra center is either a strict corner center or lies in one of the
four closed axial regions. Centers on x=+/-1/2 or y=+/-1/2 are included
in that cover.

If no axial region is occupied, the fully reviewed opposite-quadrant
lemma leaves at least one empty corner for every actual circle offset,
including offsets with a zero coordinate. The other three corners
each have capacity one.

If a north axial center exists, v>29/60. Opposite axial occupancy is
impossible immediately; either adjacent axial direction would violate
the exact cross-radius bound. Every north axial center lies in the
same rectangle of width 2/3 and height 1/30, so there is at most one.
The two southern corners violate the true unit-center radius by the
stated 247/3600 reserve. The two northern corners each still have
capacity one. Rotations give the other three initial axial choices.
This exhausts every actual extra center and proves the full count.

## 7. Original geometric callers and retained limits

I checked the occupied-four-ring equality and its degree-independent
scope in `FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md`, Sections 1--2.
That equality identifies five actual cross units without assuming
circle loads on ring vertices. The present theorem therefore makes
every actual four-ring whole-unit region empty in a nine-packing.

I also checked the restricted physical embedding argument in Section 1
of `GLOBAL_CLOSURE_SPANNING_K23_BOUNDARY_AND_TERMINAL_EXCLUSIONS.md`.
Restricting the existing physical embedding to an actual K_(2,3)
preserves its actual edges and routing: an outer four-cycle encloses
its fifth actual body and gives the occupied cross. The present
theorem consequently excludes an actual positive K_(2,3) subgraph at
arbitrary higher degrees and with no circle-load premise. This use of
Section 1 does not depend on that source's later, weaker cross-capacity
caller, so it introduces no circular dependency.

No five-sided bounded region, remaining exterior completion, whole
coarse parent, or original graph/load gate is closed just by this
review. The source's stronger four-ring and K_(2,3) conclusions are
accepted at precisely the full stated physical scopes. No shared
ledger, remote branch, Lean file, or workflow was changed.
