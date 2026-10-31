# Uniform central capacity for both four-load C6 orbits with a diagonal channel

Date: October 26, 2026.

**Status: accepted complete original-domain join after full independent
reviews in REVIEW_C6_FOUR_LOAD_DIAGONAL_CENTRAL_CERTIFICATE_REDUCTION_2026_10_26.md
and REVIEW_C6_PATH_DIAMETER_AND_FOUR_LOAD_JOIN_ROOT_2026_10_26.md.**
The two path dependencies also have a complete independent review in
REVIEW_C6_PATH_DIAMETER_EXTENSIONS_CERTIFICATE_REDUCTION_2026_10_26.md.
This source does not close either original four-load parent.

## 1. Exact two original orbits

Keep all nine actual interior-disjoint unit squares in
\[
79/40\le R\le\sqrt{1105}/16.
\]
The entire selected positive component is a bare six-cycle with exactly
four positively circle-loaded bodies and two original unloaded
degree-two transmitters. There are precisely two remaining unloaded
placements, after the already excluded adjacent placement.

Use these fixed actual cycle orders:

| Original orbit | Actual cyclic order | Positive block loads |
| --- | --- | --- |
| FOUR_ZERO_DISTANCE2 | \(U-A-V-B-D-C-U\) | \(A,B,D,C\) |
| FOUR_ZERO_DISTANCE3 | \(U-A-B-V-C-D-U\) | \(A,B,C,D\) |

In the first row U and V occupy vertices 0 and 2; in the second they
occupy 0 and 3. Every original circle resultant, force, support owner,
true application mean, physical circle mask and individual zero weight
remains. In particular the isolated load A in the first row keeps both
of its original channel forces. All three additional physical squares
remain, including every repeated exterior allocation.

**Theorem.** If at least one of the two actual transmitter widths is
\(\sqrt2\), then all six actual core centers have mutual distances
strictly below three. The whole central free union consequently contains
at most one of the three extras.

The same central conclusion holds, for either width pattern, in the
strict radius range \(R<\sqrt{17}/2\). The equality radius is included
in the first assertion whenever an actual diagonal channel is present.

## 2. Complete pair cover for zero distance two

One- and two-edge pairs have center distances at most \(\sqrt2\) and
\(2\sqrt2\), respectively, using their actual contact points. This
covers twelve of the fifteen center pairs without any force equation.

The remaining opposite pairs in \(U-A-V-B-D-C-U\) are \(U,B\), \(V,C\),
and \(A,D\).

| Actual endpoint pair | Unchanged physical path | Complete metric theorem |
| --- | --- | --- |
| \(U,B\) | \(U-C-D-B\) | TWO_MIDDLE_BOUNDARY_PATH_DIAMETER.md: the two middle bodies C,D are physical boundary bodies |
| \(V,C\) | \(V-B-D-C\) | TWO_MIDDLE_BOUNDARY_PATH_DIAMETER.md: the two middle bodies B,D are physical boundary bodies |
| \(A,D\), when V is diagonal | \(D-B-V-A\) | LOADED_INTERMEDIATE_DIAGONAL_PATH_DIAMETER.md at true loaded intermediate B |
| \(A,D\), when U is diagonal | \(D-C-U-A\) | LOADED_INTERMEDIATE_DIAGONAL_PATH_DIAMETER.md at true loaded intermediate C |

At least one of the last two rows is available under the theorem's
width premise. If both are available, either suffices.

The first two rows do not assume that the endpoint U or V physically
touches the circle. The last two rows retain the proper true
degree-two concurrence at B or C and the original diagonal channel.
They do not treat the loaded A or D as an unloaded intermediate body.
The entire simple cycle has four loads, so the nonparallel and
positive-channel-height hypotheses of that local theorem hold.

Thus all fifteen distances are strictly below three.

## 3. Complete pair cover for zero distance three

Again twelve one- and two-edge pairs are automatic. The remaining
opposite pairs in \(U-A-B-V-C-D-U\) are \(U,V\), \(A,C\), and \(B,D\).

| Actual endpoint pair | Unchanged physical path | Complete metric theorem |
| --- | --- | --- |
| \(U,V\) | \(U-A-B-V\) | TWO_MIDDLE_BOUNDARY_PATH_DIAMETER.md at the two actual boundary middle bodies A,B |
| \(A,C\), when V is diagonal | \(A-B-V-C\) | LOADED_INTERMEDIATE_DIAGONAL_PATH_DIAMETER.md at B |
| \(B,D\), when V is diagonal | \(D-C-V-B\) | LOADED_INTERMEDIATE_DIAGONAL_PATH_DIAMETER.md at C |
| \(A,C\), when U is diagonal | \(C-D-U-A\) | LOADED_INTERMEDIATE_DIAGONAL_PATH_DIAMETER.md at D |
| \(B,D\), when U is diagonal | \(B-A-U-D\) | LOADED_INTERMEDIATE_DIAGONAL_PATH_DIAMETER.md at A |

Either actual diagonal supplies both required loaded-intermediate paths.
Their intermediate bodies have their original degree two and both
positive forces. No endpoint degree or extra force is changed.

This proves the full six-center metric bound in the second orbit.

## 4. Original central enclosure and complete allocation consequence

SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md and
SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md apply to each entire four-load
cycle. SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md then gives the actual
central-plus-two-channel-region cover. Every direct loaded-loaded
exterior pocket is empty. The two surviving exterior regions use the
unchanged U and V channel applications and their entire means.

Write \(n_{\rm in},n_U,n_V\) for the numbers of extra squares in the
whole central free union and the two actual exterior channel unions.
Any additional physical contacts may subdivide those unions but do
not remove or reassign an extra. The full original accounting is
\[
n_{\rm in}+n_U+n_V=3.
\tag{1}
\]

The actual physical contact ring has winding one on every central
extra interior, with the same compact-interior weak-junction convention
as the routing source. All six ring squares lie in the disk of squared
radius at most \(1105/256\), and Sections 2--3 prove all actual center
pair distances below three. Hence
SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md applies to that
unchanged ring and gives
\[
\boxed{n_{\rm in}\le1.}
\tag{2}
\]
The theorem permits a nonconvex center chain and does not introduce a
convex-hull edge-length premise.

Consequently the complete remaining three-extra allocation cover in
this width family is
\[
\begin{array}{c|c}
n_{\rm in}&(n_U,n_V)\\ \hline
0&(0,3),(1,2),(2,1),(3,0)\\
1&(0,2),(1,1),(2,0).
\end{array}
\tag{3}
\]
In particular no cap occupancy was assumed in order to prove the metric
bound or (2). Equation (1) now forces at least two exterior extras,
but their exact locations and repeated occupancy remain in (3).

For completeness, if \(R<\sqrt{17}/2\), every actual center has norm
strictly below \(3/2\), since \(r^2+r+1/2\le R^2<17/4\).
All pair distances are then below three for either transmitter-width
pattern, so the same original routing and theorem give (2)--(3)
without a diagonal premise.

## 5. Exact frontier retained

This proves one common central result across both remaining four-load
orbits, all original physical masks and all actual diagonal placements.
It adds no computational certificate or finite parameter subdivision.

A side-normal channel with a physically radial endpoint may additionally
use RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md, and a diagonal incident
to such an endpoint may use
RADIAL_BOUNDARY_DIAGONAL_CHANNEL_RADIUS_RESTRICTION.md. Those conclusions
must be applied to the same actual cap and their stated radius domains;
they are not presumed here for an arbitrary unique endpoint.

The seven allocations (3) still require their joint exterior
obstruction. In the all-side family at \(R\ge\sqrt{17}/2\), the present
source also leaves the additional center-diameter work explicit.
It does not claim that an arbitrary mixed side path has diameter below
three or that an occupied cap exists at each transmitter.

Accordingly the original gates
M6.B6.C6.FOUR_ZERO_DISTANCE2.CAPS,
M6.B6.C6.FOUR_ZERO_DISTANCE3.CAPS,
M6.B6.C6.FOUR_ZERO_DISTANCE2 and
M6.B6.C6.FOUR_ZERO_DISTANCE3 all remain open.
The original all-positive-load and all-three-extra contract is
unchanged. No shared ledger, Lean compilation or CI is used here.

