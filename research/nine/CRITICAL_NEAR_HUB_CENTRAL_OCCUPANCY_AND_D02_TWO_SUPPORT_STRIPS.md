# Critical near units force central occupancy and two actual D02 support strips

Date: October 28, 2026 UTC. Author: mixed_capacity_review continuation.

**Status: complete proposed uniform hand reductions, submitted for full
root and separate independent review. No whole original gate is closed.**
Root proposed combining the critical near-unit count, central capacity and
the complete one-hub pocket theorem. Root also identified the outer-hub-arc
distance export to check in that theorem's full proof. The author checked
that complete proof, supplied the exact occupancy and boundary-band joins,
the short-segment lemma, and the two-strip and unique-tip consequences
below. A root adoption is consequently an integration/author check;
a separate reviewer is required for independent certification.

Every statement retains the original nine physical units, unchanged circle
origin, actual frames, full selected force and torque equations, true
positive degrees, original normals, actual applications and shared means,
all physical circle corners and individual zero coefficients. No numerical
pose, coefficient packet or additional computational certificate is used.

Put

    Q=1105/256,
    delta=sqrt(2*(2+sqrt(2)))*(sqrt(1105/512)-1)-1,
    kappa=sqrt((2-sqrt(2))^2-delta^2).

The complete critical inner-arc theorem gives

    1/5<delta<29/128<1/4.

The following exact comparisons will be used:

    1/2<kappa<3/5<1-delta.                            (1)

Indeed the elementary bound sqrt(2)<283/200 gives

    (2-sqrt(2))^2-1/4>9/100,
    kappa^2-1/4>9/100-(29/128)^2
                  =15839/409600>0.

For the upper bound, kappa<2-sqrt(2)<3/5 follows from sqrt(2)>7/5.
All square roots have positive arguments before they are compared.

## 1. Complete one-hub component and the explicit whole-extra partition

Retain any actual nine-square packing in 2<=R<=sqrt(Q). Suppose an entire
positive component has exactly the form

    H, B_1,...,B_k, 3<=k<=6;
    B_i B_(i+1), 1<=i<k;
    H B_1, H B_k, and any subset of H B_i for 1<i<k.

H is unloaded. Every B_i has positive total circle load. The actual exterior
face order is H,B_1,...,B_k,H, with the original compatible physical
embedding. All original hub spokes and all original boundary-path forces
remain. In particular the actual endpoints have true positive degree two;
there is no omitted force at an endpoint or from H to another component.

Let Omega be the actual closing exterior circle pocket through H between
B_k and B_1. Assume the caller has proved the following entire physical
allocation: each of the other 8-k units lies wholly, in the sense of its
open interior, either in Omega or in an actual remaining free union C.
Assume C has capacity at most one whole unit, counting all its components
together. This allocation and capacity are genuine hypotheses, not inferred
from a picture or from the centers of the completing units.

**Theorem A.** Exactly one completing unit E_0 lies in C, and

    dist(O,H)<delta,    dist(O,E_0)<delta.             (2)

The other 7-k completing units all lie in Omega. The seven actual units
consisting of those 7-k units and the k boundary bodies all have distance
strictly greater than1/4 from O. H and E_0 are physically circle-clear.
Thus there are exactly two delta-near units and exactly seven quarter-clear
units, with no other actual square in the intervening clearance range.

**Zero-capacity corollary.** If the same entire allocation has capacity
zero in C, the whole stated component is impossible in the nine-unit
packing, with no further closing-pocket capacity estimate required.

The arbitrary-subset-of-spokes scope is literal. A caller cannot delete
an actual positive force to create it. Central capacity alone does not
supply the required exterior allocation.

## 2. Complete proof of the near-unit count and forced central occupancy

The critical theorem, Section 11, applies before any force certificate:
at least two distinct original units have distance strictly less than
delta. It also proves that no actual unit contains the entire closed
disk D_delta, including a side-tangent containment.

Every actual boundary body has distance at least R-sqrt(2)>1/4 from O.
Use any one of its actual circle corners and the whole unit diameter;
the argument does not require that corner's coefficient to be positive.

The complete GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md applies to the
entire component above. Every whole completing unit in Omega therefore
has distance strictly greater than1/4. Since delta<1/4, neither a B_i
nor a completing unit in Omega can be one of the two critical near units.

Only H and the completing units in C remain possible. The capacity-one
hypothesis permits at most one unit of the latter kind. Consequently
H and one actual E_0 in C must both be near, and that E_0 is unique.
Every other completing unit is in Omega by the whole allocation premise.
The exact count is k+(7-k)=7 far units and the two near units in(2).
Their physical circle-clearance follows from the same boundary-distance
bound; zero load is not substituted for physical clearance.

If C has capacity zero, H would be the only possible near unit, contrary
to the critical theorem. This proves the corollary at its whole stated
component scope. For example it applies uniformly to a completely
triangulated one-hub boundary-path component whenever the full actual
face/exterior allocation is supplied: each triangular central free face
has capacity zero, every direct boundary-pair exterior pocket is empty,
and all remaining extras are in Omega. The complete physical triangle
area and weak-junction arguments, rather than the abstract graph alone,
provide those premises.

There is also one useful joint angular budget. On the same radius-5/4
circle, each of the seven far units has an actual open-interior arc
longer than pi/4 by the complete force-free inner-arc theorem. Their
intersections are disjoint. Therefore

    measure_angle(int(H) intersect {|z|=5/4})
      +measure_angle(int(E_0) intersect {|z|=5/4})<pi/4. (3)

No connectedness is assumed for either near unit's circle intersection.
Equation(3) is a measure inequality for their actual unchanged interiors.

## 3. The entire outer hub boundary arc is far, so nearness is on the occupied arc

Let Gamma_out be the closed outer H boundary arc between the two actual
endpoint applications, containing no internal positive spoke in the
physical exterior-face order. Let Gamma_in be the complementary closed
occupied H arc. The applications are distinct, as proved in the full
one-hub source from actual boundary-path geometry.

The complete proof of GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md has
the stronger surviving export

    dist(O,Gamma_out)>1/4.                            (4)

This is not inferred merely from its stated pocket conclusion. Its
Section 2 explicitly uses(4) in criterion(8), and Sections 3--6 prove
that criterion or contradict the entire original equations in every
endpoint-normal case. The same-axis alternative is contradicted.
Adjacent axes give a strict diagonal support bound; opposite axes use
the entire vertical segment and both actual port radii. The mixed
axis/oblique cases use that same complete segment argument. Adjacent
oblique vertices give a side height greater than3/10; opposite oblique
vertices use the full hub-force groups and both positive side supports.
All shared endpoint means, coincident internal spokes and individual
zero circle coefficients remain. Thus every actual surviving component
in the exact whole scope of Section 1 satisfies(4).

Combining(2) with the critical no-contained-disk theorem gives

    dist(O,partial H)<delta.                         (5)

Here is the full inside/outside argument. If O is outside H, a nearest
point of the closed square lies on its boundary and has norm less than
delta by(2). If O is on its boundary, (5) is immediate. If O is inside
H and every boundary point had norm at least delta, the whole closed
disk D_delta would lie in H: otherwise a segment from O to a point of
that disk outside H would meet the boundary at a smaller norm. That
closed containment is forbidden even at equality. Thus(5) holds in all
three origin-location cases.

Since delta<1/4, (4)--(5) show that some actual boundary point of norm
less than delta lies strictly on Gamma_in, away from its two endpoints.
No claim that O is in H is needed. The near point is geometric only;
it is not substituted for any force application or side mean.

## 4. A short segment joining physical boundary ports stays beyond3/10

The following force-free lemma is useful for many callers. Let two actual
points P,Q each belong to an actual physical boundary unit in the same
disk, and assume |P-Q|<=1. Then

    dist(O,[P,Q])>=sqrt((R-sqrt(2))^2-1/4)>3/10.      (6)

The units containing P,Q may have arbitrary loads, degrees and frames;
the points can be actual shared-side means or endpoints. No pair force
or physical contact between those two units is required for the lemma.

Write r_0=R-sqrt(2), so |P|,|Q|>=r_0. If the nearest point of the
segment to O is an endpoint, its norm is at least r_0 and(6) follows.
Otherwise the perpendicular projection lies in the segment. One of the
two endpoint distances along the segment from that projection is at most
|P-Q|/2<=1/2. Pythagoras at that endpoint gives

    r_0^2<=dist(O,[P,Q])^2+1/4.

The displayed radical is real since R>=2, and

    (2-sqrt(2))^2-1/4
      =23/4-4*sqrt(2)>9/100

using sqrt(2)<283/200. This proves(6), including zero length and all
weak endpoint/projection cases. The segment is actual occupied geometry
when it is a side or chord of an original square; nothing is moved.

## 5. Literal D02 central and exterior allocation

Retain the original M6.B6.HEXAGON.D02.L01345 component with actual rim
01,12,23,34,45,50, positive chord02, and load set{0,1,3,4,5}. Put

    U=2, V=1, W=0, T=3,
    boundary path1,0,5,4,3.

All original degrees remain U3,V2,W3,5_2,4_2,T2. The entire positive
component is the Section 1 one-hub path with k=5 and its three actual
spokes UV,UW,UT. The same-nine analytic lower-window theorem gives
2<R<=sqrt(Q), with all three original completing units retained.

The original bounded faces are the actual triangle012 and pentagon02345.
CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md bounds their whole central free
union by one unit. Its proof assigns whole extras to actual face sides
using their connected open interiors and the complete compatible
weak-junction routing; it does not remove the chord.

For the exterior, choose simultaneous actual circle spokes at all five
loaded boundary bodies in the same physical embedding. Every whole
extra is central or belongs to one of the exterior circle pockets.
The four actual direct boundary-pair pockets along1--0--5--4--3 are
empty by the complete physical boundary-pair theorem. The only remaining
exterior pocket is the actual closing pocket through U between V and T.
Additional physical zero-weight contacts may subdivide these regions
but cannot connect them through a closed occupied unit.

These are precisely the entire allocation and capacity hypotheses of
Theorem A, with no assumption about an extra's center. Consequently:

* Exactly one original extra E_0 lies centrally, and it is delta-near.
* U is delta-near and physically circle-clear.
* The other two original extras lie wholly in the closing pocket and
  are strictly quarter-clear.
* Together with V,W,5,4,T, they are the seven far units of Theorem A.

The central triangle is empty, so E_0 is on the actual pentagon02345
side. Its particular pose, forces, orientation and contacts are not
prescribed. None of the three extras has been omitted or replaced.

## 6. Exact two support strips in the entire remaining D02 owner cover

Use the full published singleton terminal-axis cover, with circle origin
still O=0 and only a rigid rotation/reflection:

    U=[x-1,x] x [p-1,p],
    P=P_UV=(x,p), Q_U=P_UW=(x,p-1), S=P_UT=(x-1,p-h),
    n_UV=(a,b), n_UW=(c,-d), n_UT=West,
    a,b,c,d>0, a^2+b^2=c^2+d^2=1,
    K=ad+bc>0, L=ac-bd>0, h=bc/K in(0,1).           (7)

The original UV and UW contacts are external side-interior singletons.
The original UT is a physical singleton in the relative interior of
U's West side and is the sole U-owned spoke. All masks and path means
remain. The following implications work simultaneously for both
remaining V-owned and W-owned VW normals; no unique V mask is required
until Section 8.

The occupied U arc runs clockwise from P through Q_U and the lower-left
vertex to S. The actual internal spoke UW fixes that choice. Hence the
outer U arc consists of the top side followed by the left-side segment
from the top-left vertex to S. The exact true T2 moment sign in the
complete one-hub source gives

    det(S,West)=p-h>0.                               (8)

Thus p>h>0. Both P and Q_U belong to actual physical boundary units,
and their connecting segment is the whole right U side of length one.
Lemma(6) puts that entire side beyond3/10. Section 3 puts the entire
outer U arc beyond1/4. The delta-near boundary point from(5) must
therefore lie on one of the two remaining actual segments:

    [x-1,x] x {p-1},
    {x-1} x [p-1,p-h].                              (9)

In particular every still possible original certificate satisfies

    |p-1|<delta   OR   |x-1|<delta.                  (10)

These are necessary strips for the actual support lines, not selected
replacement contact positions. Their strict endpoints follow from the
strict critical near-unit theorem. Neither strip assumes O in U.

The stronger exact statement is the actual-segment alternative(9):
one of those two closed segments has distance less than delta. It
retains the finite segment endpoints, rather than merely enlarging
the sides to infinite lines.

## 7. Both positive support coordinates exceed kappa>1/2

Hub nearness and p>0 imply

    x<1+delta,    p<1+delta.                         (11)

For example if x-1>=delta, every point of U has norm at least delta;
the p bound is identical. The unit T is wholly in x_coordinate<=x-1
and has horizontal projection half-width at least1/2. Its actual center
therefore satisfies(c_T)_x<=x-3/2. Every contained unit center obeys

    |c_T|<91/60,

because its farthest-corner radius is at least |c_T|^2+|c_T|+1/2 and
(91/60)^2+91/60+1/2-Q=31/57600>0. Thus

    x>-1/60.                                         (12)

If the bottom strip in(10) holds, the actual boundary point Q_U gives

    x^2+(p-1)^2> (2-sqrt(2))^2,
    |x|>kappa.

Equations(1),(12) exclude the negative alternative. Consequently

    x>kappa,    p>1-delta>kappa                       (13)

throughout the bottom-strip domain.

If the left strip in(10) holds, the actual boundary point S and(8) give

    (x-1)^2+(p-h)^2>(2-sqrt(2))^2,
    p-h>kappa.

Hence in this domain

    p>h+kappa>kappa,    x>1-delta>kappa.              (14)

The two alternatives exhaust(10). Thus uniformly over both actual
return-owner interfaces,

    kappa<x<1+delta,    kappa<p<1+delta,
    max{x,p}>1-delta,
    kappa>1/2.                                       (15)

In particular the actual hub center(x-1/2,p-1/2) is strictly in the
northeast quadrant about the unchanged circle origin. Its origin-facing
boundary nearness is confined to the two actual sides in(9).

The complete U3 identity also gives h>b^2. Indeed

    h-b^2=(bc-b^2*(ad+bc))/K
          =ab*(ac-bd)/K=abL/K>0.

Thus the entire left-strip domain has the additional strict bound

    p>b^2+kappa.                                     (16)

No derivative, numerical angle bound or scalar pose certificate enters
these inequalities. They use actual physical boundary points and the
full unchanged terminal moment.

## 8. Uniform consequences at the unique physical V corner

Now suppose V has its remaining unique physical circle corner. Let
k=Jn=(-b,a). Its exact actual side chart is

    V=P+[0,1]n+[-rho,1-rho]k, 0<rho<1.

In the V-owned return interface the full V2 is F_V=mu*n+omega*k.
In the W-owned interface it is F_V=mu*n+omega*l, with
l=K*n+L*k. All magnitudes and K,L are strictly positive. Thus both
own components of the actual unique circle corner are positive.
Write that physical corner as

    Z_V=A*n+B*k,
    A=P.n+1=1+a*x+b*p,
    B=P.k+1-rho,
    A^2+B^2=R^2, A>1/2, B>1/2.                     (17)

The strict half-unit inequalities follow by comparing the two adjacent
contained corners; equality in either would give a second physical
circle corner, contrary to this section's hypothesis. From(15),

    A>1+kappa*(a+b)>1+kappa>3/2,
    1/2<B<23/16.                                    (18)

The last comparison is exact:

    B^2=R^2-A^2<Q-9/4=529/256.

Because W is an actual boundary neighbor of the true loaded V2, the
complete proper-concurrence lemma gives

    q_V=P+ell*n=tau*F_V, ell>=0, tau>0.

Both ordinary coordinates of P are positive by(15), and a,b>0.
Therefore q_V has two strictly positive ordinary coordinates. The
unique-circle resultant is a positive multiple of Z_V, so that actual
physical circle corner lies in the strict northeast quadrant as well.

There is also a uniform incoming-tilt lower bound. Let beta=P.k. The
last display and B>0 give beta>0. In the original ordinary coordinates,

    x=a*(A-1)-b*beta<a*(A-1).

Since B>1/2 and R^2<=Q, one has A-1<61/60 by the same exact radial
comparison as before. Thus

    a>60*kappa/61>30/61.                             (19)

These are actual-coordinate necessary consequences for both original
unique-tip interfaces at once. All W and T physical masks, original
side parameters, other boundary-path means and the one central/two
closing extras remain. No complete interface contradiction is claimed.

## 9. Exact operative sources and adoption boundary

| Source | SHA256 | Exact use |
| --- | --- | --- |
| UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md | c8c9dc223e11dbcd7be9063818d546a3d3c0bc77b66cdac181b9ea97d51bae69 | Complete exact critical near-unit and closed-disk obstruction; radius-5/4 arc theorem for(3) |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Whole-component pocket clearance, full endpoint moments and the complete surviving outer-arc export in criterion(8), proved by every case in Sections3--6 |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Whole actual D02 central triangle/pentagon free union capacity one |
| D02_SINGLETON_TERMINAL_AXIS_TWO_NONPARALLEL_RETURN_COVER.md | 7997a9a7eacc0aedf85801eda33b5e7a0ca2e4ce37b86b95f7cb1ba3b6c28ce9 | Entire original two-interface chart, true degrees, full U3 and V2 equations, exact original applications and L>0 |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Complete actual boundary-pair exterior-pocket emptiness and physical corner order |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Compatible actual embedding, simultaneous circle spokes and weak-junction whole-unit routing |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original D02 graph/load/degree domain and all three extras |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Only full true-V2 all-mask proper-concurrence Lemma2.1 with actual physical boundary neighbor W |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same-nine strict R>2 for the literal original D02 caller |

The general statements require their explicit whole-extra allocation;
they do not assert that every cyclic graph has central capacity one.
The D02 application has its complete physical allocation above and earns
zero whole original-row credit. No original ID, order, count or flag is
changed. The global sharp theorem and complete equality classification
remain open. No Lean/Lake invocation, CI/workflow dispatch, original-ledger
edit, commit, remote write or pull request merge is performed here.
