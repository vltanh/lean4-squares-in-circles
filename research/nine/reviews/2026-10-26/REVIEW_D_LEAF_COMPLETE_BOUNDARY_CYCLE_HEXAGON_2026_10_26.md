# Independent review: a genuine D leaf and an otherwise loaded simple cycle

Date: October 26, 2026.
Reviewer: separate hexagon proof worker.
Source reviewed: D_LEAF_COMPLETE_BOUNDARY_CYCLE_EXCLUSION.md.

**Verdict: accepted throughout the complete stated original domain.**
I checked the full source against the actual fixed-point selection,
the endpoint proper-concurrence lemma, the original local D-articulation
calculations, and the previously reviewed degree-free endpoint-moment
and port-order arguments.

## 1. Full component and the selection boundary

The original component is exactly one simple cycle and one genuine
D leaf. Every nonroot cycle body is loaded and truly degree two; the
root is truly degree three. No additional positive chord, root spoke,
or second leaf is removed. The entire radius domain is retained by
the explicitly inherited same-nine R<=2 exit, including that source's
arithmetic dependency.

RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md states its theorem
for any genuine radial-leaf root with exactly two other positive
neighbors, both physically boundary, and distinct singleton actual
intersections. It has no C4 or fixed cycle-length hypothesis. Its
finite physical candidate prelist precedes extraction, preserves the
strict/nonradial/matched normal conventions, and survives thinning.
Thus its use for the present longer cycle is legitimate. The new
source invokes its owner conclusion only when both intersections are
distinct singletons. The shared branch uses no such conclusion.

## 2. The central exit and complete shallow-side reduction

The genuine D chart has O in int H, r>1/2, s>1/3 and
r^2-s^2>1/16. If both transverse margins exceed 1/4, H contains a
strictly larger concentric disk and each of the eight other physical
units has strict distance greater than 1/4. Their nearest-point
supporting lines satisfy exactly the cap-arc theorem's premise. The
eight pairwise disjoint open-interior arcs give the contradiction.
The k=7 case uses the same argument on its eight physical boundary
units directly, so no seven-cycle exception is lost.

In the remaining reflected chart 0<a<=1/4, the real D leaf gives a
valid cut point on H which no third square can contain. Physical
boundary path order therefore gives the stated normal order, and the
unchanged endpoint torque equations give first moment positive and
last moment negative. Both are genuine degree-two endpoint equations.

All-horizontal root reactions are excluded with every lift endpoint
retained. A first east lift at zero applies above the real leaf cut
and has negative moment. A first west lift applies below -1/4 by the
boundary-point radius floor and has negative moment. A first lift of
2pi makes both normals east and cannot balance the leaf.

The full root vertical equation now gives one upper and one lower
normal, in that order. The northwest vertex is too central for any
boundary unit, so the upper normal is north or northeast. The full
horizontal equation makes the lower normal strictly southwest and its
contact the southwest singleton. The two normals are nonparallel:
opposite parallel normals with nonzero vertical components could not
balance the nonzero horizontal leaf. Their force-line intersection is
(q,0), and the actual positive first moment gives 0<q<=r. In
particular the two applications, at heights a and -b, are distinct.

## 3. Northeast upper contact

Here both root intersections are distinct singletons, so the accepted
selection makes the upper normal tip-owned. Because the normal is
strictly northeast, the root owns no side axis; the actual root vertex
lies in the relative interior of the tip side. This excludes a free
vertex/vertex interpretation without rotating an obtained force.

The actual application has norm below 3/4, excluding the entire
physical two-circle-corner mask, whose every point has norm above
9/10. The genuine endpoint concurrence then fixes the unique far
corner to be P+n-rho k. The negative transverse sign follows from
the strictly positive original endpoint moment.

The actual tip side meets the real D-leaf edge at t_0<1/4, strictly
inside that leaf edge. Extending beyond t_0 enters the leaf's open
interior, so the unchanged side parameter satisfies rho<=t_0. The
resulting corner norm is below 3/4+sqrt(17)/4<15/8<2, contradicting
the inherited R>2. No lower-tip height lemma or middle-body equation
is used in this reduction.

## 4. North singleton and north shared side

For a north singleton, the actual application (q,a) has q>sqrt(6)/5
and norm below 3/4. The physical two-corner mask is again excluded.
The singleton is the bottom vertex of an oblique unit: an aligned
unit would give either a shared side or a point-only vertex contact
with the forbidden nonstrict axis normal.

The unique circle corner must be the opposite vertex, since either
adjacent vertex has norm below 7/4. Proper concurrence lies in this
unique-corner tip, so its positive radial coefficient is at most one.
Its unchanged x coordinate is q, proving Delta>=0. The boundary-point
floor gives g=r-q<=a^2/(r+q)<1/16. For Delta>=1/2, an actual side
enters the real leaf after meeting the interior of its upper edge;
thus Delta<1/2. The stated strictly increasing far-corner norm then
gives R^2<553/144<4. This covers the whole oblique normal-owner and
original-circle-mask domain.

For a positive-length north intersection, the neighboring unit is
aligned and the original application remains an arbitrary mean on
the shared interval. The actual leaf obstruction gives x+1<=r+a;
otherwise a horizontal section at height a+epsilon enters the leaf
interior. Together with the unchanged mean's membership this gives
-1<X<11/12 and 0<Y<=5/4 throughout the upper unit. Its entire corner
set has norm squared below 41/16<4. The lower singleton may still
be free in this branch, since no ownership conclusion was imported.

These three cases exhaust the actual north/northeast upper normal
cover. They exclude the shallow-side core itself and hence retain
every arbitrary completion square without a pentagonal-hole claim.

## 5. Exact new gate

For H=0 and path 1,2,3,4 in the original C5, load set 1234 gives
the required four genuine loaded degree-two bodies. The D-leaf root
has true degree three and the three other original physical squares
remain. Thus the complete new original gate is exactly

    M6.B5L.C5.L1234.D.

The theorem also legitimately covers any longer simple cycle with
the identical true degree-three root and one D leaf within the nine
body budget. It does not extend to extra root forces or unloaded
cycle endpoints. Its S alternative and other original C5 load sets
are correctly left separate.

No sampled pose, new scalar certificate, Lean compilation, CI,
remote operation, or shared-ledger mutation was used in this review.
