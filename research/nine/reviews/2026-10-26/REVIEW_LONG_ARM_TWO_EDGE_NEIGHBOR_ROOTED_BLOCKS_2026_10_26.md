# Independent full review: long and two-edge arms at touching roots

Date: October 26, 2026.
Reviewer: rooted-blocks independent agent.

**Verdict: ACCEPT the complete original-layout exclusion.**
The full source reviewed is
`GLOBAL_CLOSURE_LONG_ARM_EXCLUDES_TWO_EDGE_NEIGHBOR.md`, SHA-256
`ab13b22f08fadb69c75ad80fff15dabc7a339460f01795a5af8b7d63537052e7`.
It excludes the whole (3,2) layout, including (3,2,1), for physically
touching roots with the stated genuine pendant paths. No force or circle
load at either root is discarded.

## 1. Original long-arm input and full short-arm cover

The length-three source has its exact required scope: internal bodies
truly unloaded of degree two, actual S/D leaf, and arbitrary original
root forces and circle load. Its complete width, leaf and physical P
arguments give d>1, epsilon=d-1 in (0,1/60), the original S leaf S(e),
and the first transmitter U with longitudinal interval
[epsilon-1,epsilon] and a transverse interval containing zero. Thus U
contains zero without any assumption that A itself is unloaded.

For the two-edge path, the actual leaf and transmitter equations give
the original applications r_M v and (r_M-w)v. I checked both discarded
leaf/width alternatives. A genuine D leaf has its off-origin inner
vertex in the relative side interior of its parent T under the retained
strict/nonradial point-normal convention. T is therefore side-aligned,
has longitudinal interval [r-1,r], and has zero strictly inside its
transverse interval. Since 0<r<1, it contains zero in its open interior.
The D/diagonal vertex-contact alternative is excluded by that same
original convention, not by changing its normal.

For an S leaf with a diagonal transmitter, the two unchanged radial
applications are opposite vertices of T. Since 0<d<sqrt(2), zero lies
strictly inside that diagonal and hence in T's open interior. Either
case overlaps the physical U that already contains zero. Thus only the
actual S/side alternative remains, with application epsilon v at B.

## 2. The small radial application forces the complete root frame

For any unit square with actual outward radial support epsilon v,
0<epsilon<1, its full unit inward segment belongs to the square. At a
vertex, the inward own-coordinate decrements are the nonnegative
components of a unit vector, each at most one; at a side the statement
is the ordinary perpendicular unit segment. Thus B contains zero.

It cannot have zero as a vertex. In [0,1]u+[0,1]w, every nonzero
positive radial support is at an adjacent or opposite vertex, or on a
far support with an own coordinate equal to one. Its radius is therefore
at least one. The two origin sides cannot support a positive multiple
of their outward axis. This exhaustive support cover includes axis
endpoints and excludes epsilon<1.

Neither B nor U can contain zero in its open interior because the
other contains it. Each must therefore have zero in a relative side
interior. U's longitudinal interval straddles zero strictly, so its
origin side is parallel to e. Disjoint tangent half-planes must be
opposite and have the same boundary line. Hence B has the exact aligned
form [a,a+1] times [-1,0], with a<0<a+1, after reflection.

This derivation retains the actual B orientation; it does not impose a
common frame as a hypothesis or infer it from a center alone.

## 3. The whole remaining feature cover contradicts either leaf distinctness or contact

An actual epsilon-radius support cannot lie on the far horizontal face,
whose points have norm at least one. An origin-side interior has upward
normal and cannot contain its positive radial multiple. At either
origin-side endpoint, radiality itself makes the normal horizontal.
Vertical-side interiors already have horizontal normals. Thus every
remaining original contact feature, including all endpoints, gives
v=e or v=-e.

The first direction makes the two actual S terminals identical, contrary
to the disjoint path body sets. The second puts B entirely in x>=-epsilon,
while A remains in x<=-(1-epsilon). These closed supporting half-planes
have strictly positive gap 1-2epsilon>29/30, so the original roots cannot
touch. This contradiction does not use their circle loads, degree, a
triangle moment, or a concurrence sign.

The two short-arm types and all original means are exhausted, and the
critical or lower radii were already excluded by the complete long-arm
physical P argument. All other physical units remain in each capacity
and nonoverlap premise. The result is a whole layout theorem; it does not
alone close an entire larger coarse cell or imply a final radius/equality
claim.

No correction is required. No Lean compilation, CI, numerical search,
remote action or shared-ledger edit was performed.
