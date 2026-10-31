# Root review: all intact triangles at one root, with arbitrary bridge forests

Date: October 26, 2026.

**Decision: ACCEPT the complete source at its stated local and whole-family
scope.** No whole bridged C2.33 row, original fine gate, unrestricted radius
bound or equality classification is closed by this review.

Reviewed source:
`GLOBAL_CLOSURE_COMMON_ROOT_INTACT_TRIANGLE_FORESTS_EXCLUSION.md`.
The exact mathematical source pin before status-only acceptance edits is

    c795a5ecd42de5fcd2030849b2061f1ea970a3e5ae6f72fe72598f793e72e4ac

I read the entire source, the complete origin-interior end-triangle theorem,
the boundary angular-neighbor proof, and the local circle-resultant angle
estimate. The whole-forest join was checked against the already accepted
articulation and off-origin bridge reductions. This is a full physical-scope
review, not a check of a chosen drawing or only the displayed arithmetic.

## 1. Common-side consequences and all actual ports

The root origin theorem applies at arbitrary true root degree and retains
every outside force. Its actual common side has height P<39/40; its two
actual ports strictly straddle transverse height zero, including the
parallel branch. In the nonparallel branch the normal components along
the common outward side axis are strictly positive. Since the origin is
strictly inside the square, a nonzero transverse normal component can
occur only at the correspondingly signed side endpoint. The full normal
sign assertions used in the new source are therefore valid, including
zero proper lengths, tangential endpoint limits and actual side means.

The straddling port interval has length at most one. At least one port
has transverse magnitude at most 1/2. It belongs to a physically boundary
tip, so its norm is strictly greater than 67/120. Thus

    P^2 > (67/120)^2-1/4 = 889/14400 > 1/25.

Origin containment supplies P>0, so P>1/5. Each root vertex has axial
coordinate P or P-1. Both magnitudes are greater than 1/40, using the
strict upper bound P<39/40. This proves the claimed vertex margin, but
does not assert a disk margin at the other two sides.

## 2. The at-most-one-petal-per-face assertion

Each tip is a true loaded degree-two body with a physical loaded neighbor.
Its complete proper concurrence is a positive multiple of its actual
circle resultant and lies beyond the unchanged root port along the root
outward normal. The common-side port signs consequently put the two
resultant directions strictly on opposite sides of the common side axis
and inside its open angular semicircle.

The two tips physically touch. Their center directions are consecutive
along a minor gap less than 2pi/5; every pair of boundary-center directions
is more than pi/5 apart. The entire nonnegative circle resultant, including
individual zero corner weights, differs from its own center direction by
less than pi/12. The disjoint center intervals preserve cyclic order.
The resultant gap for the touching pair is positive and less than

    2pi/5+pi/6=17pi/30<pi.

It is therefore its minor gap and contains no other loaded resultant
direction. Two distinct petals at the same root have four distinct true
tips. If both petals used one face, their two open minor gaps would both
contain that face axis. Overlapping arcs of length less than pi with four
distinct endpoints put an endpoint of one inside the other (including
the nested-arc alternative). This contradicts the empty touching-pair
gap. The common face is unambiguous because its two ports are distinct.

## 3. Every small radial bridge is excluded at a two-petal root

At an origin-interior root, a radial application has the form sigma e,
sigma>0. Its hypothesized norm at most epsilon<1/60, together with the
vertex margin greater than 1/40, makes it a genuine side-interior port.
Thus e is an actual root side axis and the two parallel support heights
are sigma and 1-sigma. The bounds 1/5<P<39/40 exclude both of these
faces for any intact petal; the upper comparison has strict reserve

    59/60-39/40=1/120.

A perpendicular petal has one port with e-coordinate in (0,sigma]. Its
physical boundary norm then gives

    P^2 > (67/120)^2-(1/60)^2 = 299/960 > 1/4.

Every used perpendicular face has height greater than 1/2. Section 2
allows at most one petal on either face. Two petals would need both
opposite faces, whose heights sum to one, a contradiction. If epsilon
is zero, a positive radial support of norm at most epsilon is already
impossible; no limiting port is discarded.

## 4. The entire specified bridge-forest join

All cyclic blocks in this theorem share H, and every other cyclic vertex
is a true degree-two tip. The theorem does not assume this of a decorated
tip. Each actual triangle is intact and puts O in the open interior of H.
Every other actual square, including a square touching H at a zero-weight
contact, avoids O even on its boundary.

The accepted minimum-support articulation reduction, with its named
small-core joins, makes a loaded bridge-only body a genuine leaf. Any
remaining positive bridge-only internal body is unloaded and off-origin.
Its complete classification gives true degree two and an inward neighbor
containing O, which must be H. The inward actual application has norm in
(0,epsilon], contradicting Section 3. This handles every internal forest
shape and length before concluding that all branches are direct leaves.

The final equation is the full equation at H, with every petal and every
genuine direct leaf retained. H is physically circle-clear. Each petal
has strictly positive center pressure. Each S leaf has projection at
least d-1/sqrt(2)>0; each D leaf has projection r-1/2>0. Their sum cannot
vanish after taking scalar product with c_H. This excludes the entire
stated common-root intact-petal forest family, including the empty forest.

## 5. Verification and limits

Exact Fraction arithmetic independently checked 889/14400, its reserve
313/14400 above 1/25, 299/960, its reserve 59/960 above 1/4, and the
strict 1/120 side/vertex comparisons. These checks support the continuous
proof and are not sampled physical poses or a substitute for its cases.

The result does not cover tip-decorated petals or a graph lacking an
intact petal. It does not contract a long branch to a leaf, delete an
outside force, assign a degree-two equation to H, or change any normal,
physical mask, individual circle weight or actual shared mean. No Lean
compilation, CI, remote action or shared-ledger update was performed in
this review.
