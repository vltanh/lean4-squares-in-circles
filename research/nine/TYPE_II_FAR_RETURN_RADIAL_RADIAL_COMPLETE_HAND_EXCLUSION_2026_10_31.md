# The entire original far-return radial/radial mask is excluded by hand

Date: October 31, 2026 UTC.

**Status: complete hand exclusion of the original Type II far-return
side feature with both exterior endpoints physically radial.** The
actual six-unit core has room for at most two additional units, whereas
the original nine-square packing retains three. This closes the whole
stated physical mask over its complete continuous domain. It does not
close the other endpoint masks, the whole far-return feature, or the
whole original D02.L135 row.

The proof keeps the actual positive chord and full loaded endpoint
stars. Its five main capacities are

    triangular face 0, pentagonal face 0,
    outer N pocket 0, outer A pocket 1, outer D pocket 1.

Both physical two-corner endpoint caps have capacity zero as well.
These are bounds on the original physical regions, including all their
weak subdivisions; no generated pose cover supplies any part of this
conclusion.

## 1. Exact original entry and the three units still to be placed

Retain all nine actual unit squares in the unchanged disk and the
original physical plane embedding of D02.L135. Its six-unit core is

    A=0, V=1, D_hub=2, C=3, N=4, B=5,

with positive exterior cycle

    A--V--D_hub--C--N--B--A

and the original positive A--D_hub chord. The complete original stars
are A3, D3, V2, B2, C2 and N2. The hubs A,D_hub and N have zero circle
load; V,B,C have their original positive circle loads. Zero load is
not identified with physical circle clearance.

Take the original unique-circle V, Type II D-owned roof-direction,
strict far-A-vertex side return, and assume that B and C have their
physical two-corner radial masks. All original common selected normals,
positive contact forces, applications, side means and individual
nonnegative circle coefficients remain. Either individual circle
coefficient at B or C may be zero. The three completing units need not
have any prescribed force or physical circle mask.

The original chart and the complete hand radial-mask reduction are
recorded in

    UNIVERSAL_UNIT_SQUARE_CAP_AND_COMPLETE_TYPE_II_FAR_RETURN_DIAGONAL_EXCLUSION_2026_10_29.md,
    TYPE_II_FAR_RETURN_B_RADIAL_GAP_AND_COMPLETE_RADIAL_MASK_HAND_REDUCTION_2026_10_31.md.

Only the hand portions of that original chart are used. In particular
the former generated all-radial-endpoint cover is not an input here.

The same-nine hand measure theorem gives R>2, while the unchanged upper
window is R^2<=1105/256. The fully printed hand route is

    NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md,
    NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md,
    NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md,
    ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md, Section 3.

It uses the analytic measure mass 8997/1000<9 and the printed whole-square
mass bounds, rather than a generated numerical certificate. These same
hand dependencies are recorded in the radial-mask companion.

Use the actual oriented frame (d0,n), with d0=-tD, and write the radial
support scalar as

    D=sqrt(R^2-1/4)-1, 117/125<D<61/60.

This scalar is distinct from the hub D_hub. The exact radial/radial
bridge, with its unchanged endpoints, gives

    r=sqrt(1+q^2)-q=D-1/(4D), 2/3<r<4/5,
    theta=atan(r), s=sin(theta), c=cos(theta),
    f=(-2*s*c,c^2-s^2), w=Jrot(f),
    u=(-s,c), j=Jrot(u)=(-c,-s),
    B=[D,D+1]*f+[-1/2,1/2]*w,
    C=[-1/2,1/2]*d0+[-D-1,-D]*n,
    T=D*f+w/2, U=(-1/2,-D), T-U=u,
    T.u=1/2, U.u=-1/2, T.j=U.j=D.                 (1)

The actual N has its entire original transverse interval

    N=[-1/2,1/2]*u+[rho,rho+1]*j,
    D-1<=rho<=D.                                  (2)

Let W be the unchanged A/D_hub application, K the original A/B
application and L the original D_hub/C application. The bounded
pentagonal contact face has order

    W -> L -> U -> T -> K -> W.                    (3)

The other bounded positive face is the original A,V,D_hub triangle.

## 2. The two actual bounded faces are empty

The complete physical face list and routing are Sections 1--2 of
`CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md`. For the original single
short chord 02 they give precisely the triangle 012 and the pentagon
02345. Every central completion unit lies on the bounded side of one
of these actual faces, retaining the positive chord.

For the triangle, the hand contact-ring theorem
`CONTACT_RING_HOLE_AREA.md` gives free area at most sqrt(3)/4<1.
Consequently this entire bounded face contains no additional unit.
This includes every physical subdivision of the triangular free union.

For the pentagon the stronger whole-domain result is

    TYPE_II_FAR_RETURN_RADIAL_RADIAL_CENTRAL_STRIP_EMPTY_HAND_EXCLUSION_2026_10_31.md.

That proof uses the original hub and radial equations to show that all
five actual contact vertices in (3) satisfy

    D-797/800 < point.j <= D.                      (4)

For the hub vertex W its exact calculation is

    D-W.j=[1+cos(theta-eta)-cos(theta)]/[2*sin(theta)],
    0<eta<atan(3/13)<theta,

followed by a strictly decreasing one-variable trigonometric comparison.
For K and L the full genuine side means give respectively

    K.j=D-beta_B*c, L.j=D-beta_C*c,
    1/2<beta_B,beta_C<1,
    c<5/6<797/800.

Thus (4) holds simultaneously for all original radial weights and all
values of the full N transverse mean. The entire bounded polygonal
winding region lies in the convex hull of these vertices and hence in
the same strip. Any unit square has width at least one in direction j:
for its orthonormal own axes g,h that width is

    |g.j|+|h.j| >= sqrt((g.j)^2+(h.j)^2)=1.

The strip in (4) has width less than one. It contains no whole unit.
The whole actual central allocation therefore has capacity zero, not
merely capacity one.

## 3. The entire original outer N pocket is empty

The whole-mask hand theorem

    TYPE_II_FAR_RETURN_RADIAL_RADIAL_SIDE_POCKET_EMPTY_HAND_EXCLUSION_2026_10_31.md

proves directly from the unchanged A side and actual disjointness that

    rho>1/40, hence dist(O,N)>1/40.                 (5)

Its geometric point is an actual point E of the A side WK, where
E.u=1/2. The exact original equations put

    1/40<E.j<D.

If rho<E.j, points of the same actual A side immediately toward W
would be in int(N), contrary to physical disjointness. Thus rho>=E.j.
This argument treats every transverse value in (2), including both
original extreme means, and does not move or reselect N.

The complete force-free theorem
`FORCE_FREE_OCCUPIED_SIDE_CHANNEL_ONE_FORTIETH_PROXIMITY.md` says that
a whole unit in this actual C--N--B outer pocket would require
dist(O,N)<1/40. The original channel height T.j=U.j=D>0 and the actual
positive exterior order are precisely its routing data. Equation (5)
contradicts that necessary condition. The entire outer N pocket has
capacity zero.

Possible zero-load physical circle contact of N is also retained. In
(2),(5), its far j-side corner norms are
sqrt(1/4+(rho+1)^2)<=sqrt(1/4+(D+1)^2)=R; its near j-side corners
are strictly closer. Equality can occur only when rho=D. Such physical
anchors merely subdivide the same original outer N region. The cited
whole-pocket theorem includes them, so they create no additional
completion allocation.

## 4. The two literal exterior hub pockets have total capacity at most two

The two complete hand theorems are

    TYPE_II_FAR_RETURN_RADIAL_RADIAL_A_HUB_POCKET_CAPACITY_ONE_HAND_EXCLUSION_2026_10_31.md,
    TYPE_II_FAR_RETURN_RADIAL_RADIAL_D_HUB_POCKET_CAPACITY_ONE_HAND_PROOF_2026_10_31.md.

Both concern the same unchanged original units. They first establish
the useful physical fact

    |W|^2<5/36<1/4.

Since W belongs to each hub, every point of either hub has norm less
than 1/2+sqrt(2)<2<R. Thus A and D_hub are physically circle-clear
throughout this whole mask. No additional hub boundary anchor is
omitted merely because its circle coefficient was zero.

For A, the original AV and AB applications are opposite A vertices.
Its actual outer intermediate vertex has n-coordinate greater than
79/60>5/4. The unchanged full V and B stars supply strict port moments
and proper positive endpoint rays. The cited A theorem verifies every
physical hypothesis of the existing opposite-vertex high-roof geometric
proof, including the actual upper closing circle arc. It does not
apply a two-force equation at the true-degree-three hub or presume a
physical boundary neighbor at V. That exact hand roof argument gives
capacity at most one for the entire original V--A--B pocket.

For D_hub, the cited theorem displays an actual occupied crosscut from
C's right physical circle corner through the unchanged shared C/D
side, D's outer sides and the actual V sides to V's unique physical
circle corner. Every point of it and its protected closing arc lies
to the right of d0-coordinate 2/5. Its whole pocket is therefore
quarter-clear. On the radius-5/4 circle, the actual C and V endpoint
incircles leave an interval of length less than pi/2. Every additional
unit in this pocket contributes a connected open arc longer than pi/4.
Two such disjoint units cannot fit. This proves capacity at most one
for the entire original C--D_hub--V pocket.

Both conclusions include every weak junction and every subdivision by
extra zero-force physical contacts. They keep the same actual A/D
chord, full endpoint circle means and three original completing units.

## 5. The physical two-corner caps add no capacity

Each radial boundary square has a physical side joining its two circle
corners. For B this is its outer f-side at f-coordinate D+1. The
circular segment beyond that occupied side has width

    R-(D+1)=R-sqrt(R^2-1/4)<1.                    (6)

For example R>2 makes the width
`(1/4)/(R+sqrt(R^2-1/4))` strictly less than 1/15, since the
denominator exceeds `2+7/4=15/4`. The same statement
holds for C, reflected in its radial direction. Each entire segment
therefore has capacity zero, because every unit square has width at
least one in every direction.

These small caps are not silently absorbed into a neighboring pocket.
Their circle endpoints and the occupied outer side make a closed
barrier. A connected open completion interior cannot cross that side
or either circle endpoint to straddle the cap and another region.
Thus each whole completion unit assigned there would have to lie in
the width-(6) cap, which is impossible. Both physical corners are
retained even when one of their original circle coefficients is zero.

V has only its unique physical circle corner in the original feature,
so it has no second-corner cap. Section 4 proves physical clearance
for A,D_hub. Any physical boundary subdivision at N has already been
included in Section 3.

## 6. Complete actual-region allocation and the contradiction

Use the original physical plane embedding, rather than a redrawn
canonical hexagon. Its positive chord splits the bounded side of the
rim into the two face cycles used in Section 2. The actual exterior
paths between the positive boundary units are

    V--A--B, B--N--C, C--D_hub--V.

The literal occupied crosscuts and protected circle arcs in Sections
3--4 identify their three original outer pockets. At a radial endpoint
the two gap-facing choices are separated by exactly the small
two-corner cap treated in Section 5. This lists the complete free
allocation: the two bounded faces, the three outer pockets, and the
two radial endpoint caps. An additional zero-load physical contact
can subdivide one of these regions; it cannot join two through an
occupied barrier.

Here is the weak-contact justification explicitly. The open interior
of any completing square avoids every closed core unit: an open
neighborhood of a point in a closed unit meets that unit's open
interior. The completing interior is connected. A compact connected
inner square has positive distance from the closed core and from the
containing circle. It therefore has one physical face or outer-pocket
label under every sufficiently small center/contact routing, and its
winding label cannot change across an occupied segment. Exhaust its
open interior by these nested compact inner squares. Their labels
agree because they overlap. Closure puts the whole actual completing
square on that same region's closed side. Retraced segments, tangent
junctions and full shared-side extreme contacts do not create a new
region containing part of one whole unit.

This is the same routing convention proved for the two central faces
in `CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md`, Section 1, and checked
for each literal exterior crosscut in the three pocket companions.
In particular there is no uncounted pocket at the original AD chord,
no free strip across a radial endpoint's outer side, and no extra
physical hub boundary cap.

The complete resulting capacities are

| Original physical region | Whole-unit capacity | Hand reason |
| --- | ---: | --- |
| A,V,D_hub triangular bounded face | 0 | Contact-ring area below one |
| A,D_hub,C,N,B pentagonal bounded face | 0 | Entire actual contact polygon in width <797/800 |
| B,N,C outer pocket, all subdivisions | 0 | Actual N has distance >1/40; occupancy requires <1/40 |
| V,A,B outer pocket, all subdivisions | 1 | Literal proper opposite-vertex high-roof theorem |
| C,D_hub,V outer pocket, all subdivisions | 1 | Actual endpoint arcs leave less than pi/2 |
| B physical two-corner cap | 0 | Width R-sqrt(R^2-1/4)<1 |
| C physical two-corner cap | 0 | The same width bound |

Every one of the three original additional units must occur in this
list. The sum of its valid capacities is two. Three distinct actual
units cannot be assigned to it. This contradiction excludes the
entire original radial/radial physical mask.

## 7. Exact closure scope

The conclusion is the full original unique-V, Type II D-owned
roof-direction, strict far-A-vertex SIDE return with both B and C
physically radial. Its proof covers the complete continuous parameter
domain, all original N transverse means, both individual circle
coefficient endpoints, every additional physical contact and all three
original completing units simultaneously.

The one-unique endpoint alternatives remain separate obligations. In
particular this source does not declare the whole original far-return
feature or D02.L135 closed, does not create an original fine identifier,
and does not alter an original fine or coarse count. The appropriate
use is to replace the radial/radial part of the former computational
leaf by this complete hand exclusion.

All inputs used for closure are printed continuous geometric or exact
algebraic hand proofs. No sampled pose, generated exclusion certificate,
external mathematical proof script, Lean/Lake invocation or CI is used.
