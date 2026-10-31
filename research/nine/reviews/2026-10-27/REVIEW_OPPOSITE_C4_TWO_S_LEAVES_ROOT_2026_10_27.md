# Full root review: the opposite-leaf C4, including the whole attachment join

Date: October 27, 2026. Reviewer: root.

**Decision: ACCEPTED in the complete stated original scopes.** I read
the entire off-origin tilted-root source, the entire opposite-S/S
source, the entire mixed-D bypass source, and all three separate
independent review records listed below. The aligned-root prerequisite
has already received my complete mathematical review in
`REVIEW_C5_S1234_COMPLETE_ROOT_2026_10_27.md`; its unchanged pin is
`7c0e55bc75013f14d667a85635cd743361b325f7180f4710fd832c4f14ab9873`.
This review checks the new local mathematics and the complete original
radius, load, leaf-type and attachment joins. It is not an acceptance
based on a summary or another review's conclusion.

## 1. Frozen complete sources

| Source | SHA-256 |
| --- | --- |
| OFF_ORIGIN_TILTED_S_ROOT_BOUNDARY_NEIGHBORS_ONE_SIDE.md | c6f8bba23df9b27ccd40446386a0d81a03bb48e7e81e3c4ad68c3b71cd01f6e7 |
| OPPOSITE_C4_TWO_S_LEAVES_COMPLETE_EXCLUSION.md | 155dd1819ed6fdf4321dd6b9228402c2107624bd683a3b8020a0d6abaa96d780 |
| D_LEAF_ROOT_OPPOSITE_NEAR_BYPASS_EXCLUSION.md | 1a9c4d2b446d0c9fabbcae96d655f6264545a6ec12a963425b66343917eb2064 |

The complete independent S/S and local-root review is
`REVIEW_COMPLETE_OPPOSITE_C4_SS_AND_LOCAL_S_ROOTS_ROOTED_BLOCKS_2026_10_27.md`,
pin `c8a194732e1e84a8a1fee0003f3e638c59f0a0e0713868ed209f6df60377993d`.
The bypass source has both
`REVIEW_D_LEAF_ROOT_OPPOSITE_NEAR_BYPASS_TRIANGLE_BRIDGES_2026_10_27.md`,
pin `12de69ebbddec240a0f4f1179c03ebbd6eebce32ec8fa047d4191dc354974aea`,
and `REVIEW_D_ROOT_OPPOSITE_NEAR_BYPASS_HEXAGON_2026_10_27.md`,
pin `a53872f3aa50f4c84d6c7fc3d74e3916f6d5da009b78b29552493231a9639f18`.
These are separate full-source reviews, with the authorship distinction
explicit in the S/S assembly review.

The frozen source headers still describe submission for review. This
record and the named independent acceptances supply the later decision;
no mathematical source is silently changed merely to alter its header.

## 2. Complete tilted-root chart and physical screen

The genuine S leaf supplies its real port `(U,V)` and direction
`e=(U,V)/d` in the root's own axes. The frame symmetry makes
`U>=V>0`, and the root is `[U-1,U] x [V-1,V]`. Since
`V<d/sqrt(2)<1` and `U<2`, exclusion of the origin from the open
root is exactly `U>=1`, including its side-boundary limit. Thus
`0<=a=U-1<1/60` and `0<V<11/60`. No force is used to replace
an original port or side mean.

I checked the complete upper support-feature cover. The upper-left
vertex is too close to the origin to belong to a physical boundary
unit. At the genuine leaf port, the root's inward quadrant and the
leaf's inward half-plane leave two gaps, each strictly narrower than
a unit's ninety-degree inward sector. A third square cannot touch
there. Consequently any upward boundary normal must be the exact
north axis at an actual point `(q,V)` of the top side.

The physical boundary-distance inequality gives `q>3/5`, on the
entire high-radius interval. For a north square with a horizontal
bottom side, any extension beyond `x=U` produces an actual open
intersection with the tilted S leaf near its inner side. Therefore
all corners have the stated strict coordinate bounds. For a tilted
north square, its unique bottom vertex and inward axes `(c,s)` and
`(-s,c)` cover both tilts and every angle with `c,s>0`.

If the right upward edge does not reach the leaf's inner line, all
corners lie in the rectangle with squared bound `13130/3600<17/4`.
Otherwise its first crossing has actual leaf tangent coordinate
`g*d*s/(U*c+V*s)`, where `g=U-q`. Avoiding the occupied inner-side
interval requires that coordinate to be at least one half, including
equality. This gives the complete inequality

    q <= U-V/(2d)-(U/(2d))*(c/s).

It forces `c/s<61/72<1`, which bounds the opposite corner. For the
remaining adjacent corner I checked the full scalar maximum:
`sqrt(1-s^2)*(1-t/s)` has its positive maximum at `s^3=t`, equal
to `(1-t^(2/3))^(3/2)`. Here `t=U/(2d)>30/61>3/8`, so that
maximum is less than `3/8`; its nonpositive part is immediate.
The corner bound `(167/120)^2+(6/5)^2<17/4` is strict. Every
actual north square is therefore physically circle-clear, in
contradiction with the stipulated boundary neighbor. No equation
or positive degree at that neighbor was assumed.

## 3. Full original root force and torque

With every upward boundary normal excluded, the two original
nonleaf forces have nonpositive vertical components. If both also
had nonpositive horizontal components, every negative horizontal
force would act at a negative height on the actual left face.
Since all root first coordinates are nonnegative, each such moment
is strictly negative; pure south forces have nonpositive moments.
This contradicts the unchanged root torque, whose genuine radial
leaf has moment zero.

Write the remaining full forces as `(-u,-v)` and `(w,-z)` with
`u,w>0`, `v,z>=0`. The original force balance gives
`u-w=alpha*U/d` and `v+z=alpha*V/d>0`. If `v,z>0`, their actual
lower-vertex moment sum is `b*(u-w)-a*v-U*z<0`. If `v>0,z=0`,
the right-side mean stays arbitrary and the exact moment is
`alpha*(V-U)/d+w*(b-y_R)<0`. The double-zero case violates the
vertical force balance. Hence precisely the west and strict
southeast support features remain. This exhaustive calculation
uses all three original positive forces and the full side ranges.

The west application `(a,y)` satisfies `y<-647/1000`: the exact
comparison is `419/1000-1/3600>(647/1000)^2`. In the leaf's radial
frame it has negative transverse component and radial magnitude
less than `1/5`. A circle corner on the opposite closed semicircle
would consequently be more than a unit diameter away. At the
southeast application `(U,V-1)`, the exact coordinates are
`d-V/d` and `-U/d`. For the same wrong semicircle the squared
distance is at least

    (R-d)^2+1+2*V*(R/d-1) > 2.

Both inequalities are strict at all permitted endpoints. Thus
**every physical circle corner** of each neighbor is in one open
semicircle. A physical two-corner mask with a zero individual
weight is covered without converting it to a unique-corner mask.

## 4. The entire original opposite-S/S family

The component is the actual C4 `A-B-C-D-A`, with genuine leaves
at opposite roots `A,C`. Both roots retain their true degree three.
An unloaded `B` or `D` would supply an actual normal channel of
width at least one between two roots meeting the closed epsilon
disk. Its real support endpoints instead give width at most
`2*epsilon<1/30`. Therefore both private units are loaded and
physical boundary neighbors. This is the literal original load
cover, rather than an assumed pair of triangle equations.

For `d<1`, any tilted root contains the origin openly and overlaps
the other closed-origin root. An aligned root can avoid that
overlap only with the origin in a transverse side interior. The
two occupied half-neighborhoods must be opposite, and equal
directed leaf axes would duplicate the same physical radial leaf.
These facts force the two displayed whole rectangles and opposite
leaf directions. The local normal cover is exhaustive: an east
neighbor would coincide with the genuine leaf by the sharp cap;
two west normals have positive moments; the lower-left vertex is
too central for a boundary unit; a downward normal with positive
horizontal component at the lower-right vertex enters the real
leaf. Full force balance leaves an exact south neighbor and a
strict northwest neighbor at height one.

The rotated root cover forces that northwest neighbor to have
minimum height zero. Its southeast support cannot be at height
one: in the aligned case it is a bottom vertex, while in a tilted
unit its entire southeast support face lies on one actual side
of vertical span strictly less than one. This includes side means
and both endpoints and proves the strict-low case.

At `d=1`, a tilted root again contains the origin openly, and the
already fully reviewed aligned-root theorem handles the remaining
origin-side and origin-vertex alternatives. At `d>1`, that same
theorem excludes either aligned root. Of two remaining tilted
roots at least one does not contain the origin openly, so the
complete local theorem above applies with both original boundary
neighbors, without altering the second root's forces.

## 5. Circle order and full component balance

I checked the order-transfer argument with the actual physical
embedding. Circle points of distinct contained unit squares are
distinct; at a shared circle point, two disjoint right-angle inward
sectors would require the whole tangent half-plane, including a
tangent side direction unavailable to a nondegenerate square
contained in the strictly convex disk. Every body-center/contact
strand is strictly inside the containing circle. The accepted
physical uncrossing and small routing preserve the chosen actual
circle spokes, all actual force data, and weak junction limits.

The actual C4 is a Jordan cycle. A genuine boundary leaf must lie
on its exterior side, since its bridge and circle-access spoke
cannot escape from the bounded face across the cycle. Its exterior
face walk therefore meets the four marked boundary bodies in
alternating order `B,L,D,M`, up to reversal. A thin regular
neighborhood and four disjoint access arcs transfer this order to
their actual circle corners. This is valid for each choice of M's
physical corner and retains all side-contact endpoints; it makes
no change to the selected applications or forces.

Choose the upper physical circle corner of L in its radial frame.
Both B,D corners lie in the lower open semicircle. Their lower
connecting arc excludes this chosen L corner. Alternation puts
every M corner on that lower arc as well. The full circle loads
of B,D,M consequently have strictly negative transverse projection.
The genuine L resultant is radial with transverse projection zero;
the two roots are physically clear. Summing the six unchanged body
force equations cancels every original internal pair force and
would give total transverse force zero, the required contradiction.
All three arbitrary completion squares remain physical throughout.

## 6. Complete mixed-D bypass and the whole attachment join

I also read the entire saved mixed-D source and both independent
reviews, rather than relying only on its previously closed fine
checkbox. The true D root retains its actual chart
`[-s,r] x [h-1,h]`, with `0<h<1`. A distinct near-origin bypass
forces one actual vertical margin at most epsilon; reflection gives
`0<h<=epsilon`. The accepted physical shallow-side theorem applies
to both original boundary neighbors. Full vertical force balance
makes their normals horizontal. Two west normals would both have
negative moments at their real heights `y<-1/4`, while two east
normals cannot balance. The exact remaining support half-planes
are therefore west and east, with all original application means.

The bypass contacts make its horizontal projection contain the
root's whole unit-length interval. I checked the complete physical
separating-axis calculation, including zero axis components. With
width `w=c+t`, projection containment gives `|u|<=(w-1)/2`, and
any tilted separating side reduces to vertical separation because

    (1-t)*(w+1)-c*(w-1) = 2*c*(1-t) >= 0.

The near point excludes the lower placement. Consequently the
actual west boundary unit reaches height at least h, while its
original root contact is below `-1/4`. Its complete aligned and
tilted corner cover gives strict squared bounds `185/64` in the
aligned case and `73/64`, `157/64`, `249/64`, `2425/576` in the
tilted case. The first three are below four and the last is below
`17/4`. Thus physical boundary contact is impossible, independently
of that neighbor's degree, mask, weights and additional contacts.

The whole mixed orbit follows by the actual opposite-root swap:
below or at `d=1` the open-origin D root overlaps the closed-origin
S root; above it the S root supplies exactly the required real
near-origin bypass. D/D is excluded by the accepted two distinct
open-origin D roots. S/S is the complete proof in Sections 2--5.
The actual BD load set and these three leaf-type orbits exhaust
the original opposite-root attachment. Thus both original IDs

    M6.B4L2.C4.OPPOSITE.LBD.SS
    M6.B4L2.C4.OPPOSITE

have complete whole-family exits after this root review and the
separate full assembly review. The mixed fine ID was already
closed upstream and is not newly counted. The unrestricted C1.4.b2
parent, other attachment layouts, sharp nine-square theorem and
every original equality packing retain their separate obligations.

No Lean compilation, CI, workflow dispatch, numerical pose, force
deletion, normal reselection or remote mutation was used in this
review. Every original degree, positive force, physical circle mask,
individual zero weight and actual shared-side mean is retained.
