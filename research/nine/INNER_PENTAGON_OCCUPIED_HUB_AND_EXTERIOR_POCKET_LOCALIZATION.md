# An occupied inner pentagon leaves every completion square in its exterior pockets

Date: October 28, 2026. Author: mixed_blocks.

**Status: complete proposed physical localization theorem, frozen for
full independent and root review.** The whole original H2/H3
families are not excluded here. The new weak-junction and whole-unit
argument puts all three actual completion squares outside the original
five-unit rim. The complete boundary-pocket join then leaves one or
two explicitly listed actual exterior pockets in each remaining load
family. No exterior capacity is assumed or claimed.

Keep all nine actual interior-disjoint closed unit squares in the
original selected physical certificate and radius window

    79/40<=R<=sqrt(1105)/16.

The original six-body biconnected component has outer-face cycle
0-1-2-3-4-0 and the actual interior vertex H. Every original spoke,
chord, force, circle mask, zero individual weight, side mean and
physical zero-stress contact stays. In particular H has not been
replaced by a point or by a free-area allowance.

**Theorem.** Every one of the other three actual unit squares lies
wholly, in the sense of its open interior, in the exterior of the
actual rim. Cut that exterior by simultaneous real circle spokes at
the positive-load rim bodies. Each whole extra belongs to one of
the resulting actual circle pockets. A pocket whose rim arc is a
direct contact of two such boundary bodies contains no extra.

The complete consequences for the five still-relevant H2/H3 load
representatives are the table in Section 5. Every reflected image,
physical zero-weight circle mask and weak contact junction is included.

## 1. The actual inner side, with the original hub retained

For the unchanged rim edge i--(i+1), let p_i be its original actual
aggregate contact point. Several p_i may coincide. Let c_i be the
actual center of rim square i, and let

    Gamma=c_0 p_0 c_1 p_1 ... c_4 p_4 c_0             (1)

be the actual center/contact loop, with multiplicities retained.
All of its segments belong to the closed rim squares. It need not
be Jordan at a multiple junction; no simplicity is assumed for (1).

The common selected physical embedding has this cycle as the outer
face boundary and the actual H center in its bounded face. The
bc98 construction permits arbitrarily small compatible resolutions
of the contact junctions and of coincident same-body strands. These
resolutions preserve the full original cyclic sector order, including
all H spokes and every positive outer chord. Restrict one such
embedding to the rim, obtaining a Jordan curve Gamma_delta.

Every point in the open interior of H, or of an extra unit, avoids
all five closed rim squares. Indeed, an open neighborhood of a point
of a closed unit square meets its open interior. Membership in another
unit's open interior would therefore violate physical nonoverlap.
In particular the four non-rim centers under consideration have
positive distance from the closed rim union. Here the actual centers
are those of H and the three extras; the same statement applies to
any additional test points used below.

Choose the junction and tube neighborhoods smaller than the distances
of these finitely many centers. Every sufficiently small resolution
then has the same winding at each center as (1). The original
outer-face contract gives winding one at c_H, after orienting the
rim positively. Any extra center has winding zero or one. Because
its entire open square is connected and avoids (1), that winding
is constant throughout its open interior. The same is true for H.

Thus an extra is a whole inner unit or a whole outer unit at this
stage. A mean on a shared side, a tangential extra, or a common
multi-unit junction cannot make one open square cross the actual rim.
This is actual region membership, before any area bound is used.

## 2. Full weak-contact extension of the five-ring area bound

We justify the area calculation at every permitted junction, rather
than assuming the actual contact points in (1) are distinct.
Move each rim center toward its actual contact-chord midpoint:

    c_i(t)=(1-t)c_i+t(p_(i-1)+p_i)/2,  0<=t<1.       (2)

It stays in the open interior of its original square. If its two
contacts are distinct, the two open segments from c_i(t) to them
are disjoint except at c_i(t). If they are opposite collinear rays,
they still meet only at that center. If the contacts coincide, keep
two separate parallel strands in their original contiguous tangent
sector, joined only at c_i(t). This is the same local two-strand
resolution used in the original compatible embedding; it does not
identify the two rim edges.

For any interior base point in a convex square, the cyclic order of
its distinct boundary rays is the boundary order of those contact
points. That order does not change during (2). Coincident contacts
retain their original order in the common junction's physical sector
drawing. At a junction shared by different squares, the same
noncrossing selected local drawing is therefore available for every
t<1. Different squares' open segments cannot intersect. Consequently
each loop in (2) has arbitrarily close simple resolutions with the
same original rim rotation. They can be chosen continuously on any
closed subinterval t<1, with shrinking junction neighborhoods.

Take t tending to one and resolution sizes tending to zero. These
Jordan curves converge uniformly to the actual five-vertex contact
polygon

    P=p_0 p_1 p_2 p_3 p_4 p_0,                     (3)

with its edge midpoints inserted. They all have winding one at c_H:
the center contraction is inside the closed rim squares and therefore
avoids H, while the resolutions can avoid its center by the positive
distance established in Section 1. Thus all approximants have the
same positive orientation.

For every point off (3), winding is unchanged by a sufficiently
small uniform perturbation of the curve. It follows that the winding
of P is always zero or one off its edges. This conclusion includes
coincident polygon vertices, zero chords, self-tangencies, and retraced
pieces. In particular no cancellation of positive and negative lobes
can hide completion area.

The homotopy (2) lies in the closed rim union. For H and for every
extra classified as inner in Section 1, it therefore preserves
winding one throughout the entire connected open unit. Let G be
the winding-one region of P. All these whole open units lie in
G outside the closed rim union.

Write l_i=|p_i-p_(i-1)|<=sqrt(2). The complete long-chord lemma
of CONTACT_RING_HOLE_AREA applies unchanged. When l_i>1, the
open chord lies in the open interior of its own rim unit. No other
polygon edge can enter that open unit. Across the positively oriented
chord winding jumps by one; since its only values are zero and one,
the connected inward part of the actual square has winding one.
That occupied part has area at least

    (1/2)sqrt(l_i^2-1).

Different occupied parts have disjoint interiors. For l_i<=1 no
positive subtraction is claimed. Hence the full free winding-one
area satisfies

    area(G outside the closed rim union)
      <= A(P)-(1/2)sum_i sqrt(max(l_i^2-1,0)).       (4)

Here A(P) equals the ordinary signed polygon area because all
winding values are zero or one. The complete finite Fourier polygon
inequality, valid also for degenerate polygons, gives

    A(P)<=C sum_i l_i^2, C=(1/4)cot(pi/5)<1/2.

For x in [0,2], the entire scalar function

    C x-(1/2)sqrt(max(x-1,0))

is at most C. On [0,1] this is immediate; on [1,2] it is convex
and the endpoint values are C and 2C-1/2<C. Thus (4) is at most

    5C=(5/4)cot(pi/5)<2.                            (5)

For completeness, cot^2(pi/5)=1+2/sqrt(5)<64/25,
because 50<39sqrt(5), whose positive squared reserve is
5*39^2-50^2=5105. This proves the strict comparison in (5).
The whole continuous area and chord arguments have included every
original contact mean, without a chosen-vertex or generic-position
assumption.

## 3. The real occupied H excludes every inner extra

Section 1 placed the actual open H at winding one, and Section 2
preserved that placement through the actual contact homotopy. It
contributes its full area one to the free region in (4). If any
one of the three actual extra units were inner, it too would
contribute its full unit area there. Their interiors are disjoint.
This would give area at least two, contradicting the strict (5).

Therefore every actual extra is outer. This is not a count of
unoccupied abstract graph faces: the real H is one of the occupied
units in the area contradiction. It is also not an assumption that
an extra whose center is inner fits inside a small polygon. Its
whole open interior was localized before area was compared.

The proof is independent of H's degree, its spoke owners and the
presence of allowed outer chords. It applies to every original
six-body inner-pentagon domain, including the exact H2/H3 cases
used below, without deleting an edge or splitting a force.

## 4. One simultaneous exterior-pocket partition

Select one actual circle corner on every positive-load rim unit.
Use the simultaneous center-to-circle spokes of bc98 in the same
rim embedding. Their open segments belong to their actual units;
different spokes are disjoint, and none meets the rim except at
its own rim center. They lie in the exterior annulus, since their
circle endpoints are outside the Jordan rim. Resolve any contact
junctions compatibly and as narrowly as in Sections 1--2.

Cutting the annulus along these disjoint spokes gives the actual
pockets between successive marked rim bodies in their rim order.
The annular crosscut argument fixes this same cyclic order on the
containing circle. The complete corner-direction intervals in
CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS Section 2 ensure that any
physical two-corner choice preserves it. No circle point is shared
by two actual units.

The actual unperturbed pocket boundaries consist of rim center/contact
paths, the two endpoint circle spokes and a circle arc. Their
non-circle pieces lie in closed core units. Every extra's connected
open interior avoids all these pieces and lies strictly inside the
containing circle. Using its center to choose a component, then
the same shrinking-neighborhood winding argument as in Section 1,
places the whole open extra in one of these actual pocket regions.
At a weak junction this means the union of the corresponding free
subregions on that side of the occupied boundary; it does not
permit an extra to cross a core square or a collapsed crosscut.

All initially unmarked physical boundary units and all zero-stress
contacts stay. Their circle spokes or physical contacts may further
subdivide these pockets. They cannot connect regions through the
already occupied barriers or enlarge the listed allowed union.

If a marked rim arc consists of a direct physical boundary contact
A--B, its corresponding circle arc is the one with no other marked
body between them. The physical angular-neighbor theorem identifies
it as their minor ordered corner arc. There are at least three
marked rim bodies, so the complementary arc contains another marked
body and cannot be the pocket chosen by the common annular order.

This direct pocket is precisely the complete exterior boundary-pair
pocket of CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS Sections 3--4.
That theorem includes all actual point/side contacts and arbitrary
other packing units. Its simultaneous dilation argument excludes
every whole additional unit in this pocket. Only this force-free
completed theorem is used; no radial displacement of the present
packing or its certificate is performed here.

Thus every extra belongs to a pocket whose rim path includes at
least one actual zero-load rim body. There is no capacity assertion
for such a longer pocket in this manuscript.

## 5. Complete original five-family localization

Use the exact original graph/load table cfe85a20. The H2_D0 graph
has spokes H0,H2 and reflection i->2-i modulo five. The H3 graph
has spokes H0,H1,H3 and reflection i->1-i. The actual H remains
inside the same outer rim in every listed image. The following
table lists paths in cyclic rim order; reversing a path names the
same pocket.

| Original graph/load representative | Direct boundary pockets excluded | Entire allowed exterior union for all three extras |
| --- | --- | --- |
| H2_D0.L013 | 0--1 | 1--2--3 and 3--4--0 |
| H2_D0.L1234 | 1--2, 2--3, 3--4 | 4--0--1 only |
| H3.L024 | 4--0 | 0--1--2 and 2--3--4 |
| H3.L1234 | 1--2, 2--3, 3--4 | 4--0--1 only |
| H3.L0124 | 0--1, 1--2, 4--0 | 2--3--4 only |

All four-load rows have exactly one zero-load rim body. That body
is physically circle-clear: otherwise all five rim units would
form a physical boundary C5, forbidden by the full e54 physical
boundary-graph theorem. Every extra in such a row is in the one
displayed two-edge pocket through this actual clear degree-three
rim body. Neither its third force to H nor an endpoint's extra
force is removed.

In each three-load row there are two zero-load rim bodies, each
between two positive boundary rim neighbors. Neither, or exactly
one, may physically touch the circle. Both cannot, by the same
physical C5 exclusion. If one does, insert its actual circle
spoke in the same partition. Both direct boundary-contact pockets
incident to it are empty by Section 4. The original two-edge
pocket through that zero-load body consequently contains no whole
extra, so every extra lies in the other listed pocket. This covers
the complete physical zero-weight mask refinement without changing
its selected total load or assigning it a new force equation.

The actual H2 reflection carries all paths, loads and spokes
together; for example L013 goes to L124. The H3 reflection likewise
carries L024 to L124, L1234 to L0234, and fixes the L0124 orbit.
No reflected image is omitted or counted as a new domain.

The separate complete H3.L0134 exclusion does not enter this table
and receives no duplicate credit. The five displayed load families
and the joint capacities of their remaining pockets stay open here.

## 6. Exact frozen inputs and verification boundary

| Source | SHA256 | Complete operative scope |
| --- | --- | --- |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a | Entire original outer-rim/interior-H contract, H2/H3 loads, actual degrees and reflected images. |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Full original local sector order, compatible multiple-strand resolutions, one simultaneous plane embedding and physical circle spokes. |
| CONTACT_RING_HOLE_AREA.md | 50034e7eabf4812c6a9f87a801f07dabe7a444d723c62fdc63d096c6ceb0ec6f | Complete Sections 1--4 long-chord area, winding subtraction and exact polygon inequality; all weak-junction and occupied-H joins are proved above. |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Complete Sections 2--4 physical corner order, actual exterior boundary-pair pocket and whole-pocket exclusion with all other units retained. |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Complete actual boundary-neighbor order and physical C5 exclusion, including zero circle multipliers. |

All five pins, the exact cotangent comparison, every listed path
partition and both graph-preserving reflection maps were checked.
The new theorem concerns complete actual regions and whole units;
it uses no pose sample, auxiliary stress polygon, fictitious
capacity or shortened positive star. No shared ledger, original
fine label, frozen source, remote object, Lean file, CI or workflow
was changed. Neither the six-body parent nor the unrestricted
bound or equality classification is closed by this localization.
