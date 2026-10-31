# Boundary edges are exterior, and a diamond cannot have two boundary hubs

Date: October 25, 2026.

**Status: accepted complete hand topological implication and whole-family
applications after independent saved-source and scope review in
REVIEW_BOUNDARY_EDGE_DIAMOND_EXCLUSION_2026_10_25.md.** Eight existing
gates are discharged. No coefficient certificate is introduced.

Work with the original nine interior-disjoint closed unit squares in

    79/40 <= R <= sqrt(1105)/16,

and their common selected planar physical positive body graph. Its
vertices are the actual square centers. Its edges are the original
positive body pairs, aggregated at their actual application means.
All physical zero-stress contacts and every original square remain.

Two statements hold:

1. A positive edge joining two physically circle-touching bodies is
   incident to the unbounded face of a sufficiently close physical
   embedding of the selected graph.
2. Such an edge has at most one common positive neighbor. In
   particular, a positive diamond cannot have both hubs physically
   circle-touching.

The hypotheses concern physical circle contact, not positive circle
weight. They impose no positive-degree assumption on any vertex and
permit arbitrary additional positive edges outside the displayed
subgraph. No normal, force, mean or square is changed.

## 1. Two already complete geometric inputs

CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md, Sections 3--4, applies to
any physically touching boundary pair U,V. Choose any actual common
point p and one actual circle corner z_U,z_V of each body. The path

    z_U -- c_U -- p -- c_V -- z_V

is a simple crosscut of the disk. Together with the shorter circle
arc from z_V to z_U, it bounds the exterior pocket Omega. No other
physical unit square has its open interior in Omega. This theorem
requires no circle-weight positivity, degree condition or additional
boundary body. It retains all other original squares.

NO_POSITIVE_K4_SUBGRAPH.md, Sections 1--2, gives two further precise
facts about the selected physical embedding:

* it can be constructed in arbitrarily small neighborhoods of the
  actual center/contact strands, fixing all body centers and
  preserving their physical cyclic port orders;
* if its neighborhoods are sufficiently small (the displayed
  choice epsilon<1/80 suffices), no embedded three-cycle encloses
  another body center.

The latter is a geometric theorem for every three-cycle, not just a
step valid when the graph is K4. Its proof contracts the three
center/contact strands to a contact triangle. Each triangle side
has length at most sqrt(2), hence area at most sqrt(3)/2. The
concentric inner square of side 19/20 belonging to an allegedly
enclosed body has area 361/400>sqrt(3)/2 and stays disjoint from
the strand homotopy, giving the contradiction. This proof includes
coincident contact points and arbitrarily small junction routing.

## 2. Circle-corner rays can be kept in the physical embedding

Fix one positive boundary edge UV and take p to be its actual
application point, including an arbitrary original shared-side mean.
Choose actual circle corners z_U and z_V. Consider the auxiliary
segments

    rho_U=[c_U,z_U],       rho_V=[c_V,z_V].

Their open parts lie in their respective square interiors. They
meet each other neither in their interiors nor at their circle
endpoints. As recalled in the exterior-pocket source, a physical
circle point cannot belong to two distinct packing squares.

Every original center/contact half-strand in U joins c_U to a
physical contact point q on its boundary. Its ray differs from
the ray c_U--z_U: if they had the same ray, the unique intersection
of that ray with the boundary of the convex square would give
q=z_U, contrary to the preceding circle-point fact. Therefore
rho_U meets the other half-strands in U only at c_U. Half-strands
of other bodies have open parts in those bodies' open interiors,
so cannot meet rho_U's open part. The same statements hold at V.

There are only finitely many strands and contacts. Away from small
center disks, the two auxiliary rays therefore have positive
clearance from every strand except their own endpoints. The
center disks can be chosen so that each circle ray occupies the
unused sector between its adjacent incident strand directions.
Use the existing physical embedding construction with tubes and
junction disks smaller than these clearances, and retain those
unused sectors when routing the center stars.

This makes a plane embedding of the original positive graph
together with both auxiliary rays. The rays are geometric aids,
not selected stress edges. No junction normal or matching is
altered. The original uncrossed local routing is used at every
multiple-square contact; neither auxiliary ray meets a contact
junction. An original shared-side mean may be at either endpoint
of its physical overlap interval without affecting this argument.

All positive center/contact strands are strictly inside the disk:
their centers are interior and a common pair-contact point cannot
be on the circle. Finiteness gives a positive circle clearance for
their union. Choose the embedding neighborhoods smaller than that
clearance as well, so every embedded positive edge stays strictly
inside the disk. The shorter circle arc between z_U and z_V is
then disjoint from the positive graph and both ray interiors.

These restrictions are compatible with an arbitrarily small
physical embedding and hence with the no-enclosed-center theorem
in Section 1. They constrain only the proof drawing of the
already selected graph, not the physical certificate.

## 3. The actual boundary edge is incident to the unbounded face

Let e_UV be the embedded positive edge from c_U to c_V. With the
two rays and shorter circle arc, it forms a simple closed curve J:

    c_U -- z_U -- (short circle arc) -- z_V -- c_V
          -- (embedded edge e_UV) -- c_U.

Its simplicity follows from the augmented plane embedding of
Section 2. The auxiliary circle arc lies on the disk boundary;
the positive edge lies strictly inside it.

Replace e_UV by its original center/contact strand c_U--p--c_V.
The corresponding closed curve is the exterior-pocket boundary
from Section 1. Every other body's center lies strictly outside
that pocket. Indeed its open square interior avoids the original
crosscut, and an interior center in the pocket would place the
whole open square there, contradicting the complete exterior-pocket
theorem. No other center lies on that boundary either.

The embedded edge is homotopic relative to its endpoints to the
original strand inside an arbitrarily small neighborhood of U union V,
as in the physical embedding source. This homotopy avoids every
other body center: each such center has its open inscribed disk of
radius 1/2 disjoint from U and V, so its distance from their union
is at least 1/2. In particular an epsilon<1/80 neighborhood is
sufficient. Keep the two rays and the circle arc fixed during the
homotopy. Winding number about every other center is unchanged.

Since J is simple and the original pocket winding number is zero
at every other center, the bounded side of J contains no other
graph vertex. It also contains no positive graph edge. To see
the latter without an empty-face assumption, any edge entering
that bounded side must remain there until one of its endpoints:
it cannot cross J in the augmented plane embedding. Its only
possible endpoints there or on J are c_U and c_V. The graph is
simple after body-pair aggregation, so the only edge with those
two endpoints is e_UV itself, already in J; loops are absent.
Every other positive edge has an endpoint outside and cannot
enter the region. There is no component of the graph without
a vertex inside it.

Consequently a point immediately on the J-interior side of an
interior point of e_UV can be joined through that empty region
to the auxiliary circle arc and then to infinity, avoiding the
original positive graph. The auxiliary rays and circle arc are
not part of that original graph and need not be avoided in the
last passage. Thus e_UV is incident to the unbounded face.

**Theorem 3.1.** Every positive boundary-to-boundary edge has the
stated exterior-face property. The proof permits a different
auxiliary pair of rays for each application, always in an
arbitrarily small physical embedding satisfying Section 1.
No simultaneous choice of stress or contact normal is involved.

## 4. Two common positive neighbors would force an enclosed center

Suppose U,V are physically boundary and the positive graph
contains two distinct common neighbors A and B. Retain exactly
the four vertices and the five positive edges

    UV, UA, VA, UB, VB.

The graph is a diamond. Extra positive edges at these vertices,
including AB if it happens to be present, are removed only from
the proof drawing, not from any equilibrium equation. A subgraph
argument makes no claim that the extracted smaller graph is
itself a positive stress certificate.

Choose the physical embedding from Section 3. Removing other
vertices and edges cannot remove e_UV from the unbounded face:
the same path from its exterior side to infinity still avoids
the smaller graph. The restricted diamond remains plane.

Its three internally disjoint U-to-V paths are the direct edge,
U--A--V and U--B--V. As the diamond is biconnected, each face
boundary is a simple cycle. The only simple cycles containing
the direct edge UV are U--A--V--U and U--B--V--U. Since UV is
on the unbounded face, that face is bounded by one of those
triangles. The other tip vertex lies strictly inside the triangle.

That triangle is also an embedded three-cycle of the original
positive graph. The other tip is an original body center, so
Section 1's no-enclosed-center theorem gives a contradiction.

**Theorem 4.1.** A positive edge whose endpoints both physically
touch the circle has at most one common positive neighbor.
Equivalently, in every positive diamond at least one hub is
physically circle-clear. This is independent of all four actual
positive degrees, circle-weight splits, force magnitudes and
additional contacts. It also excludes a diamond whose two hubs
physically touch the circle with zero circle multipliers.

The central edge must belong to the selected positive graph.
This theorem does not silently add an arbitrary zero-stress
physical edge to that graph; its junction routing need not
remain planar after such an addition.

### 4.1. A degree-three diamond-hub pair is a forbidden local pattern

Suppose the actual positive graph has adjacent vertices U,V with
exact positive neighborhoods

    N_+(U)={V,A,B},       N_+(V)={U,A,B},

where U,V,A,B are four distinct physical bodies. The degrees,
loads and additional positive neighbors of A and B are arbitrary.
Zero-stress physical contacts at U and V are also retained.

NO_UNLOADED_DIAMOND_HUB.md applies to U: among its three actual
neighbors, V physically touches both A and B. Thus U has
strictly positive total circle load. Interchanging U and V
gives the same conclusion at V. Both hubs physically touch
the circle, contrary to Theorem 4.1 for their actual positive
diamond.

**Corollary 4.2.** No such adjacent exact-degree-three hub pair
occurs in the common selected positive graph throughout the
declared radius window. This is a uniform local forbidden
pattern in any component size, not only a four-body block.
It does not assume that A or B has degree two, carries a leaf,
or has any specified physical circle mask. A fourth positive
force at U or V invalidates the degree-three load argument
and is never deleted to apply this corollary.

## 5. Two entire C1.5.b1 rooted types are excluded

Use the original labels and complete load cover of
FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md. The subdivided K4 has
the exact positive edges

    AX, XB, AC, AD, BC, BD, CD.

Its C,D hubs and A,B tips contain the positive diamond

    CD, CA, DA, CB, DB.

If the genuine leaf is at X, the unchanged exact-degree-three
vertices C and D are forced loaded by the original degree/load
cover. They are therefore physically circle-touching. Theorem 4.1
excludes the entire graph for both genuine S and D leaves.

If the genuine leaf is at A (or the symmetric B), C and D again
retain their exact degree-three neighborhoods and are forced
loaded. The same contradiction excludes this entire rooted
graph. The already excluded S branch is included, and the
remaining D branch is now excluded without restricting its
actual side-interior root slider.

These arguments retain the real extra leaf force at the actual
root and all three arbitrary physical completion squares. They
use no force equation on a contracted or isolated five-body
block. Both whole rooted types close, not just their displayed
physical corner masks. The third subdivided-K4 root orbit,
with a leaf at C or D, is not covered: that root is physically
clear and the remaining loaded sets do not force both diamond
hubs boundary.

## 6. The whole two-tip-leaf diamond layout is also excluded

Use the C1.4.b2 diamond with hubs H,K, tips B,C, and one genuine
leaf at each of B and C. The exact positive diamond edges are

    HK, HB, HC, KB, KC.

The roots B,C retain their actual extra leaf forces. The unchanged
hubs H,K each have exact positive degree three, and each one's
neighbors contain the two physical edges from the other hub to
both tips. NO_UNLOADED_DIAMOND_HUB.md therefore forces both
H and K loaded, just as in the accepted original load cover.
Both physically touch the circle, contradicting Theorem 4.1.

The argument includes all SS, SD and DD genuine leaf types,
all positions and original circle masks, every shared mean and
all three completion squares. DD was already excluded by the
distinct-D-root theorem; no dependency on that separate exit
is needed here. This excludes one entire additional attachment
layout of C1.4.b2, without modifying the hubs' genuine equations.

## 7. Exact existing-gate consequences, independently accepted

No new ID is needed. The original complete load covers supply
the entire scopes of exactly these eight previously open IDs:

| Existing ID | Complete new exit |
| --- | --- |
| M6.B5L.SUBDIVIDED_K4.NEW.LCD.S | Subdivision root X, whole S leaf domain |
| M6.B5L.SUBDIVIDED_K4.NEW.LCD.D | Subdivision root X, whole D leaf domain |
| M6.B5L.SUBDIVIDED_K4.NEW | Both leaf types and sole complete CD load orbit |
| M6.B5L.SUBDIVIDED_K4.ENDPOINT.LCD.D | Subdivided-edge endpoint root A, whole D leaf domain |
| M6.B5L.SUBDIVIDED_K4.ENDPOINT | Whole rooted graph, including the already closed S branch |
| M6.B4L2.DIAMOND.TWO_TIPS.LHK.SS | Both actual leaves S, entire HK load orbit |
| M6.B4L2.DIAMOND.TWO_TIPS.LHK.SD | Both mixed-leaf placements, entire HK load orbit |
| M6.B4L2.DIAMOND.TWO_TIPS | Whole rooted attachment, with every genuine leaf type |

This improves the C1.5.b1 rooted-type cover from two closed of
sixteen to four closed of sixteen, leaving twelve whole rooted
types and thirty-six necessary block-load orbits. It does not
close the whole C1.5.b1 or C1.4.b2 coarse cell. The uniform
Theorem 4.1 may be applied inside any larger selected graph
whenever its actual positive edges and two physical boundary
hubs satisfy the stated hypotheses.

All existing common-certificate prerequisites retain their
original scope. No secondary minimizer is added by this
topological implication. No computational sign certificate,
numerical pose cover, Lean compilation, CI or workflow dispatch
is used.
