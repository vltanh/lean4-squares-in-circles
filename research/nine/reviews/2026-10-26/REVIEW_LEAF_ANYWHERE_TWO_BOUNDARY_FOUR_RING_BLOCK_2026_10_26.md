# Independent review of the leaf-anywhere two-boundary four-ring exclusion

Date: October 26, 2026.

**Result: PASS for the complete stated geometric theorem and its K2,3
corollary.** This is an independent saved-source and original-domain
review of LEAF_ANYWHERE_TWO_BOUNDARY_FOUR_RING_EXCLUSION.md. No new
roadmap gate or complete larger-component family is inferred here.

## 1. Exact theorem and dependency scope

I read the complete new source and separately checked the full enclosed
unit equality proof and cross comparisons in Sections 1--3 of
SPANNING_K23_LEAF_BLOCK_EXCLUSION.md. The new proof uses its degree-free
Lemma 2.1, not its older root-on-ring exclusion or six-body load count.
Thus the new genuine leaf is allowed anywhere in the full selected
positive graph. Every original ring degree, force, mean and physical
circle mask remains unchanged.

The enclosed-unit lemma retains the original winding-one contact polygon,
its complete area equality chain, the coincident-application cases and
the equality characterization forcing an aligned cross. In particular,
it does not assume in advance that the ring's free region is convex.
The hypothetical enclosed physical unit is what forces the exact square
contact polygon and the four full-side exterior neighbors.

I also read the relevant original statements in
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md, Sections 3 and 6, and
PHYSICAL_BODY_GRAPH_UNCROSSING.md, Section 6. The former supplies a
point of the actual genuine-leaf root at distance at most
max(R-2,0), without a root-degree restriction. The latter supplies a
simultaneous arbitrarily small compatible embedding in which every
physical circle-touching positive vertex is exterior, irrespective of
its selected circle weights.

## 2. Cross comparison and the strict interior disk

For a common-frame unit centered at (a,b), the farthest corner has
squared norm (|a|+1/2)^2+(|b|+1/2)^2. I independently reconstructed
both cases of the boundary-ring comparison.

An opposite boundary pair first makes the corresponding central
coordinate zero. Containment of the farther perpendicular ring unit
then makes the other coordinate zero. Its forced radius squared is
5/2, contrary to the exact lower reserve 2241/1600.

For an adjacent boundary pair, choose them as right and top by a global
rotation/reflection about the unchanged circle origin. Containment of
left and bottom gives x,y>=0; the two boundary equalities then give
x=y=t. The common squared radius is 2t^2+4t+5/2. I verified

    221/50 - 1105/256 = 663/6400 > 0,
    (25/12)^2 - 1105/256 = 55/2304 > 0.

Therefore t<2/5 and the entire closed radius-1/10 disk belongs to
the OPEN interior of the central unit T. This is a strict inclusion,
including every endpoint of that closed disk; no translation of the
origin is used. The genuine-leaf root H meets the strictly smaller
radius-1/12 disk.

The conclusion H=T is valid for actual physical bodies. If a point of
H lies in int(T), then a neighborhood of that point lies in int(T).
Every point of the nondegenerate closed square H is a limit of points
of int(H), including its edges and vertices. Thus H distinct from T
would give an open-interior overlap. No unsupported inference from
boundary intersection alone is being made.

## 3. The topological contradiction at the identified root

The genuine degree-one leaf L is physically boundary by its original
one-force equation and radial classification. In the complete compatible
plane graph it is therefore incident to the unbounded face. A true
degree-one vertex has only one incident face, and its sole edge has
that face on both local sides. Its root H is consequently incident to
the same unbounded face.

The hypothesized enclosed unit T is not one of the four ring vertices,
and its center is strictly inside their simple embedded cycle. After
H=T has been forced by physical nonoverlap, this simple cycle separates
H from infinity. Such a vertex cannot be incident to the unbounded
face of the complete graph, whether or not additional edges or other
components are present. This contradicts the preceding genuine-leaf
argument. The graph is not simplified for any force equation.

The compatible routing can be chosen simultaneously: the accepted
enclosed-unit argument permits arbitrarily small neighborhoods avoiding
an inner concentric square in T, while the exterior-face construction
preserves all selected center-to-circle spokes. Thus weak contact
junctions and actual shared-mean endpoints cause no new exception.

## 4. The K2,3 corollary and exact limitations

The six original K2,3 edges form a biconnected plane subgraph. Its outer
face boundary is a simple four-cycle containing the two hubs and two
pages; the third page is strictly enclosed. A physical boundary vertex
retains its access to the unbounded face on restriction to a subgraph.
Hence all hypothesized physical boundary members of this K2,3 belong
to its outer four-cycle. The new theorem applies with the unchanged
genuine leaf from the complete graph, regardless of its root's location.

Additional chords, root forces, attachments, zero-weight physical
contacts and all nine occupied units remain present. The actual
two-boundary-member premise must still be established in any larger
component; it is not implied by a global count of loads lying elsewhere.
The source correctly adds no new original gate and claims no closure of
an unrestricted larger coarse cell, sharp inequality or equality audit.

No computational certificate, numerical pose, Lean compilation or CI
was needed for this review.
