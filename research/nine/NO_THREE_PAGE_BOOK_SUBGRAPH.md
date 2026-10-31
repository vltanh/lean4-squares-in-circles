# A positive edge belongs to at most two triangles

Date: October 25, 2026.

**Status: accepted complete radius-free hand implication after independent
saved-source review in REVIEW_K23_LEAF_AND_BOOK_EXCLUSIONS_2026_10_25.md.**
Its existing-gate applications are accounted for in the complete assembly.

Work with the selected simple positive physical body graph of
interior-disjoint unit squares. Use its arbitrarily close physical
plane embedding from PHYSICAL_BODY_GRAPH_UNCROSSING.md and
NO_POSITIVE_K4_SUBGRAPH.md, Section 1. No containing-radius bound,
circle load, exact degree or secondary minimizer is required.

**Theorem.** Every positive edge has at most two common positive
neighbors. In particular the selected graph contains no three-page
book: there cannot be distinct bodies H,K,A,B,C with all seven
positive edges

    HK, HA, KA, HB, KB, HC, KC.

All additional positive forces and physical zero-stress contacts
remain. This is a subgraph implication, not the deletion of a force
from an equilibrium equation.

## 1. Every positive triangle bounds an empty graph face

NO_POSITIVE_K4_SUBGRAPH.md, Section 2, proves that no embedded
three-cycle encloses another body center in a sufficiently close
physical embedding. This statement is independent of its later
K4 application and has no radius premise. Its contact-triangle
area and inner-square argument includes coincident physical
applications and arbitrarily small junction-routing disks.

Let T be any embedded positive three-cycle. Its bounded side
therefore contains no graph vertex. It also contains no graph
edge: an edge entering the bounded region cannot leave it
without crossing T, unless it ends at a vertex of T. Such an
edge would have both endpoints among T's three vertices, but
the selected body graph is simple and all three corresponding
edges already belong to T. Loops are absent. No other edge or
component can lie in that region without a vertex there.

Thus the bounded region of T is a face of the positive graph.
Every positive three-cycle is the boundary of a bounded
triangular face.

## 2. The two sides of one edge give the bound

An interior point of a plane embedded edge has two local sides.
At most one face occupies either side. Distinct triangular
cycles containing that edge have distinct third vertices and
distinct bounded face boundaries, by Section 1. Therefore at
most two such cycles contain the edge, one on each possible
side. The edge has at most two common positive neighbors.

For a three-page book, the central edge HK belongs to the
three distinct positive triangles HKA, HKB and HKC. This
contradicts the two-sided bound. This also gives the conclusion
when the book has additional edges, arbitrary tip degrees or
zero circle weights at every displayed vertex.

## 3. Scope and consequence for attached books

The common selected embedding is the only certificate input.
The small geometric drawing does not move any physical body,
normal, contact mean or original force. The proof applies to
every component size and any larger graph containing the
specified seven positive edges.

Consequently every three-page-book leaf attachment in C1.5.b1,
including both a hub root and a page root, is impossible without
using its original load or S/D leaf cover. The exact existing
page-root gate consequences are included in the broader
SPANNING_K23_LEAF_BLOCK_EXCLUSION.md assembly. No new gate
or computational certificate is introduced.

The conclusion is for the selected positive graph. It does not
assert that the entire physical touching graph is planar or
that arbitrary zero-stress contacts can be added to this
embedding. No Lean compilation or CI is used.
