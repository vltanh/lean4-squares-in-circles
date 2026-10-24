# Three boundary bodies cannot have two common positive neighbors

**Status: complete hand topological implication; independent hand audit passed.** In the selected planar physical positive graph, no two distinct body vertices can have three distinct common neighbors all of which physically touch the containing circle.

This is a graph obstruction with the physical exterior-face hypothesis. It does not assert that an arbitrary physical touching graph is planar, or exclude every abstract K2,3 when its three intermediate bodies are circle-clear.

## 1. Input and statement

PHYSICAL_BODY_GRAPH_UNCROSSING.md supplies a plane embedding of the selected positive body graph in which every physically circle-touching body vertex lies on the unbounded face. All contacts and bodies are actual physical ones.

Suppose two vertices U,V had three distinct common positive neighbors B1,B2,B3, each circle-touching. Retain just the five vertices and the six edges

\[
                   UB_i,\quad VB_i,\qquad i=1,2,3.
\]

They form a K2,3 subgraph. Additional positive edges or physical zero-stress contacts do not affect this subgraph argument.

## 2. The outside face of a plane K2,3

The three paths U--Bi--V are internally vertex-disjoint. Each simple cycle of K2,3 consists of two such paths and has length four. The graph is biconnected, so every face boundary in a plane embedding is a simple cycle. In particular its unbounded-face boundary consists of U,V and exactly two of B1,B2,B3.

For completeness, a repeated vertex on a face boundary of a connected plane graph separates the incident sectors leading to distinct parts of that boundary; deleting it disconnects those parts. Thus a biconnected plane graph has no repeated boundary vertex. The face boundary is therefore one of the four-cycles just listed.

The third Bi is strictly on the bounded side of that outside four-cycle and is not incident to the unbounded face. Equivalently, among three embedded U--V paths, two bound the outside region and the third runs between them.

Removing edges and vertices from a plane graph cannot take a surviving vertex off the unbounded face: a curve from that vertex's outside sector to infinity which avoided the old graph still avoids the smaller graph. Hence every Bi that was on the original unbounded face must remain on the unbounded face of the K2,3 subgraph. This contradicts the preceding paragraph.

**Theorem 2.1.** No two vertices of the selected physical positive graph have three common neighbors that all physically touch the circle.

The conclusion retains additional graph edges, zero circle multipliers, shared contact points and all independently oriented squares. Its only geometric input is the already established physical exterior-face embedding. It applies throughout every coarse cell.
