# Independent review: the entire pure triangle block-tree family

Date: October 26, 2026.
Reviewer: global_closure, independent of the source author.

**Decision: ACCEPT the complete whole-family assembly and both new
original coarse-cell closures.**

Source reviewed in full: `ROOTED_PURE_TRIANGLE_BLOCK_TREES_CLOSED.md`.
Source SHA-256:
`345e8d33f1219268141a3783e982b219db414063035cd8c32f7236ad1a4b01a5`.
The new geometric input was independently accepted in
`REVIEW_END_TRIANGLE_ORIGIN_INTERIOR_GLOBAL_2026_10_26.md` after a full
original-domain audit. I also reread the complete end-triangle pressure
assembly used at the final common root.

## 1. Genuine terminal blocks, without deleted forces

For a connected positive graph with no bridges and only triangle cyclic
blocks, the block-cut incidence graph is a finite tree. Articulation
nodes have degree at least two, so every leaf node is a block. A leaf
triangle has exactly one articulation and two true degree-two tips in
the original whole component. Any other positive edge at either tip
would change precisely this block-cut status; none is silently omitted.

The two tips must be loaded because an unloaded degree-two transmitter
separates its two physically touching neighbors. The new origin theorem
therefore applies at the actual arbitrary-degree root of every terminal
triangle. Distinct such roots would have overlapping open interiors
around O. Hence all terminal triangles have the same actual root H.

## 2. The graph argument exhausts every non-bouquet layout

Root the incidence tree at H. If a node were at distance at least two,
a node of maximal distance would have no child and would be a leaf.
It cannot be an articulation node. The resulting terminal block would
have a root different from H, a contradiction. Thus the whole incidence
tree is a star centered at H: every triangle is a genuine end petal at
that one root, and there is no unexamined chain, fork or other four-block
layout. This argument does not presume a drawing of the contact graph.

## 3. Full force contradiction for the remaining bouquet

H is physically circle-clear because it has two mutually touching
physical boundary tips in any one petal. Each actual complete petal
resultant M_j has strictly positive c_H projection by the accepted
end-triangle pressure theorem, which permits all the other forces at H.
The original force equation at H sums all 2r pair forces and gives
sum_j M_j=0. Its scalar product with c_H is an immediate contradiction.
No tip degree or circle mask is changed and no root force is deleted.

## 4. Original-cell accounting and scope

The exact size formula is 1+2r, so in nine physical squares the stated
range r>=2 consists exactly of r=2,3,4. The table correctly gives the
existing C2.33.b0 exit and the two new entire rows C3.333.b0 and
C4.3333.b0, with respectively four, two and zero arbitrary completion
squares. The four-block conclusion is a whole incidence-tree cover,
not just a linear-chain or common-root case.

All end triangles use the same preselected physical normal conditions.
Their inheritance under the stronger minimum-support selection elsewhere
is legitimate because it changes no physical pose or surviving normal.
The assembly itself needs no such stronger selection. Its explicit
restriction to the no-bridge family is correct; attaching a positive
edge at a terminal tip requires a new degree justification.

No correction or missing graph case was found. This review adds no fine
checklist ID, ledger mutation, numerical pose, Lean compilation, CI or
unrestricted final-radius conclusion.
