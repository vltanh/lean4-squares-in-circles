# Every pure triangle block tree with at least two blocks is excluded

Date: October 26, 2026.

**Status: complete whole-family assembly, accepted after the full-source reviews
REVIEW_PURE_TRIANGLE_BLOCK_TREES_ROOT_2026_10_26.md and
REVIEW_PURE_TRIANGLE_BLOCK_TREES_GLOBAL_2026_10_26.md.**
Its origin-interior prerequisite has separate complete reviews. The assembly
closes whole coarse cells C3.333.b0 and C4.3333.b0; no original fine-checklist
label is added or changed.

Work with the original nine physical unit squares and the same common
compatible selected physical certificate in

\[
                    79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

**Theorem.** A connected positive component cannot have no bridges and
have all its cyclic blocks be triangles, with at least two such blocks.
Every physical circle mask, individual zero circle weight, original
contact normal and shared application mean remains. All physical squares
outside that positive component remain arbitrary and present.

For nine squares the theorem covers precisely the pure no-bridge
triangle-block rows with two, three or four blocks. In particular it
closes the entire original three-triangle and four-triangle coarse cells,
not only their common-root bouquets or a middle-cycle moment slice.

## 1. Every terminal block supplies an intact loaded end triangle

Use the actual block-cut incidence tree of the connected positive body
graph. Its nodes are the cyclic blocks and their articulation vertices;
adjacency records membership. There are no bridge blocks by hypothesis.
Every articulation node has degree at least two, while a triangle block
contains at most three articulation vertices. With at least two blocks,
this finite incidence tree has at least two leaves, all of them block
nodes.

Let a leaf block be H--U--V--H. It has precisely one articulation H.
Its other two actual bodies U,V have exact positive degree two in the
whole original component, with neighborhoods {H,V} and {H,U}.
There is no unrecorded positive force outside the block at either tip:
such an edge would make that vertex an articulation or enlarge its
biconnected block.

Both tips are loaded. If, for example, U were unloaded, its two positive
pair forces would be opposite. H and V would then lie beyond opposite
support lines of U, whose gap is the positive width of a unit square.
They could not physically touch, contrary to the actual HV triangle
edge. The same argument applies to V. Their physical boundary contacts
are actual and all their circle-weight endpoints remain.

Thus this is exactly an intact loaded end triangle at arbitrary-degree
root H. ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md gives

\[
                            O\in\operatorname{int}H.
\tag{2}
\]

Consequently every terminal triangle must have the same actual root H:
two different root squares would both contain O in their open interiors,
contradicting the original pairwise interior disjointness.

This step uses the full intact-tip equations, without deleting the
middle blocks or their original forces. It applies to all orientations
and all directed cycle moments, including zero moments.

## 2. A finite block tree with one terminal root is a bouquet

We give the short combinatorial argument so that no other no-bridge
layout is omitted. Regard the articulation node H from Section 1 as a
root of the block-cut tree. Every leaf block is adjacent to H.

If some node had distance at least two from H, choose one of maximal
distance. In a finite tree a maximal-distance node has no neighbor
farther from H, and therefore is a leaf. It cannot be an articulation
node, since every such node has degree at least two. It is a leaf block
whose unique adjacent articulation is not H, contradicting Section 1.

Hence all block nodes are directly adjacent to H and there are no other
articulation nodes. The actual original positive component is a bouquet
of r>=2 intact end triangles sharing H and otherwise having disjoint
vertices. It has exactly 1+2r actual bodies.

Equivalently, every non-bouquet pure triangle block tree has two genuine
terminal triangles with different roots and is already impossible by
(2). No drawing or particular ordering of its blocks is assumed.

## 3. The full bouquet contradicts its original force equation

Write the r original end triangles as H--U_j--V_j--H. Every U_j,V_j
is a true degree-two loaded tip by Section 1. H is physically
circle-clear: if it touched the circle, H,U_j,V_j would be a physical
boundary triangle, forbidden by CIRCLE_CONTACT_ANGULAR_ORDER.md.
Its actual circle force is therefore zero.

For each actual block put

\[
                         M_j=F_{U_j}+F_{V_j}.
\tag{3}
\]

The true tip force equations identify M_j with the sum of that block's
two outward H-to-tip pair forces. The complete end-triangle pressure
theorem, BOWTIE_CELL_CLOSED.md, Section 2, permits arbitrary further
positive forces at H and gives

\[
                            c_H\cdot M_j>0
                            \quad\text{for every }j.
\tag{4}
\]

At H, retain all 2r original positive pair forces. Its full original
force equation is exactly

\[
                                \sum_{j=1}^r M_j=0.
\tag{5}
\]

Taking the scalar product with c_H contradicts the strictly positive
sum in (4). This excludes the entire bouquet domain and finishes the
theorem. No stress is split or altered in this last step.

## 4. Complete original coarse-cell mapping

A pure triangle block tree with r blocks and no bridges has 1+2r
bodies, since every additional triangle shares precisely one articulation
with the preceding connected block union. With nine actual bodies and
r>=2, the only possible values are r=2,3,4.

| Triangle blocks | Actual positive bodies | Arbitrary remaining squares | Entire original coarse cell | Status supplied by the theorem |
| ---: | ---: | ---: | --- | --- |
| 2 | 5 | 4 | C2.33.b0 | Whole bowtie, already closed by its original pressure assembly |
| 3 | 7 | 2 | C3.333.b0 | Every bouquet and every distinct-root chain |
| 4 | 9 | 0 | C4.3333.b0 | Every original four-block incidence tree |

For three blocks, the incidence tree is either the common-root bouquet
or a middle triangle with end triangles at two different vertices. The
first is Section 3; the second is excluded directly by the two actual
open-origin roots. For four blocks, Section 2 supplies the entire graph
cover without assuming that the non-bouquet graph is a linear chain.

All these conclusions use the same initial compatible selection as
the completed end-triangle pressure and common-side inputs. Their finite
conditions were imposed for all actual physical candidates before
multiplier extraction. Applying them at several true terminal blocks
does not reselect any normal or fix any shared mean after extraction.
Any stronger support-minimization used elsewhere in the overall proof
preserves this existing scope; none is needed for the present assembly.

This source establishes exactly the stated no-bridge pure-triangle
family. If a terminal triangle tip has another positive edge, the
intact-tip hypothesis must be re-established before using Section 1.
Graphs with bridges, larger cyclic blocks or nonterminal triangles as
the only visible triangles are not removed merely by this table.

There is no numerical pose, scalar certificate, extra angular cover,
Lean compilation or CI in this assembly. The unrestricted n=9 lower
bound, its equality cases and the other coarse cells remain separate
obligations.
