# The entire five-body biconnected cell C1.5.b0 is closed

**Status: complete hand whole-cell assembly; root and separate independent
full assembly audits passed. All three graph-family assemblies have also
passed root and independent full reviews.** Work with a hypothetical nine-unit radius minimizer and
its compatible selected physical planar certificate in
\[
                   \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
The lower endpoint is the inherited prerequisite
LOWER_WINDOW_FROM_EIGHT.md. The global selected-component theorem and
TREE_AND_TWO_LOAD_COMPLETION.md supply the unique positive component
and exclude fewer than three positive circle-loaded bodies in this
radius proof. None of those prerequisites is re-proved here.

**Theorem.** The selected positive component cannot be biconnected on
exactly five bodies. Thus the entire coarse cell C1.5.b0 is excluded,
for every positive graph, positive-load set, physical circle mask,
actual contact owner and shared-side mean. All four arbitrary extra
squares remain in the original packing.

## 1. Exact component and certificate scope

Let G be the simple positive body graph of this entire five-body
component. It is biconnected and has no additional positive edge to
any of the other four bodies. Its edges carry actual physical contact
forces, aggregated with their genuine application means. An omitted
positive edge may still be a zero-stress physical contact.

Let L be the positive circle-loaded set. The physical noncontact graph
on L is connected, by ACUTE_LOADED_CONTACT_GRAPH.md. Consequently
\[
           |L|\ge3,\qquad \overline G[L]\text{ is connected}.
\tag{2}
\]
The second implication holds because every positive edge is a physical
contact, so the physical noncontact graph is a subgraph of the induced
positive-graph complement. It never identifies a missing positive edge
with a physical noncontact. Physical circle contacts with zero total or
individual multiplier remain independent physical labels.

The same certificate retains the existing strict point-normal,
compatible diagonal, matched-junction and finite generic choices.
All choices precede multiplier extraction. The three remaining
graph-family proofs below use one compatible certificate, not separate
normal choices imposed after seeing its positive graph.

## 2. The exhaustive ten-type graph cover and its exits

FIVE_BODY_BICONNECTED_REDUCTION.md, Sections1--3, gives a hand
classification of every possible G. Biconnectivity implies minimum
degree at least2, hence at least5 edges, and its complement has maximum
degree at most2. The complement is therefore a disjoint union of paths
and cycles. Classifying its possible edge counts gives precisely the
following ten biconnected graph types:

| Positive edges | Entire positive graph type | Complete exit |
| --- | --- | --- |
| 5 | C5 | FIVE_CYCLE_POSITIVE_COMPONENT_EXCLUSION.md |
| 6 | House | HOUSE_POSITIVE_COMPONENT_EXCLUSION.md |
| 6 | K2,3 | Three loaded common neighbors, as in Section3.2 of the graph reduction |
| 7 | Three-page book: a hub edge and three common degree-two neighbors | The same three-loaded-common-neighbor obstruction |
| 7 | Fan over a four-vertex path | FOUR_LOAD_FAN_EXCLUSION.md |
| 7 | K4 with one edge subdivided once | Three loaded common neighbors, as in Section3.3 of the graph reduction |
| 8 | Four-rim wheel with its hub | Loaded-complement connectivity (2) |
| 8 | K5 with two adjacent edges removed | Contains a positive K4 |
| 9 | K5 with one edge removed | Contains a positive K4 |
| 10 | K5 | Contains a positive K4 |

Here is the complete combinatorial accounting behind the table. At
five edges every degree is2, giving C5. At six edges the complement
has four edges and maximum degree2. Its possibilities are P5,
C4 disjoint from one isolated vertex, and K3 disjoint from K2.
The middle complement gives two triangles with one common articulation
in G, so it is not biconnected. The other two give the house and K2,3.

At seven edges the complement is respectively K3 with two isolates,
P4 with one isolate, or P3 disjoint from K2, giving the three displayed
types. At eight edges its two edges are either disjoint or adjacent,
giving the wheel and the listed K4-containing graph. At nine or ten
edges a K4 is immediate. Thus the count is
\[
                             1+2+3+2+1+1=10.
\]
No graph or pose search is a premise.

The uniform exits for the seven remaining graph types keep the entire
physical domain. For the wheel, every component of its complement has
at most two vertices, contradicting (2). For K2,3 and the book, (2)
forces exactly the three common neighbors to be loaded. For the
subdivided K4, (2) likewise forces a three-vertex complement-path set
whose members have two common positive neighbors. In all three cases
NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md gives a contradiction. The
remaining three rows contain a positive K4 and are excluded by
NO_POSITIVE_K4_SUBGRAPH.md. These are subgraph theorems with their
stated full force scope, not degree-two cycle arguments applied after
deleting an edge.

Only C5, the house and the four-path fan therefore require the complete
metric and owner-family proofs. Each is now excluded in full.

## 3. The three complete surviving graph-family exits

### 3.1. C5

FIVE_CYCLE_POSITIVE_COMPONENT_EXCLUSION.md combines the exact load
cover and both entire metric orbit proofs. The three-load orbit keeps
the isolated load's full parallel/nonparallel alternatives and both
transmitter widths; its proper concurrence triangle contradicts the
full center-angle sum. The four-load orbit keeps every endpoint frame
and mean and contradicts the actual side- or diagonal-channel endpoint
separation. An all-loaded C5 is excluded by the physical boundary-cycle
theorem. These are arguments for the entire degree-two positive cycle,
with no deleted chord and no completion motion.

### 3.2. House

HOUSE_POSITIVE_COMPONENT_EXCLUSION.md derives exactly three necessary
load orbits from the complement path: the two reflected end triples,
the middle triple, and the two reflected four-load sets. The respective
complete assemblies are HOUSE_END_TRIPLE_BRANCH_CLOSED.md,
HOUSE_MIDDLE_TRIPLE_BRANCH_CLOSED.md and
HOUSE_FOUR_LOAD_BRANCH_CLOSED.md.

The end-triple proof covers both bypass frames, both physical lower-tip
circle masks, every lower-tip frame and every actual endpoint owner.
The middle-triple proof covers shared, one-owner and free hub contacts,
with complete parallel and nonparallel unloaded-star exits. The
four-load proof keeps only the house's three real hub spokes and
excludes both its full wall and free/shared endpoint alternatives.
Every variable mean and every physical zero-weight corner limit is
included. None of these proofs turns a degree-three body into a
degree-two body by deleting a force.

### 3.3. Four-path fan

FOUR_LOAD_FAN_EXCLUSION.md first removes both three-load masks using
the exact unloaded-diamond-hub theorem. It then covers the entire
four-loaded-path family with its genuine degree-four hub. The two
endpoint normals cannot both be hub-owned or both non-hub-owned.
The three remaining mixed families are excluded in full: tip-owned,
unique-free opposite a shared boundary side, and physical radial-free.
The full hub equations and both degree-three internal path bodies are
retained. The fan's extra spoke is not silently removed to use a house
argument.

## 4. Whole-cell conclusion and its limits

The original ten-type classification is exhaustive, the uniform
subgraph/load obstructions remove seven types, and the three full
graph-family assemblies remove the rest. Therefore no selected
positive component in (1) belongs to C1.5.b0.

All finite normal exclusions used by the graph-family prerequisites
are imposed simultaneously before extraction, with their physical
candidate tuples and fixed/shared applications prelisted. Their
source proofs establish the nonzero factors and compatibility with
matched junctions. Physical uncrossing preserves surviving point
normals and adds only shared-side atoms, whose actual means remain;
thinning only removes atoms. No normal, force application, circle
weight, body orientation or extra-square position is changed after
the certificate is obtained.

These are direct selected-core contradictions with all four extras
fixed. No new secondary-minimizer or exterior-pocket premise is used
by this cell assembly. Inherited global prerequisites retain their
original scope and are not replaced by this statement.

The exact five-body component hypothesis is essential. A larger
positive component may contain a C5, house or fan subgraph with
additional positive forces at its vertices; the degree-specific
equilibria above do not automatically apply to that subgraph.
Such larger components require their own complete proofs or explicit
local-motif transfer theorems. This closes C1.5.b0 only, not any
six-body coarse row, the remaining global lower bound or its equality
classification. No numerical parameter cover, Lean compilation or
CI run is a premise or a reported verification.
