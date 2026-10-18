# Outer spectator contacts in a minimal B3 core form complete arcs, never dangling pieces

**Structural research, 2026-10-13.** This is a complete
actual-contact graph normal form under the **additional
hypothesis C has exactly its three positively stressed
actual contact neighbors X,Y,Z**. No square frames are
fixed and no cap constant is optimized.

## Theorem

Choose a least-radius packing of eight genuine unit
squares **with the fewest actual contacting pairs**
among all radius minimizers, at the eight-square
radius ceiling \(R<2\). Assume k=7 outer-center
exterior squares, no full seven-outer actual-contact
ring, and the positive stress component
\[
C-X-Y-C\quad\text{plus radial bridge }C-Z
\]
from [HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md]
(HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md).

Assume **C's only ACTUAL square-contact neighbors**
are exactly these three positive neighbors:
\[
\boxed{N_{\rm actual}(C)=\{X,Y,Z\}.}
\tag{A}
\]
The three actual stressed outer labels appear in
circular order \(X,Y,\ldots,Z,\ldots,X\), with X,Y
consecutive, and **at least one spectator square**
on each of the complementary Y-to-Z and Z-to-X arcs.

Let \(\mathcal A_{YZ}\) and \(\mathcal A_{ZX}\) be
the two paths of *outer-ray-neighbor* edges
from Y to Z and from Z to X, respectively.
Each path has at least two edges and at least
one internal spectator.

Then **exactly one** of the following **three**
actual outer-contact edge patterns is possible:

1. **I — isolated spectators:** neither complementary
   arc carries an actual contact edge. All four
   spectators are **completely isolated** in the
   full actual-contact graph.
2. **YZ — whole Y-to-Z arc:** every circular-neighbor
   edge along \(\mathcal A_{YZ}\) is an actual contact;
   **none** along \(\mathcal A_{ZX}\) is. Every spectator
   on the YZ arc has actual degree two, with both
   neighbors on that same arc; all other spectators
   are completely isolated.
3. **ZX — whole Z-to-X arc:** every edge along
   \(\mathcal A_{ZX}\) is an actual contact;
   **none** along \(\mathcal A_{YZ}\) is.
   Its internal spectators have actual degree two;
   all other spectators are isolated.

In symbols,
\[
\boxed{
E_{\rm outer,actual}=
\{XY\},\quad
\{XY\}\cup\mathcal A_{YZ},\quad
\{XY\}\cup\mathcal A_{ZX}.
}                                                   \tag{1}
\]

**No partly contacted spectator arc is possible.**
Both complete complementary arcs simultaneously are
also impossible, because with XY they close the
forbidden full outer seven-cycle.

Every auxiliary actual spectator contact in modes YZ/ZX
has **zero positive stress** for the chosen physical
stress; the sole positive outer edge is XY.

### Additional forced bracing of CS/SD leaf modes

If the radial positive leaf Z has genuine
**CS** (C-corner/Z-side) or **SD**
(C-side/Z-diagonal) interface, it is not allowed
to be an actual C-only leaf by
[HUMAN_B3_RADIAL_STRESS_LEAF_BRACING.md]
(HUMAN_B3_RADIAL_STRESS_LEAF_BRACING.md).
Therefore **mode I is impossible** for such a
nonparallel radial bridge, and it must use
one of the two **complete YZ or ZX spectator arcs**.

In particular CS/SD has at least **one fully
contacting spectator transmitter path** connecting
Z to X or Y, not just a single extra zero-weight
Z-to-spectator edge.

This is a strong whole-contact-graph restriction, not
a claim that the remaining contact graphs fit inside
the sharp disk or that the full B3 root has been closed.

## Proof

**Angular visibility.** The established outer-contact
visibility theorem says that every actual contact
between two outer-center squares joins two **consecutive**
outer center rays. The positive outer edge XY is
already present. All other possible actual outer edges
are precisely those on the two disjoint angular
paths \(\mathcal A_{YZ},\mathcal A_{ZX}\).
Both have at least one internal spectator because
Z is not adjacent to either X or Y.

**Noncentral actual leaves are impossible.**
The complete contact-minimal actual-leaf theorem
in HUMAN_STRESS_GRAPH.md states that a square with
one actual square-square contact must have the central
square C as its sole neighbor.
Under (A), none of the four spectators contacts C.

Consider a path arc, say \(\mathcal A_{YZ}\),
on which **some but not all** circular-neighbor
edges are actual contacts. Take an endpoint
of a maximal nonempty run of present edges
which is not Y or Z. Such an endpoint exists
because the run is not the full arc between Y,Z.
It is an internal **spectator label** and has
exactly one actual outer neighbor in the run,
no other outer contact by angular visibility,
and no central contact by (A).

It is therefore an **actual contact-graph leaf
whose only neighbor is noncentral**, contradicting
the proved contact-minimal actual-leaf theorem.
Hence **every arc is either empty or completely present**.

If both complementary arcs were complete, together
with XY they would form the complete outer actual
seven-contact cycle, excluded by the root hypothesis.
Thus at most one complementary arc is complete.
That leaves exactly the three edge patterns (1).
The spectator degree and isolation statements follow
from the explicit path structure and the absence
of central spectator contacts.

Every contact on either auxiliary arc outside XY has
zero positive-stress weight, by the assumed *unique*
positive core C-X-Y triangle plus C-Z bridge.
The independently proved CS/SD bracing theorem
requires at least one *actual* outer contact of Z
with a spectator. This is impossible in mode I,
so CS/SD requires YZ or ZX as claimed. QED.

## Exact finite case enumeration

The earlier positive graph theorem gives exactly
seven circular positions for the unique positive
outer edge XY and three nonadjacent outer-ray
positions for Z, **21 labeled positive stress
supports**. Under (A), every such positive support
has **three** graph-theoretically admissible complete
outer actual-contact patterns from (1).
Therefore there are exactly
\[
\boxed{21\cdot3=63}
\]
**labeled actual-graph templates**, before any
continuous true-square feasibility constraints.
The pure SS actual leaf mode can use I/YZ/ZX,
while genuine CS/SD requires YZ or ZX.

[verify_B3_complete_spectator_arcs.py]
(verify_B3_complete_spectator_arcs.py)
enumerates every optional edge subset of the outer
seven-cycle at each positive XY and Z placement
and verifies that every rejected partial arc
creates a forbidden noncentral spectator leaf.
It is a graph-only cross-check; the hand proof
supplies the actual physical leaf rigidity.

## Scope and open tasks

This theorem **needs** the minimal actual C-neighbor
assumption (A). If C has one or more additional
actual but zero-stress contacts to spectators, those
spectator labels may avoid the noncentral-leaf
contradiction. The present three-way arc form
cannot be copied to that different case.

Also, **the 63 counts are combinatorial
templates, not 63 feasible eight-square packings**.
No removal of the real sharp full-outer-contact-ring
equality root is asserted.

The next structural attack on the still-open B3
core should focus on the full YZ/ZX auxiliary
actual paths and their true transmitter/zero-
positive-weight contact geometry. A successful
whole-case radius obstruction must retain all
four full exterior spectator squares and the
central pocket. The unrestricted \(R_8\ge\widehat R\)
remains OPEN.
