# The selected physical positive graph has no K4 subgraph

**Status: complete hand geometric implication; two independent hand audits
passed.** A selected planar physical body graph for interior-disjoint
unit squares has no \(K_4\) subgraph. More precisely, its physical
plane embedding can be made so close to the actual center/contact
strands that no three-cycle encloses another body center.

There is no containing-radius restriction in this implication. The
selection of a planar physical force-and-torque certificate is supplied
by `PHYSICAL_BODY_GRAPH_UNCROSSING.md`. The conclusion concerns that
selected positive graph, not the entire physical touching graph: four
aligned unit squares around one point do have all six physical pair
contacts, while the selected uncrossing removes at least one of their
two opposite-pair edges.

In particular this excludes the entire \(K_4\)-block branch of
C1.4.b1, with any leaf attachment and all remaining physical squares.
It also excludes \(K_4\) subgraphs inside every larger selected cell.
Other block types are not excluded here.

## 1. An arbitrarily small physical embedding

Fix the selected positive stress after junction uncrossing and
aggregation. Its body centers and genuine contact application points
are fixed. For a positive pair \(i,j\), let \(p_{ij}\) be its
actual common application point. The original two-segment strand is

\[
                         c_i p_{ij} c_j.                 \tag{1}
\]

Each half-strand lies in its own closed square, with its open part in
that square's open interior. The planar embedding construction in
`PHYSICAL_BODY_GRAPH_UNCROSSING.md` has the following explicit
small-neighborhood form:

> For every \(\varepsilon>0\), the positive graph has a plane
> embedding fixing all body centers, with each edge (1) replaced by a
> simple arc homotopic to that strand, relative to its endpoints,
> inside the \(\varepsilon\)-neighborhood of
> \(S_i\cup S_j\).

Here the homotopy is for an individual edge; different edge homotopies
need not be performed without crossing one another. Only the final
embedding is required to be planar.

To obtain this version, choose all finitely many junction disks with
radii less than \(\varepsilon/4\), and choose the center/strand
tubes thinner than \(\varepsilon/4\). At a junction the surviving
local graph has at most one opposite-pair diagonal, so its outerplanar
routing can be drawn in an arbitrarily small disk, preserving the
physical sector order. Parallel strands are separated in arbitrarily
thin tubes inside the incident square interiors. The body-center
stars can likewise be separated in arbitrarily small interior disks.
Shrinking these neighborhoods does not alter any of the required
local cyclic orders.

An edge's detours in a contact disk can be contracted to the original
contact point within that disk, and its tube detours contracted to the
original half-strands. Every point of a contact disk for that edge is
within \(\varepsilon/4\) of its own common point
\(p_{ij}\in S_i\cap S_j\). Thus these contractions give the
claimed homotopy inside the displayed neighborhood, even at a
multiple-body junction. No assumption that a perturbation disk is
empty of the other physical squares is needed.

## 2. No embedded three-cycle can enclose another body center

Choose an embedding from Section 1 with

\[
                              \varepsilon<\frac1{80}.
                                                               \tag{2}
\]

Let three distinct body vertices \(A,B,C\) form a three-cycle
in this plane graph, and let \(\Gamma\) be its embedded Jordan
curve. Suppose the center of another unit square \(D\) were
on its bounded side.

Inside \(D\), take the concentric square \(D^-\) obtained by
moving each side inward by \(1/40\). It has side length
\(19/20\) and area

\[
                 \operatorname{area}(D^-)=\frac{361}{400}
                      >\frac9{10}>\frac{\sqrt3}{2}.      \tag{3}
\]

Every point of \(D^-\) has distance at least \(1/40\)
from the complement of the open square \(D\). The closed
squares \(A,B,C\) are disjoint from the open interior of
\(D\): otherwise a small open neighborhood would meet both
open square interiors. Thus

\[
                  \operatorname{dist}(D^-,A\cup B\cup C)
                       \ge\frac1{40}.                   \tag{4}
\]

The curve \(\Gamma\) and its homotopy to the actual
center/contact loop lie within the \(\varepsilon\)-neighborhood
of \(A\cup B\cup C\), so avoid \(D^-\) by (2)--(4).
The connected square \(D^-\) contains the center of \(D\).
It is therefore wholly on the bounded side of \(\Gamma\),
and the winding number of \(\Gamma\) is nonzero about each
of its points.

Let the three actual contact points be

\[
 p_{AB}\in A\cap B,\quad p_{BC}\in B\cap C,
 \quad p_{CA}\in C\cap A.
\]

First apply the edge homotopies from Section 1. Then, within each
of the three convex squares, move its center vertex to the midpoint
of its two adjacent contact points. This gives a homotopy from
\(\Gamma\) to the closed contact-triangle walk

\[
                          p_{AB}p_{BC}p_{CA}p_{AB}.       \tag{5}
\]

The entire homotopy avoids \(D^-\). Thus (5) has nonzero
winding about every point of \(D^-\). If its three points
are collinear or coincide, its winding is zero off its segments,
already a contradiction. Otherwise all of \(D^-\) lies in
their closed convex triangle \(\Delta\).

Each side of \(\Delta\) joins two points of one unit square,
so its length is at most \(\sqrt2\). The elementary contact
triangle estimate in `CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`
gives

\[
                           \operatorname{area}(\Delta)
                                \le\frac{\sqrt3}{2}.
\]

This contradicts (3). Therefore no embedded three-cycle encloses
another body center.

This proof does not require the unperturbed center/contact loop to be
Jordan. Coincident triangle contact points, shared-side endpoint
contacts, and all artificial small junction-routing faces are included.
The inner square \(D^-\) supplies a uniform positive clearance,
so no limit or unsupported drawing convention is needed.

## 3. Apply the plane K4 topology

Suppose the selected positive graph contained a \(K_4\) subgraph.
Restrict the embedding from Section 1 to these four vertices and their
six edges. A plane embedding of \(K_4\) has four triangular
faces. For example, Euler's identity gives four faces, while every
face boundary has at least three edges and the sum of their lengths
is twelve; all four lengths are therefore three.

The boundary of its unbounded face is a three-cycle. The fourth
vertex lies strictly on its bounded side. This contradicts Section 2.

**Theorem 3.1.** The selected planar physical positive body graph
contains no \(K_4\) subgraph. In the sufficiently small physical
embedding above, every three-cycle has no other body center on its
bounded side.

The theorem does not assert that all positive graphs are outerplanar,
nor that longer contact cycles have empty interiors. In particular it
does not settle the remaining C4 or diamond block branches of
C1.4.b1, or the general seven-cycle completion.
