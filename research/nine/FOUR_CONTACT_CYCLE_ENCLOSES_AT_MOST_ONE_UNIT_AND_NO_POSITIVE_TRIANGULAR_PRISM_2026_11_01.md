# A four-contact cycle encloses at most one other unit; the selected positive graph has no triangular prism

Date: November 1, 2026. Author: module_universal, with root's independent
contact-quadrilateral area and equality-reserve check. The arbitrarily
small physical embedding and three-cycle theorem are credited existing
inputs, not new constructions here.

**Status: complete new hand geometry, frozen for independent review.**
No radius bound, boundary load pattern, degree restriction, numerical
pose, mathematical program, graph enumeration, Lean, build or CI is
used. All original positive forces and physical units remain.

## 1. Exact physical scope and conclusions

Keep a finite packing of actual closed unit squares with disjoint open
interiors and the same compatible selected planar physical positive
body graph. Each original positive pair retains its actual common
application or full shared-side mean. Use the arbitrarily small
center/contact embedding supplied by
`PHYSICAL_BODY_GRAPH_UNCROSSING.md` and restated with its full local
homotopy construction in `NO_POSITIVE_K4_SUBGRAPH.md`, Section 1.

**Theorem 1.** The embedding can be chosen sufficiently close to the
same original physical strands so that no positive four-cycle encloses
the centers of two other actual unit squares on its bounded side.
All positive three-cycles simultaneously enclose no other body center,
as in the existing theorem.

**Theorem 2.** The selected positive body graph has no literal
triangular-prism subgraph. Every additional positive edge, full body
degree, circle load, physical contact and completion square is allowed.

The conclusion concerns the selected physical graph at its existing
compatible plane-embedding scope. It does not assert that the entire
physical touching graph is planar, or replace an arbitrary crossing
selection by a new force certificate.

The full source `NO_POSITIVE_K4_SUBGRAPH.md` was read from the current
branch, Git blob `0a3e81e1e941af7cbeb5d5176a8108ed9a3f5ff1`. Its Sections
1--2 are the exact operative embedding and empty-triangle inputs.

## 2. Strict available area of every contact-quadrilateral walk

Take four distinct actual unit squares S_1,S_2,S_3,S_4 in positive
cyclic order, and their unchanged applications

\[
p_1\in S_1\cap S_2,\quad p_2\in S_2\cap S_3,\quad
p_3\in S_3\cap S_4,\quad p_4\in S_4\cap S_1.
\]

The closed contact walk is `p_1 p_2 p_3 p_4 p_1`. Its points need
not be distinct and its straight segments need not form a Jordan
curve. Each consecutive segment belongs to one actual S_i, so each
has length at most sqrt(2).

Let D_1 be the closed convex triangle with vertices p_1,p_2,p_3,
and D_2 the closed convex triangle with vertices p_1,p_3,p_4. Degenerate
triangles have area zero. Put V=D_1 union D_2. The ordinary triangle
area formula gives

\[
\begin{aligned}
\operatorname{area}(D_1)
&\le\tfrac12|p_1-p_2|\,|p_3-p_2|\le1,\\
\operatorname{area}(D_2)
&\le\tfrac12|p_1-p_4|\,|p_3-p_4|\le1.
\end{aligned}                                                   \tag{1}
\]

Consequently `area(V)<=2`. More precisely, the area available after
excluding the four actual cycle-square interiors satisfies

\[
\operatorname{area}\left(V\setminus
          \bigcup_{i=1}^4\operatorname{int} S_i\right)<2.
                                                                  \tag{2}
\]

If `area(V)<2`, (2) is immediate. Otherwise every comparison in (1)
is equality and the two triangles have disjoint interiors. Both have
legs of length sqrt(2) meeting at right angles, at p_2 and p_4
respectively; their common hypotenuse p_1p_3 has length two. The
two possible right-isosceles vertices for this fixed hypotenuse lie
on its opposite sides. Disjoint interiors force the two different
choices. Thus V is exactly a square of side sqrt(2), with the four
contact segments as its sides.

Each contact segment now has length sqrt(2), so it joins opposite
vertices of its own actual unit S_i. Its midpoint is that unit's
center. A sufficiently small open disk about this midpoint lies in
`int S_i`, while its intersection with `int V` is a nonempty open
half-disk. Hence a positive area of V is occupied by that actual
cycle square. Removing it gives (2).

This strict reserve is established separately for each fixed original
four-cycle; no artificial uniform numerical reserve is assumed.

## 3. Nonzero winding is confined to those two triangles

The oriented contact-quadrilateral walk is the sum of the two oriented
triangle walks

\[
(p_1p_2p_3p_1)+(p_1p_3p_4p_1),
\]

because their two diagonal segments cancel with opposite orientations.
For a point off all displayed segments, its winding number is therefore
the sum of the two triangle winding numbers. A point outside V has
zero winding for both. Thus every point with nonzero contact-walk
winding lies in V, up to boundary segments of area zero.

This argument includes crossed quadrilaterals, coincident applications,
collinear segments and any shared-mean endpoint. No Jordan property of
the straight contact walk is assumed.

## 4. Full small-neighborhood embedding and two actual inner cores

The accepted embedding theorem supplies, for every epsilon>0, a plane
embedding fixing the actual body centers. Each positive edge is drawn
in an epsilon-neighborhood of its two incident actual squares and is
homotopic there, relative to its endpoints, to its original strand
`c_i p_ij c_j`. The local junction and tube radii may all be reduced
arbitrarily; no physical point or force changes.

Fix one original four-cycle. By (2) let a<2 denote its available area.
Choose a positive delta<1/2 such that

\[
2(1-2\delta)^2>a.                                      \tag{3}
\]

Suppose an embedding with epsilon<delta encloses two other actual
centers, belonging to distinct unit squares T_1,T_2, inside this cycle.
Shrink each T_j inward by delta on its four own sides, producing a
concentric closed square T_j^- of side `1-2delta`. The original cycle
squares are disjoint from `int T_j`. Every point of T_j^- is at
distance at least delta from their union. Thus the embedded cycle and
its entire accepted edge homotopies avoid both inner squares.

Each T_j^- is connected and contains its enclosed body center, so it
lies wholly on the bounded side of the embedded Jordan cycle. Its
winding number there is nonzero. After the edge homotopies, within
each convex S_i replace the two half-strands through c_i by the
segment between the adjacent actual contact points. This second
homotopy also avoids both inner squares. The winding number of the
resulting contact-quadrilateral walk is therefore nonzero about every
point of both T_j^-.

By Section 3 the two inner squares lie in V, apart from immaterial
boundary segments. They avoid every `int S_i` and have disjoint open
interiors. Their combined area is consequently at most a. But their
combined area is exactly `2(1-2delta)^2`, contradicting (3).

There are only finitely many positive four-cycles in the fixed original
graph. Choose delta for each and take epsilon smaller than all of them
and the existing three-cycle threshold `1/80`. The resulting single
physical embedding simultaneously has the asserted four-cycle and
three-cycle properties. No limit of varying force certificates or
varying actual packings is used. Only the auxiliary drawing is made
sufficiently close to the fixed physical strands.

This proves Theorem 1, including every original multiple junction and
every cycle whose unperturbed contact walk is not Jordan.

## 5. The triangular prism cannot occur as a literal positive subgraph

Suppose six actual body vertices form a literal triangular prism:
two disjoint positive triangles

\[
A_1A_2A_3A_1,\qquad B_1B_2B_3B_1
\]

and their three positive matching edges A_i--B_i. Restrict the one
embedding from Section 4 to these six vertices and nine original edges.
Every edge remains its original physical edge. Extra graph edges and
all other bodies are kept in the packing, but are unnecessary in this
topological restriction.

The prism is biconnected: after any one vertex is removed, the other
triangle remains connected and the two remaining matching edges join
both remaining vertices of the affected triangle to it. Thus the
boundary of each face of this plane subgraph is a cycle.

Its only three-cycles are the two displayed triangles. By the accepted
three-cycle theorem neither can have any other body center on its
bounded side. Each therefore bounds an empty bounded face of the
prism embedding. Indeed any other edge entering that bounded side
would have to end at an enclosed vertex or cross the triangle again;
the former is absent and the latter is forbidden in a plane embedding.

Euler's formula gives five faces, because `6-9+F=2`. Two are the
bounded triangular faces just identified. Each of the other three
faces has boundary length at least four, and the sum of all five
boundary lengths is twice the edge count, namely eighteen. Hence

\[
18=3+3+4+4+4,
\]

and all three remaining face boundaries, including the unbounded one,
are four-cycles.

The unbounded-face four-cycle contains four of the six prism vertices.
The other two centers lie strictly on its bounded side. This violates
Theorem 1. Therefore the selected physical graph contains no literal
triangular-prism subgraph, proving Theorem 2.

The proof is independent of which prism vertices carry loads or have
extra positive neighbors. It therefore excludes the entire six-hub
unloaded cubic-prism three-port feature as a particular caller, while
requiring no new equation at any prism vertex.

## 6. Exact scope of the new closure

The new theorem removes every literal positive triangular prism at
the same compatible selected physical-embedding scope, across arbitrary
radius and outside-degree choices. It also supplies the general rule
that four-contact cycles cannot enclose two other actual unit centers
in a sufficiently small physical embedding.

It does not assert that every graph is outerplanar, that a four-cycle
cannot enclose one unit, or that every higher-degree three-port module
contains a prism. Any final use of the latter form still requires its
complete hand graph reduction. The distinct five-hub/one-transmitter
six-body candidate and the whole original `C1.8.b1` parent remain open
unless separately excluded. No original flag is changed here.
