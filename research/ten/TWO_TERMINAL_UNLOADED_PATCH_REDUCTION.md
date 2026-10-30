# Every unloaded two-terminal region has parallel forces

**Status:** reviewed hand theorem, 2026-10-30; root and two independent
mathematical reviews passed for the arbitrary-terminal scope. This is a universal local reduction. It does not assume that
every unloaded region has only two terminals, and introduces no new
catalog or exclusion count.

Work in `79/40<=R<=3/sqrt(2)` with the jointly selected planar physical
stress. Use its contact-atom planar embedding with cyclic force-normal
order, as established in
[TWO_LOADED_PARALLEL_FORCE_REDUCTION.md](TWO_LOADED_PARALLEL_FORCE_REDUCTION.md).
Let G be one connected positive body-pair component, and let A,B be
any two distinct vertices. No prior exposure assumption is imposed on
either terminal. The selection theorem supplies exterior access paths
for every loaded vertex; that property is used below.

Let U be one nonempty connected component of `G-{A,B}` and suppose
every body of U is unloaded. Define H to contain U,A,B and all edges
having at least one endpoint in U. In particular, a direct A--B edge
of G is omitted from H.

**Theorem.** Every contact force in H is parallel to one common line.
The endpoint squares A,B are separated by a support strip of width

```text
W in {1,sqrt(2),2},
```

and their distance is exactly W. The bodies of U have one of these forms:

* W=1: one side transmitter;
* W=sqrt(2): one diagonal transmitter;
* W=2: between two and four parallel side bodies, in two consecutive
  unit-width columns, with one or two bodies in each column.

The positive graph induced on U remains connected. In the last case
this is a connected graph between the two columns. The theorem imposes
no radial condition on A or B and does not call either terminal loaded.

## 1. A unique face contains both terminals

The unloaded-set lemma in
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md), Section 1,
excludes a nonempty unloaded set with only one outside body-neighbor.
Since G is connected and U is a component after deleting A,B, U must
attach to both A and B. Thus H, H-A, H-B, and `H-{A,B}=U` are connected.
There is no A--B edge in H by definition.

Both terminals are incident to H's outer face, even though they need
not have been exterior vertices of G. Suppose, for contradiction, that
B is not incident to H's outer face. Then B is unloaded: a loaded
vertex has an exterior access path in the selected embedding of G,
which also gives exterior access after restricting to H.

Every other component V of `G-{A,B}` lies in one face of H. If this
face is bounded, V is entirely unloaded. A positive circle load inside
a bounded H face would have an exterior access path crossing H, which
is impossible.

Let W consist of U, B, and all these other components V lying in
bounded faces of H. This is a nonempty unloaded set. Any component V
not included in W lies in H's outer face and cannot be adjacent to B:
the drawing of an edge from V to B would make B incident to that
face. The only outside neighbors of U are A,B, and the only outside
neighbors of any V are A,B. Consequently W has only A as an outside
body-neighbor. It has at least that neighbor because U attaches to A.
This contradicts the unloaded-set lemma. Therefore B is incident to
the outer face of H, and the same argument applies to A.

We now claim that no second face of H is incident to both A and B.

Suppose two distinct faces were incident to both terminals. In each
face draw a simple A-to-B arc whose nonendpoint points stay in that
face. The two arcs have disjoint interiors and together form a Jordan
curve J. Each side of J contains a point of H other than A,B. Indeed,
if one side contained no point of H, that side, together with small
neighborhoods of the two arcs away from A,B, would connect their two
face interiors in the complement of H. They would then be the same
face, a contradiction.

Since H has no A--B edge, a point of H on either side of J belongs to
an edge with at least one endpoint in U, or is itself a vertex of U.
That endpoint lies on the same side: the edge cannot cross J except
at A or B. Hence U has vertices on both sides of J. A path in the
connected graph U cannot cross J, because J meets H only at A,B and
U contains neither. This is a contradiction. The outer face is
therefore the unique face incident to both terminals.

## 2. Every omitted incidence occupies the same outer-face corner

Consider another component V of `G-{A,B}`. Its drawing lies in one
face of H, and its only possible neighbors outside V are A,B. If V
attaches to both, that face is incident to both terminals and is
therefore the outer face, by Section 1.

If V attaches to only one terminal, V cannot be entirely unloaded,
by the same unloaded-set lemma. It contains a loaded vertex. Every
loaded vertex has an exterior access path in the selected planar
embedding, so V cannot lie in a bounded face of H. It again lies in
the outer face. A direct A--B edge, if present in G, also lies in the
unique face incident to both terminals, hence in the outer face.

Because H-A and H-B are connected, neither terminal is a cut vertex
of H. A non-cut vertex in a connected plane graph has at most one
corner belonging to any given face. This includes the degree-one case,
where there is just one corner altogether. One may verify the usual
fact by drawing two short arcs through two purported corners of the
same face: they separate nonempty groups of incident edges, disconnecting
the graph after deleting that vertex.

Consequently all omitted contact incidences at A form one contiguous
block in its cyclic order, and the same holds at B. If a terminal is
loaded, its positive circle incidences lie in this same outer-face
corner, by their exposure paths. Include these circle incidences in
the omitted block. All force incidences of U remain in H, since its
bodies are unloaded and have no outside neighbors other than A,B.

These conclusions also hold for the contact-atom multigraph before
parallel side atoms are aggregated. Parallel copies can be routed
next to their pair edge; deletion connectivity and the face argument
are unchanged. An edge omitted by body pair has all its atoms omitted.

## 3. Replace the two omitted force blocks by two auxiliary edges

At any physical body, its full force vectors, in the embedding's
cyclic order, form a closed counterclockwise convex polygon, possibly
degenerate. This is the force-normal order and convex-vector-polygon
lemma proved in the parallel-force manuscript. It includes all positive
circle atoms separately.

At A replace the consecutive omitted block of this polygon by its
chord; do likewise at B. Removing consecutive boundary vertices from
a convex polygon leaves a convex polygon, allowing degeneracy. Write
F_A,F_B for the sums of the two omitted vector blocks. The retained
force vectors and each such sum still balance at their terminal.
Summing all equilibrium equations over H cancels every H contact, so

```text
F_A+F_B=0.                                           (1)
```

Neither vector vanishes. Otherwise both would vanish, and the positive
contact forces of H alone would balance at every vertex. Dot those
force equations with the corresponding body centers and sum. In the
gradient sign convention, a contact oriented from i toward j contributes

```text
mu*d dot (c_i-c_j) = -mu*(h_i(d)+h_j(d)) < 0,
```

where mu>0 and h denotes directional halfwidth. H has contacts, so their
strictly negative sum contradicts equilibrium. This uses no torque
condition on the omitted blocks.

Draw a new ground vertex in H's outer face and join it to A and B
through the two empty omitted corners. Give these edges vectors F_A,F_B
at the terminal ends and their negatives at ground. This is a balanced
planar multigraph. Its body force polygons are convex: at U they are
unchanged, and at A,B they are the convex chord replacements above.
The ground polygon is the segment traversed in both directions, by (1).

The reciprocal face-potential construction and signed-area cancellation
of Sections 4--5 of the parallel-force manuscript now apply verbatim.
Every body polygon has nonnegative area, ground has zero area, and
their signed areas sum to zero. Every body polygon is therefore a
segment. All its incident force vectors are parallel. Connectivity
propagates one common line throughout H.

This replacement is only in an auxiliary balanced graph. It does not
move a physical force point, alter a physical torque equation, or
assert that either sum F_A,F_B is a single physical contact force.

## 4. The physical region is a bounded-width parallel network

Choose a unit direction e along this common line. Orient every H contact
from its left body to its right body in direction e. The center
projection increases by `h_i(e)+h_j(e)>=1` along an oriented edge, so
this is a directed acyclic graph. At every body of U the positive
incoming and outgoing magnitudes agree. Its sources and sinks must
therefore be A,B. Relabel and reverse e if necessary so A is the
unique source and B the unique sink. Every vertex and edge of H lies
on a directed A-to-B path.

All H contacts at A consequently lie on its right support face, and
all those at B lie on its left support face. Each unloaded body's
left and right force totals are equal and positive. Aggregate their
physical application points separately on the two support faces.
Torque balance makes the displacement between these two effective
points parallel to e. If the support faces are sides, the body's
width is one. Otherwise they are opposite vertices, and the same
displacement condition makes e a diagonal, with width sqrt(2).
Thus every U body is an effective S or D transmitter.

Let p_A,p_B be the force-weighted average of the A--U and B--U
physical contact points, respectively. The common total force magnitude
at the two ends is positive by Section 3. Summing the original torque
equations over the unloaded set U cancels every internal contact wrench.
It gives

```text
(p_B-p_A) cross e=0.
```

The endpoint points belong to the two actual support faces by convexity.
Projection along any directed path shows that their signed separation
is positive and is the sum W of the internal full widths. Hence

```text
p_B-p_A=W*e,
e dot x<=e dot p_A for x in A,
e dot y>=e dot p_B for y in B.
```

These identities prove `dist(A,B)=W`, not just a projection bound.
The endpoint-center projection difference is at least `1+W`, while
both center norms are below 25/16. Thus `W<17/8`. Since each internal
width is one or sqrt(2),

```text
W in {1,sqrt(2),2}.                                  (2)
```

For W=1 every directed path has exactly one internal S body. There
cannot be an edge between two U bodies, since it would belong to a
path with at least two internal bodies. Connectivity of U then forces
U to be a single S body. The identical argument gives a single D body
when W=sqrt(2).

For W=2 every path has exactly two S bodies. All U bodies therefore
have the same side frame and lie in two consecutive unit-width columns.
Every first-column body has a positive contact to A and to the second
column; every second-column body contacts B and the first column.

There are at most two bodies in either column. If the relevant terminal
support face is a vertex, all its column neighbors contact that same
point. The point must lie in the relative interior of each neighbor's
support side: a vertex/vertex side-normal contact would violate the
strict-normal convention. Their transverse unit intervals therefore
all contain that height in their interiors, so there is at most one.
If the terminal support face is a side, its length is one and its frame
is parallel to the column bodies. Their unit transverse intervals have
pairwise disjoint interiors and each overlaps that unit support side
in positive length, again by the strict-normal convention. At most
two such intervals are possible.

Both columns are nonempty. This proves the two-to-four-body statement
and completes the theorem.

The result applies to every unloaded connected component after deleting
any two terminals. Equivalently, it applies to a nonempty connected
unloaded set with exactly two outside body-neighbors. It does not
automatically apply to a region with three or more outside
body-neighbors or to a subset that omits some of its positive contacts.
