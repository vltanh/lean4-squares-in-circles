# Independent review: exterior boundary edges and forbidden boundary-hub diamonds

Date: October 25, 2026. Reviewer: root, independently of `abc_review`.

**Verdict: PASS.** The complete source
`BOUNDARY_EDGE_OUTER_FACE_AND_DIAMOND_EXCLUSION.md` establishes that an
actual positive boundary-to-boundary edge is exterior in a sufficiently
close physical embedding. Such an edge cannot have two common positive
neighbors. The original complete load covers then close the eight
existing gates listed in Section 6 below. No new scalar certificate,
minimizer premise or changed force degree is used.

## 1. Full inherited geometric inputs

I read `CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md` in full, including its
actual center/contact crosscut, arbitrary physical circle-corner choices,
circle-clear pocket dilation and angular-neighbor contradiction. Its
empty-pocket conclusion applies to any physically touching boundary pair
in the stated radius window; it is not restricted to seven boundary
bodies or to positive circle weights.

I separately read `NO_POSITIVE_K4_SUBGRAPH.md`. Its Sections 1--2 supply
an arbitrarily small physical embedding and prohibit an embedded
three-cycle from enclosing any other original center. That proof applies
to every three-cycle of the selected graph, not only to a K4 instance.
It keeps coincident contacts and small junction-routing faces by using
the concentric 19/20 inner square and an explicit epsilon<1/80 clearance.

`NO_UNLOADED_DIAMOND_HUB.md` was read separately to check the exact
degree-three load implication and its compatible preselection scope.
Its neighbor vertices may have arbitrary extra positive forces; its
condition concerns only the genuine three-force hub. These accepted
prerequisites are not replaced by a diagrammatic assumption.

## 2. Augmenting the embedding by circle rays is legitimate

For each of the two actual boundary squares, the open center-to-circle
corner ray lies in its open interior. No other body's strand can enter
it. A same-body center-to-contact ray has a different direction, because
otherwise its unique boundary endpoint would be that same circle point;
two packing squares cannot share a circle point. This covers a shared
mean at either endpoint of its overlap interval as well as a strict
singleton application.

The finite set of distinct directions leaves a positive angular sector
around each auxiliary ray. Away from the center disks the compact
nonincident strands have positive clearance. The existing local physical
embedding can therefore use smaller tubes/disks and leave these sectors
unused. All actual multiple-contact routing orders remain unchanged.
The selected forces, means and normals are not modified; only the proof
drawing is chosen more closely to the original strands.

Every pair-contact point lies strictly inside the circle. The finite
positive graph therefore has positive clearance from the circle after
choosing sufficiently small neighborhoods. The circle arc, both auxiliary
rays and the embedded UV edge form the claimed simple closed curve.

## 3. Winding and the exterior-face conclusion

The original crosscut pocket contains no other center: a center inside
would put the connected open interior of its square entirely on that
side of the crosscut, contradicting the empty-pocket theorem. No center
lies on the crosscut or on its selected circle arc.

The embedded UV edge can be homotoped to its original contact strand
inside an arbitrarily small neighborhood of U union V. Every other
center has distance at least 1/2 from U union V, by its own open
inscribed disk and interior disjointness. Thus this homotopy avoids
every other center. Keeping the auxiliary rays and circle arc fixed
preserves winding number about every such center even if intermediate
curves are not simple. Since the final curve is simple, its bounded
side contains no other graph vertex.

No original graph edge can occupy that bounded side either. It cannot
cross the augmented embedded boundary; its only possible endpoints
there or on that boundary would be U,V. Body-pair aggregation gives a
simple graph, whose only U--V edge is already the boundary edge and
which has no loops. An edge entering from U and going to an outside
vertex would have to cross the boundary to leave. This explicitly
justifies the graph-empty region rather than assuming a face from an
empty list of centers.

The auxiliary rays and circle arc are not edges of the original graph.
An interior point next to UV on this empty side can pass through the
region and across the arc to infinity without meeting the original
graph. Hence UV is on its unbounded face. The construction can be made
for each requested edge; it does not require a simultaneous reselection
of any physical normal or positive multiplier.

## 4. Diamond topology and the exact-degree corollary

Restrict this physical embedding to UV and its two common neighbors A,B.
Deleting other drawing edges does not destroy UV's exterior path. It
does not delete any force from a physical equilibrium equation.
The restricted diamond is biconnected, so its exterior face boundary is
a simple cycle. The only cycles containing UV are its two tip triangles.
Thus the exterior boundary is one of those triangles and the other
tip center is on its bounded side. This contradicts the actual
no-enclosed-center theorem, including degenerate physical junctions.

The central UV edge must be a positive edge in the selected simple graph.
The source correctly does not add an unselected zero-stress contact.
Its conclusion needs only that U,V physically touch the circle, including
zero circle multipliers; no endpoint degree is assumed.

Corollary 4.2 follows without an extra geometric step: if both hubs of
any positive diamond have their true degree exactly three, the complete
no-unloaded-hub theorem makes both positively loaded and hence physically
boundary. The preceding contradiction applies. The tips may have any
additional positive forces. This is a reusable local graph exclusion,
not a license to truncate a higher-degree hub.

## 5. Whole original graph/load joins

I read the complete graph labels and load table in
`FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md`. In the subdivided K4 with
edges AX,XB,AC,AD,BC,BD,CD, the C,D hubs retain exact degree three
when the genuine leaf is at X or A (or the symmetric B). Their positive
diamond CD/CA/DA/CB/DB is present. Both are forced loaded regardless
of the real added leaf force at the root. Both entire root orbits are
therefore excluded for either S/D leaf, with all three completion squares.
The previous S-only exit at root A is not needed to restrict the new
whole D result; its original slider remains arbitrary.

For the diamond with one leaf at each tip B,C, the hubs H,K also retain
their exact degree three. Each hub's other central neighbor touches both
tips, so the same true-degree load theorem makes H,K boundary. The new
topological obstruction therefore excludes every SS, SD and DD placement,
physical mask, individual circle-weight endpoint and actual contact mean.
The preexisting distinct-D-root exit remains compatible but is not needed
as a premise of this complete layout exclusion.

## 6. Eight exact existing gates and retained limits

The root verified that each of these eight labels existed and was
unchecked in the unchanged 2,513-label roadmap:

1. `M6.B5L.SUBDIVIDED_K4.NEW.LCD.S`
2. `M6.B5L.SUBDIVIDED_K4.NEW.LCD.D`
3. `M6.B5L.SUBDIVIDED_K4.NEW`
4. `M6.B5L.SUBDIVIDED_K4.ENDPOINT.LCD.D`
5. `M6.B5L.SUBDIVIDED_K4.ENDPOINT`
6. `M6.B4L2.DIAMOND.TWO_TIPS.LHK.SS`
7. `M6.B4L2.DIAMOND.TWO_TIPS.LHK.SD`
8. `M6.B4L2.DIAMOND.TWO_TIPS`

Their full original scopes are discharged. The remaining subdivided-K4
hub-root and other rooted types require their own exits; neither coarse
C1.5.b1 nor C1.4.b2 is closed by these eight gates alone.

This is a geometric/topological whole-family proof. No coefficient packet,
angle mesh, force reassignment, body contraction or secondary minimizer
is added. All nine original physical bodies remain. The unrestricted
bound, original equality classification and older complete prerequisite
audit remain open. No Lean compilation, CI or workflow dispatch.
