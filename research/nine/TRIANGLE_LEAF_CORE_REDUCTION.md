# Complete core and region reduction for the four-body triangle-plus-leaf cell

**Status: complete hand assembly; independent hand audit passed.** In the declared window

\[
79/40\le R\le\sqrt{1105}/16,
\]

let the selected physical positive component have the triangle-plus-leaf graph C1.3.b1. This manuscript gives its complete load, leaf/articulation and completion-region reduction. It retains all five additional physical squares. The S branch is excluded in S_LEAF_TRIANGLE_EXCLUSION.md; the remaining D branch is not excluded here.

The selected certificate has the strict nonradial normal convention at point-only vertex/vertex contacts away from the origin, as supplied simultaneously by PHYSICAL_BODY_GRAPH_UNCROSSING.md and RADIAL_BRIDGE_AND_LEAF_REDUCTION.md.

## 1. Exactly three loaded bodies and their physical noncontacts

Name the leaf L, its articulation A, and the other triangle bodies B,C. The positive edges are AL, AB, BC, CA. A degree-one body cannot be unloaded, because one positive contact force cannot sum to zero. Thus L is loaded and its edge is a radial bridge.

The central endpoint theorem for bridges makes A physically circle-clear: one incident body meets the disk of radius max(R-2,0), every body meeting that disk is circle-clear, and the loaded L cannot be that endpoint. Hence A has zero circle weight.

Both B and C are loaded. Otherwise the unloaded degree-two body would transmit equal opposite contact forces between its two opposite support faces. Its two neighbors would be separated by a positive projection gap equal to its width and could not physically touch, contradicting the third edge of the triangle. This is the complete transmission argument in PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md.

Thus the loaded set is exactly {L,B,C}. The loaded physical noncontact graph is connected by ACUTE_LOADED_CONTACT_GRAPH.md. Since B and C physically touch, its only possible edges joining all three vertices are LB and LC. Consequently

\[
L\cap B=L\cap C=\varnothing. \tag{1}
\]

This is disjointness of the closed physical squares, not merely absence of positive edges. Every other physical square remains in the packing, even if it touches the circle or touches a core body with zero stress.

## 2. Exact force and moment equations

Rotate so the bridge normal from A to L is e=(1,0), and write its positive magnitude as mu. Orient the triangle A to B to C to A, and write

\[
f_{AB}=\mu_{AB}n_{AB},\quad
f_{BC}=\mu_{BC}n_{BC},\quad
f_{CA}=\mu_{CA}n_{CA},
\]

with all magnitudes positive and normals directed toward the next body. At each actual application point p_ij, the two bodies lie in the opposite closed support half-planes normal to n_ij. Shared-side applications may be any weighted mean point of the actual shared segment.

For X=L,B,C, let m_X be the sum of its positive circle-corner atoms lambda_z z. The four force equations are

\[
\begin{aligned}
f_{AB}-f_{CA}+\mu e&=0,\\
f_{BC}-f_{AB}+2m_B&=0,\\
f_{CA}-f_{BC}+2m_C&=0,\\
-\mu e+2m_L&=0.
\end{aligned} \tag{2}
\]

In particular

\[
m_B+m_C=-m_L=-\frac\mu2e. \tag{3}
\]

The bridge moment about the origin is zero. The three body moment equations therefore give the common cycle moment

\[
\det(p_{AB},f_{AB})=
\det(p_{BC},f_{BC})=
\det(p_{CA},f_{CA})=:H. \tag{4}
\]

Moreover H is nonzero: BC joins two physically circle-touching bodies, so its genuine supporting force line cannot be radial, by CIRCLE_CONTACT_ANGULAR_ORDER.md. Equation (4) does not make either other cycle edge radial.

All positive circle corners of B and C are pairwise acute. Corners belonging to different bodies are acute because B,C touch; two corners in the same unit square satisfy

\[
z\cdot w=R^2-\tfrac12|z-w|^2\ge R^2-1>0.
\]

If Z is the set of these positively weighted corners, then for each z in Z,

\[
z\cdot(m_B+m_C)=\sum_{w\in Z}\lambda_w(z\cdot w)>0.
\]

By (3), every such z has z_1<0. Their directions lie in the open left semicircle and have pairwise separation less than pi/2. Since their weighted vertical sum is zero and they cannot all have one common direction, there are positive atoms on both sides of the negative horizontal axis. Equivalently their extreme directions satisfy

\[
\pi/2<\phi_-<\pi<\phi_+<3\pi/2,
\qquad \phi_+-\phi_-<\pi/2. \tag{5}
\]

For the noncollinearity in this statement, if all vertical components were zero, both m_B and m_C would have the same negative horizontal direction, contradicting distinct loaded-resultant directions in CYCLIC_GLOBAL_CONTINUATION.md. The argument allows one or two physical circle corners on either body and every positive-weight mask.

## 3. Complete D-leaf articulation domain

The leaf theorem has exactly the two forms D and S. In the D form, put

\[
d=R-\sqrt2>0.
\]

The physical leaf is the unit square with radial diagonal, inner vertex p=(d,0), outer vertex (R,0), and center (R-1/sqrt(2),0). The circle vector is m_L=lambda_L R e, so mu=2 lambda_L R.

The bridge point p cannot be a vertex of A. It is already a vertex of L; a point-only vertex/vertex bridge away from0 is excluded by the selected nonradial normal convention. If both bodies had a common side segment through p, its support normal would be a side normal of L, whereas e is a diagonal direction of L. Thus that alternative cannot occur either.

Therefore p lies in the relative interior of A's supporting side normal to e. A has its side frame parallel to the coordinate axes and necessarily

\[
A=[d-1,d]\times[t-\tfrac12,t+\tfrac12],
\qquad -\tfrac12<t<\tfrac12. \tag{6}
\]

Conversely this describes the entire possible articulation support face in the selected D branch. Every other condition on B,C and the remaining squares must still be imposed; (6) alone is not a realization theorem for the whole core.

The endpoints |t|=1/2 are excluded for this selected certificate because they put p at A's vertex. A limiting physical packing is not discarded: the global physical stress theorem is reapplied with the prescribed strict nonradial point normals. Such a packing must then appear under its resulting positive graph, rather than under a forbidden radial point-only bridge in this cell.

Since d<1 in the declared upper window, (6) also shows that0 is in the open interior of A. This observation is specific to the D branch.

## 4. Complete S-leaf articulation domain

In the S form, put

\[
d=\sqrt{R^2-\tfrac14}-1.
\]

The physical leaf, bridge point and circle vector are

\[
L=[d,d+1]\times[-\tfrac12,\tfrac12],\quad
p=(d,0),\quad
m_L=\lambda_L(d+1)e.
\tag{7}
\]

Thus p is a rightmost support point of A. There are exactly the following pose branches, allowing harmless overlap under square symmetries.

**S0, aligned side contact.** The support face of A is its right side, giving

\[
A=[d-1,d]\times[t-\tfrac12,t+\tfrac12],
\qquad -\tfrac12\le t\le\tfrac12.
\tag{8}
\]

The entire interval is required. The endpoint cases still have genuine shared-side contact with L.

**S+, tilted vertex contact.** Choose 0<theta<=pi/4, a=cos(theta), b=sin(theta), with side frame u=(a,b), v=(-b,a). The center is

\[
c_A=\left(d-\frac{a+b}{2},\frac{a-b}{2}\right).
\tag{9}
\]

Its unique rightmost vertex is p; its inward side vectors there are (-a,-b),(-b,a).

**S-, the horizontal reflection.** Reflect the complete packing and force system in the horizontal axis. This gives the reflected frame and center

\[
c_A=\left(d-\frac{a+b}{2},-\frac{a-b}{2}\right).
\tag{10}
\]

To see exhaustiveness, a right support face of a square is either a side, forcing the aligned frame (8), or a unique vertex. In the latter case both inward side vectors have negative first coordinates. Relabeling sides, square quarter-turn symmetries and one horizontal reflection give the vectors in S+. These operations preserve every packing and equilibrium condition. The angle endpoint theta=pi/4 is covered by both reflected charts; theta tending to0 gives only the two endpoint heights in (8), not its interior slider heights.

S_LEAF_TRIANGLE_EXCLUSION.md excludes all three complete S branches using one inaccessible-circle-arc argument. No assumption that0 belongs to A is used there.

## 5. Exhaustive routing of all five completion squares

Choose one circle corner on each of L,B,C and draw its center-to-corner spoke. Each open spoke lies in its own square's open interior. A circle point belongs to only one packing square, so these spokes are pairwise disjoint and cannot meet another body's open center/contact strand. The physical circle-contact angular-neighbor theorem puts B,C consecutively along their minor circle arc; the chosen circle corners preserve this order by CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md.

Every additional square's open interior is disjoint even from the closed union of the four core squares. Indeed, an open neighborhood of a point in any closed core square meets that square's open interior. Consequently the whole connected open extra square must lie in one component of the complement of any barrier graph drawn inside the core squares and their three spokes.

There are two exhaustive contact-junction cases.

### 5.1. A,B,C have no common point

Choose one actual contact for each triangle pair. The three points are distinct; coincidence would give a common point of all three bodies. Their center/contact loop is Jordan because each open half-strand lies in its own square interior and distinct boundary endpoints determine distinct rays from its center.

The leaf bridge and its spoke lie outside this Jordan loop. Their interior strands avoid it except at A's center: within A the bridge contact is distinct from the two triangle contacts, and (1) keeps L disjoint from B,C. A path from this branch to its circle corner cannot lie on the bounded side of the triangle without crossing the loop. The B and C spokes also lie on the exterior side by the same circle-endpoint argument.

The ring and the three disjoint exterior paths to the circle therefore give four regions: the inner triangle region and three exterior boundary-port regions. The inner one has capacity0 by CONTACT_RING_HOLE_AREA.md. The exterior region along the minor B-to-C arc is the touching-boundary-pair pocket and has capacity0 by CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md. Hence every completion square lies in one of the two remaining regions, involving respectively L and B, or L and C.

### 5.2. A,B,C have a common point q

Their common intersection is a single point. If it contained a nontrivial segment, at an interior point of that segment each of three squares would have an inward tangent sector of angle at least pi, contradicting disjoint open interiors.

Use the three segments from q to the centers of A,B,C. Join A's center to L's center through the actual bridge point and retain the three circle spokes. These curves form a tree with three circle ports. There is no intersection away from its declared common vertices: open strands lie in separate square interiors, and (1) keeps the L branch disjoint from B,C. Distinct support endpoints at A give distinct rays. This tree partitions the disk into three boundary-port regions.

The B-to-C crosscut through q bounds exactly the exterior pocket of that touching pair; that region has capacity0. The other two regions again involve L/B and L/C. There is no genuine triangular hole at this common junction, and no artificial drawing face is counted as available capacity.

Thus the same routing conclusion holds in both cases. A second circle corner on any core body can subdivide these regions using that same body as a barrier; it cannot create a route between them. Additional physical contacts can only add obstacles. Other zero-stress bodies that touch the circle are retained in their respective permitted regions.

## 6. Exact remaining whole-cell obligation

**Theorem 6.1 (complete triangle-plus-leaf reduction).** Every selected C1.3.b1 core in the declared window has exactly the three loaded bodies L,B,C, satisfies (1)--(5), and lies in the complete D/S articulation cover (6)--(10). Every one of its five additional physical squares lies in one of the two residual articulation/leaf regions. The S branch is impossible by the separate complete theorem.

Consequently it remains to prove, for every D core satisfying all actual physical contact, circle, force and torque conditions, that the two residual regions have **joint unit-square capacity at most four**, or to exclude every such core in the entire radius window. No separate bound of two per region, symmetry of B/C, common square orientation, narrower t interval, or unproved radiality of cycle edges is a premise.

Closing that one remaining D obligation will close C1.3.b1. This manuscript itself is a complete reduction and does not claim that final capacity bound.
