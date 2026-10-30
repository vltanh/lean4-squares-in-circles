# Two loaded bodies force parallel contact forces

**Status:** hand theorem; root and two independent full mathematical
reviews passed on 2026-10-30. This is a reduction for a freshly selected planar physical
stress, not a claim about every stress on the same packing. It does not
by itself close the two-loaded branching family or change a finite
catalog count.

Work in `79/40<=R<=3/sqrt(2)`, and use the jointly selected physical
stress of
[PLANAR_SELECTED_PHYSICAL_STRESS.md](PLANAR_SELECTED_PHYSICAL_STRESS.md).
Consider one connected positive-contact component with exactly two
loaded bodies A,B. A body is loaded when at least one of its circle
constraint coefficients is positive. Other bodies in the component may
have geometric circle vertices with zero circle coefficients.

**Theorem.** Every positive contact force in this component is parallel
to one common line. The total circle-force vectors on A and B are
nonzero, opposite, and parallel to that line.

The proof does not initially assume parallel contact forces. It uses
force balance, positivity, convexity, and a planar embedding compatible
with the cyclic order of the force normals. Torque balance is not needed
for this reduction.

## 1. Force vectors and the augmented graph

Use the gradient sign convention. At a contact from body i toward body j,
the force vector on i is `mu*d`, where `mu>0` and d is an outward normal
of i pointing toward j. The vector on j is `-mu*d`. A positive circle
atom at a vertex w contributes `2*lambda*w`, where `lambda>0`.
The equilibrium equation at each body is that the sum of these vectors
is zero.

Keep the positive contact atoms before aggregation by body pair, after
the four-way replacements in the planar selection theorem. This atom
multigraph has the planar embedding constructed there. Attach a ground
vertex in the exterior region, with an edge for each positive circle
atom. Draw the beginning of a circle edge from the relevant body center
through its circle vertex; extend it outside the containing circle to
the ground vertex. These outside arcs can be chosen disjoint except at
ground, with their cyclic order there the reverse of their order on the
containing circle. The circle-point lemma and the exposure construction
ensure that these edges do not cross any contact edge.

The vector on the body end of a circle edge is `2*lambda*w`, and that
on ground is its negative. Summing all body equilibrium equations
cancels contact forces, so ground is balanced too. This gives a finite
connected balanced planar multigraph. Multiple atoms at one circle
vertex can first be added into one edge.

## 2. The embedding respects cyclic order of the force directions

At distinct boundary points of a convex square, outward support normal
directions occur in their boundary cyclic order. At a vertex, all
possible outward normals lie in its ninety-degree normal cone; at a
relative side interior the normal direction is unique. Thus distinct
contact points cause no ordering difficulty. Repeated equal directions
may be placed in any order within their tie.

We also need this order at a point shared by several squares. Intersect
each incident square's tangent cone at that point with the direction
circle. Its sector has angle ninety degrees at a vertex or 180 degrees
at a side interior, and the sectors have disjoint interiors. For a
fixed body i, a normal pointing toward another body j belongs both to
i's outward normal cone and to the nonnegative dual of j's tangent
sector. A ninety-degree sector is its own nonnegative dual, and the
dual of a 180-degree sector is its bisector ray. Thus, in either case,
the normal pointing toward j lies in j's own tangent sector. Different
neighbor sectors have disjoint interiors, so their permitted normal
directions occur in the same neighbor order. Equality allows only a
shared endpoint direction. Intersecting these permitted directions with
i's normal cone preserves their order.
This proves that the local two- or three-port drawing in the planar
selection theorem can use the cyclic force-normal order at each body
port. At a four-square point, the remaining graph consists of perimeter
edges and at most one opposite-pair edge. Its side normals are the two
axis directions bounding each quarter's normal cone, and the remaining
opposite-pair normal is strictly between them. Its noncrossing local
drawing has exactly the required order as well.

Consequently the contact-atom planar embedding can be chosen with the
force vectors at every body in their cyclic angular order. This does
not require any extra restriction on the already chosen strict normals,
nor alter the coherent four-way or generic polynomial choices.

A circle-force vector w is an outward normal at its circle vertex:
for every different point x of that square,

```text
w dot (x-w) <= -|x-w|^2/2 < 0.
```

Indeed `|x|^2<=|w|^2=R^2`. No other square contains this circle point.
The circle exposure edge can therefore be inserted in the same cyclic
normal order. Hence the augmented graph also has the required force
order at every body.

## 3. Merge the circle forces separately on each loaded body

A square in this radius window has at most two circle vertices. If it
has two, they are adjacent: in square-frame coordinates the farthest
vertices maximize the two separate linear terms involving the center,
and two maximizers require exactly one zero center coordinate. The
center cannot be zero in this radius window. Rotate and reflect so that
the two circle vertices are

```text
(T,-1/2), (T,1/2),       T=sqrt(R^2-1/4).
```

Their connecting side is the outer side `x=T`. No other packed unit
square can contact its relative interior. Such a square would have to
lie in `x>=T`, and its horizontal width is at least one, giving a point
with `x>=T+1>R`. No other square can contact either circle endpoint,
by the circle-point lemma. Thus there are no contact atoms on this outer
side or at its endpoints.

The two positive circle edges, when both occur, are therefore consecutive
at their body vertex. They are consecutive at ground as well. To see
the latter, the planar selection theorem gives angular distance less
than `pi/12` between any circle vertex and its square's center ray,
whereas two loaded center rays have separation greater than `pi/5`.
These two circle-vertex clusters are disjoint, so no circle edge of the
other loaded body lies between the two in this cluster.

Merge these consecutive parallel graph edges, replacing their vectors
by their sum. Topologically their outer-side corner at the body and
their circle-cluster corner at ground face the same region between the
two exposure paths. Neither corner has another incident edge. The two
edges therefore bound an empty two-edge face: connectedness prevents
any graph vertex or edge inside this region without an attachment at
one of its corners.
Equivalently their exterior exposure paths can be merged inside a narrow
neighborhood of their union and their intervening face. This preserves
planarity and the rotations of every other edge.

At the loaded body the two original force directions differ by less
than pi. The direction of their positive sum lies strictly between them.
Replacing these consecutive directions by that sum therefore preserves
the cyclic force-direction order. If just one circle coefficient is
positive, no merging is needed. This replacement is only in the
auxiliary balanced graph. It does not assert that a weighted circle
application point has this vector as a physical outward normal, and
does not change the physical stress used for later torque arguments.

The resulting graph has precisely two ground edges, carrying nonzero
vectors `F_A,F_B` at the body ends. Each is a positive sum of circle
vectors in an interval of width less than pi, so neither vanishes.
Ground balance gives `F_A+F_B=0`.

## 4. A balanced planar graph has reciprocal face potentials

For clarity, use the following elementary planar identity. Let a finite
connected graph be embedded on the sphere. Each end of each edge has a
vector, opposite to the vector at its other end, and suppose the vectors
sum to zero at every vertex. For an edge oriented from i to j, let L,R
be its left and right faces, and let f be its vector at i. There are
vectors q_F assigned to the faces such that

```text
q_L-q_R=f.                                             (1)
```

To construct them, fix one face potential and integrate these differences
along the dual graph. The increment around the small dual cycle about
any primal vertex is its vector sum, hence zero. Every closed dual walk
on the sphere is a sum of these vertex-boundary walks; therefore the
integral is independent of path. This also covers parallel edges and
repeated face occurrences. A bridge would have L=R, and balance already
forces its vector to be zero, consistently with (1).

Read the faces incident to a vertex i in counterclockwise order, with
repetitions if needed. Their potentials form a closed polygonal walk
P_i whose successive edge vectors are exactly the force vectors at i,
in the embedding's cyclic order. Define its signed area by the shoelace
sum, which is meaningful even when the walk has repeated points.

Every primal edge contributes the same dual segment to the two endpoint
walks, with opposite directions. Cancellation of these segment terms
gives

```text
sum_i signed_area(P_i)=0.                              (2)
```

No injective embedding or disjoint-interior property of these reciprocal
polygons is asserted or needed for this algebraic identity.

## 5. Convexity and zero total area force one direction

A closed vector polygon whose nonzero edge vectors occur in cyclic
angular order is a counterclockwise convex polygon, allowing collinear
edges and the degenerate case. One elementary verification is to project
all its successive vertices onto the left normal of any chosen edge.
Starting with that edge, the subsequent edge projections are first
nonnegative and then nonpositive, and their total is zero. Every partial
sum is therefore nonnegative. All vertices lie to the left of every
oriented edge, proving convexity. Its signed area is nonnegative, and
area zero means that all its vertices, hence all its edges, lie on one
line.

Apply the reciprocal identity after the circle-edge merging. By
Sections 2--3, every body polygon P_i has its edge vectors in cyclic
angular order, so its signed area is nonnegative. The ground polygon
has only the two opposite vectors `-F_A,-F_B`, and has signed area zero.
Equation (2) therefore forces the area of every body polygon to be zero.
All force vectors incident to any one body are parallel.

Every positive contact edge has a nonzero vector. If its two endpoint
bodies have parallel-force lines, that edge forces the two lines to
agree. Connectivity propagates one common line through the whole
component, and its two ground-edge vectors lie on that same line.
These are exactly the original contact-force vectors and the original
total circle-force vectors. This proves the theorem.

The remaining geometric classification may use the unchanged torque
equations of the original physical stress. The auxiliary ground-edge
merging supplied only the force-direction conclusion; it did not
replace any physical circle application point or claim that every
unloaded body has graph degree two.
