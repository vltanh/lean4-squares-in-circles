# An enlarged core polygon reduces the full loaded ring to the local outer caps

**Status:** reviewed conditional hand theorem; root and independent full
mathematical reviews passed on 2026-10-30, including the enlarged boundary,
SS replacements, winding coverage, and all pair-support and radial cases.
The additional outer-corner estimate is an explicit hypothesis, and the
certificate must satisfy the compatible normal selections specified below.

Consider an entirely loaded positive seven-ring of the physical stress of
a hypothetical ten-square minimizer, with

```text
6241/1600<=q=R^2<9/2.
```

Use a fresh certificate satisfying the normal selections in
[SEVEN_RING_ALL_INNER_FACE_CAPACITY.md](SEVEN_RING_ALL_INNER_FACE_CAPACITY.md).
Any additional selections used to establish the hypothesis below must be
made jointly with those selections, before constructing and classifying
the stress. In particular, no preservation of an old positive ring under
reselection is presumed.

Use the ownership alphabet, radial classification, inner-corner bounds,
and U2/U3 exclusion from the reviewed ring notes. Make the following
additional hypothesis:

> Every unique-circle U4/U5 body has its extra inner-boundary corner B
> (respectively C in the alphabet's U5 coordinates) of squared norm at
> most `33/20`.

The intended source of this hypothesis is
[LOADED_OUTER_CORNER_CLEARANCE.md](LOADED_OUTER_CORNER_CLEARANCE.md), with
its compatible strengthened certificate selection. The geometric and
algebraic outer-cap estimates used here are
[OUTER_SIDE_SPIKE_CAP_BOUND.md](OUTER_SIDE_SPIKE_CAP_BOUND.md) and
[OUTER_SIDE_CAPACITY_MARGIN.md](OUTER_SIDE_CAPACITY_MARGIN.md).

**Conditional theorem.** Under the stated hypothesis, every vertex of
each of the three inner squares has squared norm strictly below `83/50`.
Consequently the loaded seven-ring has no ten-square completion, since
the three-square minimum squared radius is `425/256>83/50`.

The proof includes SS, SV, VS, and VV pair supports, every radial load
split, and all allowed side-endpoint contacts. It does not require the
polygon of core corners to be convex or star-shaped.

## 1. Two corner ports allow the outer bodies in the boundary construction

For each body i let `L_i` be its incoming corner port and `R_i` its
outgoing corner port. For every body already included in
[SEVEN_RING_OUTER_EDGE_REDUCTION.md](SEVEN_RING_OUTER_EDGE_REDUCTION.md),
use its previous core corner for both ports: `L_i=R_i=A_i`.
Thus the unique-circle rows U1,U6,U7,U8,U9,U10 use the opposite circle
corner, and radial bodies retain exactly the choices in the radial
capacity theorem. Zero-length pieces are omitted.

The only new rows are U4 and U5. In the ownership alphabet's positively
oriented local coordinates, their paths and ports are

| Row | Boundary path in the cyclic direction | Incoming port | Outgoing port |
|---|---|---|---|
| U4: R -> A | incoming contact -> B -> A | B | A |
| U5: A -> T | A -> C -> outgoing contact | A | C |

The letters R and T in the row column denote square edges; `R_i` denotes
the outgoing port only. Both paths are simple paths on the square's
boundary, with its interior to the right. The segment `L_i R_i` is the
new unit side joining the extra corner to the old core. All other body
paths are the previously reviewed paths through their single core.

Every old core satisfies `|A_i|^2<36/25`. By hypothesis every extra
corner has squared norm at most `33/20`. Therefore the convex hull H of
all ports satisfies

```text
H is contained in the centered disk of squared radius 33/20.       (1)
```

At an outer body's strict V incidence the contact is its opposite
corner A, which is also the port for that incidence. This fact will make
every such contact triangle degenerate, regardless of the other body.

## 2. Every shared-side pair admits a boundary contact with a zero triangle

As in the shared-side theorem, only a geometric boundary contact is
chosen here. Every actual force direction, positive multiplier, and
aggregate application point remains fixed.

If neither S incidence is outer, use the inner overlap endpoint from
[SEVEN_RING_SHARED_SIDE_CAPACITY.md](SEVEN_RING_SHARED_SIDE_CAPACITY.md).
It is one of the two ports on that support line. The paths from the
ports to this point meet only there, and the resulting contact triangle
is the segment between the ports.

It remains to check an SS pair incident to an outer body. Up to a rigid
motion fixing the origin and, when needed, reflection with cyclic reversal,
write that body and its outer side as

```text
C=[X-1,X] x [-H-1,-H],
w=(X,-H-1),       B=(X,-H),
1/2<X<H,          q=X^2+(H+1)^2.                    (2)
```

These are the necessary inequalities from
[LOADED_OUTER_MIXED_RESTRICTIONS.md](LOADED_OUTER_MIXED_RESTRICTIONS.md).
The parallel SS neighbor lies in `x in [X,X+1]`. Its farthest horizontal
coordinate is X+1, so its farthest absolute vertical coordinate is

```text
Z=sqrt(q-(X+1)^2),
Z^2=H^2+2(H-X),       H<Z<H+1.                      (3)
```

A positive farthest vertical coordinate would give the interval
`[Z-1,Z]`. Since Z>H>1/2, its bottom satisfies `Z-1>-H`, and the two
squares could not touch. The neighbor therefore is exactly

```text
C'=[X,X+1] x [-Z,1-Z].                              (4)
```

Its circle vertex `(X+1,-Z)` is unique: X+1>1/2 and Z>1/2. Its common
support edge is an inner edge, not an outer one. In particular two outer
S incidences cannot face each other here. Its port on that edge is the
opposite corner

```text
D=(X,1-Z).
```

This is the ordinary core chosen for its permitted S row. The shared
segment is `x=X, -Z<=y<=-H`, and its inner endpoint is B. Choose

```text
Q=B.                                               (5)
```

Because `H<Z<H+1`, B is in the relative interior of C'’s support edge,
while D is strictly above B. The outer body's path meets the common line
only at B. The other body's path from D to B lies strictly above the
outer square except at B. Their paths consequently meet only at B.
The contact triangle `conv{B,Q,D}` is degenerate and contained in BD.
The reflection and reversal of this argument covers the other outer row
and either order of the two bodies.

For every SS pair we have therefore chosen a genuine shared point Q
equal to at least one port, with no boundary backtracking. Endpoint SS
intersections in the old inner-side case remain covered by its original
proof. The outer SS case automatically has positive overlap length by
(3).

## 3. The resulting boundary is a Jordan curve enclosing all inner squares

For each pair use the Q selected above if its support is SS. Otherwise
use its actual unique intersection point. Denote these choices by q_i,
where q_i is shared by bodies i and i+1. Join `q_(i-1)` to q_i on body i
along the path

```text
q_(i-1) -> L_i -> R_i -> q_i,                       (6)
```

with zero-length pieces deleted. For old rows this is precisely the old
path; for U4/U5 it is the path in Section 1.

The two chosen contacts on a body are distinct. Otherwise its two ring
neighbors would share that point, contradicting the separation of
nonneighbor loaded bodies. Each individual path is simple. Neighboring
paths at point-only contacts meet only at that point; at SS contacts the
same conclusion was proved in Section 2. Nonneighbor paths are disjoint.
Thus their concatenation Gamma is a simple closed polygon.

The physical ring theorem puts every point shared by two consecutive
loaded bodies strictly between their center rays. The center/contact
polygon using the chosen q_i is consequently the same positively
oriented Jordan ring construction as before. Replace, within each convex
loaded square, its two center/contact segments by (6). The resulting
homotopy avoids the closed disk of radius 1/2, since every loaded square
avoids that disk. Hence Gamma has winding number one about the origin,
and its bounded region Omega contains the half-radius disk.

Each inner-square center has norm below one. Its open inscribed disk of
radius 1/2 therefore meets the open half-radius disk about the origin.
The inner square's connected interior is disjoint from Gamma: an interior
point of that square lying in a closed loaded square would force an
overlap of interiors. Its interior must consequently stay in Omega, and
the entire closed inner square lies in the closure of Omega. This proves
the required enclosure without assuming that Gamma is convex.

## 4. The enlarged core chain and the exact covering identity

Let Pi be the closed oriented polygonal chain whose successive vertices
are

```text
L_0,R_0,L_1,R_1,...,L_6,R_6,L_0,
```

again suppressing repeated consecutive vertices. Pi need not be simple.
For each pair define the geometric contact triangle

```text
T_i=conv{R_i,q_i,L_(i+1)}.                           (7)
```

Cancellation of each chord from R_i to L_(i+1) gives the exact oriented
chain identity

```text
Gamma = Pi + sum_i [R_i,q_i,L_(i+1),R_i].            (8)
```

Every degenerate triangle below has q_i equal to one of its two ports,
so its oriented chain is zero and its geometric support is already in H.
For nondegenerate triangles the indicated order is counterclockwise.
The old proper and VV cases have their previously reviewed orientations.
For a new proper outer pair, the coordinates in Section 5 give determinant
`t*s>0` in the outgoing-S order; reflection with traversal reversal
preserves this sign for incoming S.

For a point outside H, Pi has winding number zero: a separating line
puts its whole chain in a half-plane not containing that point. Equation
(8) therefore implies that a point of Omega outside H belongs to one
of the triangles T_i. Equivalently, if it were outside all of them, all
terms on the right would have winding zero but Gamma would have winding
one. Points on any of the chains or on the boundary follow by closure;
the hull and the finitely many triangles are closed. Thus

```text
closure(Omega) is contained in H union union_i T_i.  (9)
```

This uses neither simplicity of Pi nor disjointness of the triangles.

## 5. Every contact triangle has the required capacity bound

Here is a complete division by pair support and by whether the chosen
ports changed.

**SS pairs.** Their triangles are the degenerate ones from Section 2,
already in H.

**A pair using an outer body's V incidence.** Its contact equals that
body's opposite corner and incidence port A. Thus its triangle is
degenerate. This includes VV pairs with one or two outer bodies and
proper pairs whose V body is outer.

**Proper SV/VS pairs using an outer S incidence.** If the other body's
contact already equals its port, the triangle is degenerate. Otherwise
that V contact has a selected geometric circle vertex adjacent to it,
and its port is the opposite corner to that vertex. This statement holds
for all unique-circle rows U6--U10 that can supply the V incidence and
for every nondegenerate radial V incidence, with exactly the choices
made in the radial capacity theorem. U2/U3 are excluded, and the outer
opposite-V cases were just removed.

Use (2), writing the actual proper contact as

```text
P=(X,-H-t),       0<t<1.
```

Strictness follows from the torque and neighbor-containment inequalities
in the outer-mixed note; P cannot be the circle corner. The neighbor's
strict V support gives incident unit directions

```text
u=(c,-s),       v=(s,c),       c,s>0, c^2+s^2=1.
```

The adjacent circle vertex must be `P+u`, and its port is `D=P+v`, as
proved in the outer-spike note. That note includes an initially radial
neighbor and in fact proves that its adjacent circle vertex is unique.
Consequently no radial boundary case is omitted by this setup. The
triangle is `conv{B,P,D}`, with signed double area

```text
(P-B) cross (D-B)=t*s>0.                            (10)
```

Its inner-square vertices satisfy the exact cap estimate

```text
|z|^2 < X^2+H^2+5(H-X)^2/(6H) <83/50.              (11)
```

The first inequality is the outer-spike theorem; the second is the
outer-side capacity margin, using the hypothesis `|B|^2<=33/20`.
Both estimates apply to the actual contact P; no force point was moved.

**All other proper pairs.** Neither incidence port has changed. The
nondegenerate pair has exactly the reviewed geometry and capacity bound
from the radial and outer-edge extensions. Those local estimates constrain
the S body's own other loaded neighbor where needed, but never require
that neighbor's other contact row to be an old row. The actual force and
neighbor used by those estimates remain fixed in this construction.
Thus each inner-square vertex in such a triangle has squared norm below
`83/50`.

**All other VV pairs.** Neither port has changed; any opposite-core
incidence is already degenerate. Every nondegenerate pair has the
circle-adjacent geometry of the all-inner-face theorem. Its compatible
open-interval and polynomial normal choices are part of the certificate
hypothesis. The theorem's radial cases, small-radius cases, and
diameter-disk cuts therefore apply without change, and again give the
strict `83/50` bound for each inner-square vertex in the triangle.

These cases exhaust all four pair-support types. In particular, a new
extra port occurs only at an outer S incidence; it never alters the
nondegenerate VV estimates or any old proper-contact cap.

## 6. The three-square contradiction

Let z be any vertex of one of the three inner squares. By Section 3 it
lies in the closure of Omega. By (9), either z belongs to H or it belongs
to one of the contact triangles. In the first case (1) gives

```text
|z|^2<=33/20<83/50.
```

In every other case Section 5 gives the same strict upper bound. Thus
all vertices of all three inner squares have squared norm below `83/50`.
Convexity of the centered disk places the entire three squares there.
This contradicts their known minimum squared radius, since

```text
425/256-83/50=1/6400>0.
```

The assembly is complete under its explicit extra-corner and certificate
hypotheses. The complete selected-certificate consequence is stated in
[SEVEN_RING_COMPLETE_CAPACITY.md](SEVEN_RING_COMPLETE_CAPACITY.md); this
conditional formulation keeps the precise local hypotheses visible.
