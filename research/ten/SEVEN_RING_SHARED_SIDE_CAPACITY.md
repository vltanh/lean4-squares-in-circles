# Shared-side pair contacts do not add spikes to the inner-face capacity argument

**Status:** hand proof; two independent full mathematical reviews passed
on 2026-10-29, including the shared-side boundary replacement and its
compatibility with the unchanged physical stress.

Use the entirely loaded physical seven-ring of a hypothetical ten-square
packing with `6241/1600<=R^2<9/2`. Assume no pair contact has support type
VV. Allow proper SV/VS contacts and SS contacts, including shared-side
endpoint contacts. Suppose every unique-circle body has local row in

```text
U1, U6, U7, U10.
```

Arbitrary radial-side bodies and circle-load splits remain permitted.

**Theorem.** Such a ring has no ten-square completion. All three inner
squares would be contained in the centered disk of squared radius `83/50`.

This extends the reviewed
[radial inner-face capacity theorem](SEVEN_RING_RADIAL_INNER_FACE_CAPACITY.md)
by permitting SS pair contacts. It does not exclude VV pairs or the
unique-circle rows U4,U5,U8,U9. Rows U2/U3 are excluded separately.

## 1. The core corners and the already bounded proper contacts

Use exactly the core corners chosen in Section 2 of the radial theorem:
a unique-circle body's opposite corner; the appropriate inner corner of
a radial mixed body; and the upper inner corner of a radial VV body.
The radial three-pattern classification used there did not assume proper
pair contacts, so it remains valid here. Every core corner has squared
norm below `36/25`.

Every S incidence belongs to a source U1, a unique-circle inner mixed
body U6/U7, or a radial mixed body. Its core corner is an endpoint of
that support edge. Choose its circle vertex as in the radial theorem;
that vertex lies on the parallel opposite edge. The other coordinate
of this circle vertex chooses the endpoint opposite the core corner.
This statement is geometric and permits a zero load on the selected
vertex of a radial body.

At every proper SV/VS pair retain the original force application point.
All its nondegenerate contact triangles satisfy exactly the previously
reviewed cap bound. In particular, a source body's cap proof may still
use its other original SS force application point and the physical
neighbor there. The boundary replacement below does not change the
stress or any hypothesis of that local estimate.

## 2. Geometry of an SS pair with inner support edges

Rotate and, if necessary, reflect so the common supporting line is
`x=z`, with the first square on its left and the second on its right.
Both are parallel to these coordinate axes. By Section 1, choose circle
vertices on their opposite vertical edges. The horizontal coordinates
of these vertices are therefore `z-1` and `z+1`.

Each selected circle vertex is at least as far from the origin as its
partner vertex across the same horizontal side. For the left square
this gives `(z-1)^2>=z^2`, hence `z<=1/2`. For the right square it gives
`(z+1)^2>=z^2`, hence `z>=-1/2`. Thus

```text
-1/2<=z<=1/2.                                         (1)
```

Let the vertical coordinates of the two selected circle vertices be
`epsilon_L*Y_L` and `epsilon_R*Y_R`, where Y_L,Y_R>0 and the signs are
in `{+1,-1}`. Then

```text
Y_L^2=R^2-(z-1)^2 >=6241/1600-9/4=2641/1600>1,
Y_R^2=R^2-(z+1)^2 >=6241/1600-9/4>1.                  (2)
```

Consequently Y_L,Y_R>1. If the signs differed, the two squares' vertical
intervals would lie strictly in opposite open half-planes y>0 and y<0.
They could not touch. Thus the signs agree. Reflect vertically so both
are positive. The squares are

```text
C_L=[z-1,z] x [Y_L-1,Y_L],
C_R=[z,z+1] x [Y_R-1,Y_R].                             (3)
```

Their chosen core corners are the lower endpoints of the common support
edges:

```text
A_L=(z,Y_L-1),       A_R=(z,Y_R-1).                    (4)
```

The common edge intersection is a nonempty segment, possibly a single
point. Its lower endpoint is

```text
Q=(z,max(Y_L-1,Y_R-1)).                               (5)
```

In particular Q is one of the two core corners. The triangle
`conv{A_L,Q,A_R}` is degenerate and belongs to their line segment.

Moreover, the portions of the two inner body paths from their respective
core corners to Q meet only at Q: whichever path is nontrivial lies
strictly below the other square's bottom edge, apart from Q. Thus this
choice removes the backtracking that might occur if one joined both
core corners to an arbitrary force application point higher on the
shared segment.

## 3. Replacing only the boundary contact, not the force witness

At every SS pair use the point Q from (5) in the geometric boundary
construction. At every proper SV/VS pair use its original contact point.
Denote the resulting chosen points by q_i. All q_i remain actual points
of intersection of their two loaded squares. No force is moved or
reassigned.

The physical ring theorem puts every point shared by two consecutive
loaded squares strictly between their center rays. Hence the polygon
through successive centers and q_i is still a Jordan curve with winding
number one about zero. The two chosen contacts on each body are distinct:
if they coincided, its two ring neighbors would touch each other, which
the loaded-ring separation theorem forbids.

Join q_(i-1) to q_i through the chosen core corner A_i along the inner
body boundary. At a proper pair the neighboring paths meet only at the
single intersection point. At an SS pair this is the last assertion
of Section 2. Nonneighbor body paths cannot meet at all. Thus, after
removing zero-length segments, these paths form a simple closed polygon.
Replacing center paths by body boundary paths preserves winding number
about zero, since every loaded body avoids the closed half-radius disk.
The same connected-interior argument as in the radial capacity theorem
puts all three inner squares in its bounded region.

As oriented chains the boundary identity is

```text
boundary(hole)
 = (A_0 A_1 ... A_6 A_0)
   + sum_i boundary(conv{A_i,q_i,A_(i+1)}).            (6)
```

Every proper-contact summand is a counterclockwise triangle or is
degenerate as in the radial theorem. Every SS summand is zero, with
q_i equal to one of its two core corners. Therefore the winding-number
argument still places every hole point outside the core convex hull in
one of the nondegenerate proper-contact triangles.

## 4. Capacity and remaining support defects

The core hull has squared radius below `36/25`. Every inner-square vertex
in a remaining proper-contact triangle has squared norm below `83/50`
by the reviewed cap and diameter-cut arguments. Hence all three inner
squares lie in that latter disk, contradicting

```text
425/256-83/50=1/6400>0.
```

This proves the theorem.

Combining it with the incident mixed exclusion, a still-possible loaded
seven-ring must therefore have at least one of the following:

* a unique-circle row U4,U5,U8,U9;
* a strict VV pair contact.

A ring with no VV pair and no weak opposite-corner row is excluded even
if it has SS pairs and radial-side bodies. No full C04 closure is claimed.
