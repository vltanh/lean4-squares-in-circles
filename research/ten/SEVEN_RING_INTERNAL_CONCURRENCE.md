# Loaded-ring forces concur inside their own squares

Use an entirely circle-loaded physical ring in the window
`79/40<=R<=3/sqrt(2)`, with the notation and original contact points of
[SEVEN_RING_FORCE_ORIGIN.md](SEVEN_RING_FORCE_ORIGIN.md).
That theorem proves that the two contact-force lines of each body meet at
a positive point on its circle-load resultant ray.

**Theorem.** Each body's concurrence point belongs to its **closed** square.
No strict-interior conclusion is asserted. The actual contact points, in
cyclic order, form the vertices of a convex polygon containing the three
remaining unit squares in a subcritical ten-square packing.

Sections 4--5 handle a unique geometric circle vertex. Sections 6--7
handle a radial-side square with two geometric circle vertices, allowing
any nonnegative load split between them. These exhaust loaded squares
in the stated radius window.

## 1. No two packed squares share a point of the containing circle

Suppose a point w with |w|=R belonged to two squares. It must be a vertex
of each: an interior point of a nontrivial line segment contained in a
strictly convex disk cannot lie on that disk's boundary.
For either square, each incident unit edge e from w obeys

```
|w+e|^2<=R^2,          so          w dot e<=-1/2<0.
```

Thus its whole closed angular sector of width pi/2 lies strictly inside
the open inward radial semicircle. The two squares' open sectors are
disjoint, by interior disjointness. But two closed sectors of total angle
pi cannot fit with disjoint interiors inside an open semicircle of angle
pi: their four endpoints have a positive minimum angular distance from
its two boundary rays. This contradiction proves the claim.

## 2. A supporting normal pointing away from an external point

Let K be any closed convex square, p a boundary point, and F an inward
supporting normal there. If

```
p-X=t F,          t>0,
```

then p is the unique point of K nearest X. Indeed, for every z in K,

```
|z-X|^2=|p-X|^2+|z-p|^2+2t F dot(z-p)>=|p-X|^2,
```

with equality only when z=p.

We call this an inward force pointing away from X. Conversely, if a
force line passes through X and its application point is distinct from
X, the force points either toward or away from X.

## 3. A left-supported neighbor estimate

Let P=(A,Y), with A>0 and 0<=Y<=A. A unit square K lying in x<=A and
containing P has every vertex z bounded by

```
|z|^2 <= max(A^2,(A-1)^2)+(Y+1)^2.                      (1)
```

If P is a vertex, write the two incident edges, after choosing which one
points upward, as `(-c,s)` and `(-s,-c)`, where c,s>=0 and c^2+s^2=1.
The other ordering is obtained by reflecting vertically. Either adjacent
vertex has squared norm at most `A^2+(Y+1)^2`. For the opposite vertex,
the larger of the two vertical-reflection expressions is

```
A^2+Y^2+2-2A(c+s)+2Y|c-s|
 <= A^2+Y^2+2-2(A-Y)
  = (A-1)^2+(Y+1)^2.
```

Here `A(c+s)-Y|c-s|>=(A-Y)(c+s)>=A-Y`. These estimates prove (1).
If P is in a side interior, that side is vertical and K is axis-parallel.
Its vertices have horizontal coordinates A or A-1 and absolute vertical
coordinate at most Y+1, giving (1) directly.

## 4. The concurrence cannot lie before the square on its positive ray

Use the body's own axes, reflected and interchanged so its center is
`(a,b)`, with a>=b>0. The strict inequality b>0 follows from the unique
circle-vertex hypothesis. Write

```
A=a-1/2,       h=b+1/2,       w=(A+1,h),
C=[A,A+1] x [h-1,h],
R^2=(A+1)^2+h^2,       h<=A+1.
```

The radius window ensures

```
A>=R/sqrt(2)-1>153/400>3/8,                            (2)
```

using `sqrt(2)<10/7` and R>=79/40.
Write the concurrence as X=k w, k>0. The ray first enters C at

```
k_entry=A/(A+1).
```

Indeed this is at least `(h-1)/h`, because h<=A+1.
Suppose 0<k<k_entry. Then X lies strictly outside C, to its left.
The circle force at w points toward X. The contact forces cannot both
point toward X as well: a strict separating linear functional between X
and the compact convex square is strictly decreasing along every such
force, contradicting their zero sum. At least one contact force therefore
points away from X. Section 2 makes its application point the unique
nearest point of C to X.

If X_y<h-1, that nearest point is the opposite corner `(A,h-1)`.
Both its coordinates are positive, since X_y>0. The
[inner-corner clearance lemma](LOADED_INNER_CORNER_CLEARANCE.md) says that
its physical neighbor is strictly circle-clear, contrary to the entirely
loaded hypothesis.

Otherwise the nearest point is P=(A,Y), with

```
Y=X_y=k h < A h/(A+1) <= A.
```

The contact normal on C points horizontally right, so the physical
neighbor lies in x<=A and contains P. Apply (1) and put z=h/(A+1), with
0<z<=1. Since Y<=Az, subtracting the upper bound from R^2 gives at least

```
2A(1-z)+(2A+1)z^2                         if A>=1/2,
4A-1-2Az+(2A+1)z^2                        if A<1/2.
```

The first expression is strictly positive. The second is at least

```
(7A^2+2A-1)/(2A+1)>0,
```

by completing the square and (2); its numerator already equals 47/64 at
A=3/8 and increases for positive A. Thus this neighbor also has every
vertex strictly inside the containing circle, a contradiction.

The concurrence cannot precede the square on its positive radial ray.

## 5. The concurrence cannot lie beyond the circle vertex

Suppose k>1. Both coordinates of X then strictly exceed the corresponding
coordinates of every point in C.

An inward contact force pointing away from X would, by Section 2, have
to act at the nearest point w of C to X. Section 1 forbids a physical
neighbor at that circle vertex. Thus both contact forces point toward X.
Each has both coordinate components strictly positive. The only boundary
point of C whose inward normal cone contains such a vector is its lower-
left corner `(A,h-1)`. Both contacts would have to use that same point.
But the physical ring theorem places the two contact rays strictly on
opposite sides of the body's center ray, so its two contact application
points are distinct. This is a contradiction.

Together with Section 4, this proves

```
A/(A+1) <= k <= 1,
```

which is exactly the asserted containment X in C along this ray.
The endpoint k=1 is deliberately retained.

## 6. Shallow corner normals on a radial-side body force circle clearance

For the remaining case write the radial-side square as

```
C=[A,A+1] x [-1/2,1/2],
R^2=(A+1)^2+1/4,
9/10<A<=sqrt(17)/2-1<3/2.
```

The bounds follow from the radius window. Suppose a neighbor K touches
its upper-left corner P=(A,1/2), with inward force on C in unit direction

```
(p,-q),        p>0,       0<=q<=p/2,       p^2+q^2=1.
```

Then K has every vertex strictly inside the containing circle.
To prove this, K is supported at P with inward normal n=(-p,q).
If P is a vertex of K, the first of its incident edges has angle theta
in `[beta-pi/2,beta]`, where beta is the angle of n; the other has angle
theta+pi/2. Since q/p<=1/2, the first possible incident-edge direction is
v=(q,p), whose angle is greater than pi/4. The first-quadrant vector
P has angle less than pi/4. Maximizing its scalar product over the
permitted semicircle of edge directions therefore gives

```
P dot e <= Aq+p/2 <= (A+1)/sqrt(5)                     (5)
```

for either incident unit edge. The last expression follows by maximizing
`Aq+sqrt(1-q^2)/2` on `0<=q<=1/sqrt(5)`: its derivative is positive,
because A>9/10 while `q/(2p)<=1/4`.

For the opposite diagonal, the permitted direction interval is
`[beta-pi/4,beta+pi/4]`. The larger endpoint projection is that of n+v;
an interior stationary point can only be a minimum. Thus

```
P dot(e+f) <= (A+1/2)q-(A-1/2)p
            <= (3/4-A/2)p
            <= 3/4-A/2.                                (6)
```

Here q<=p/2, A>1/2, and A<3/2 justify the two inequalities.
An adjacent vertex consequently has squared norm at most

```
A^2+5/4+2(A+1)/sqrt(5) < R^2.                         (7)
```

For strictness use A>5/6 and sqrt(5)>11/5, which give
`A sqrt(5)>A+1`. The opposite vertex has squared norm at most

```
A^2+1/4+2+2(3/4-A/2)=A^2+15/4-A < R^2,               (8)
```

since the difference is `3A-5/2>0`. The contact vertex P is also
strictly inside.

If P is in a side interior of K, use tangent v=(q,p). Its vertices
have the form P+t v or P+n+t v with -1<=t<=1. Convexity in t reduces
their squared norms to the endpoints: P+-v obey (7), and P+n+-v obey
(8), by precisely the same scalar-product estimates. This proves the
clearance assertion for all contact types. Reflect vertically for the
corresponding lower-left-corner statement.

## 7. Two geometric circle vertices

Every loaded square in the window has center norm greater than 5/4, so
its center is nonzero. In its own frame, it has either one circle vertex
or exactly two; the latter occurs precisely when one center coordinate
is zero. Rotate to the radial-side coordinates of Section 6.

Its outward circle-load resultant is a positive multiple of

```
wbar=(A+1,ybar),        |ybar|<=1/2,
```

where ybar is the weighted mean of the two circle-vertex heights. This
allows one of the two weights to vanish. Write its concurrence as
X=k wbar, k>0.

Suppose first that X lies before the body on this ray, so
`k<A/(A+1)`. Then X_x<A and |X_y|<1/2. The separating-functional argument
of Section 4 applies to the resultant circle force as if applied at
wbar, which is in C: that resultant points toward X. Some contact force
points away from X, and its application point is consequently the
nearest point `(A,X_y)` on the inner face.
Its neighbor is supported in x<=A. The radial-side inner-face lemma in
[SEVEN_RING_FORCE_ORIGIN.md](SEVEN_RING_FORCE_ORIGIN.md), Section 3,
proves that such a neighbor is strictly circle-clear. This contradicts
its positive circle load.

Now suppose k>1, so X_x>A+1. A contact force pointing away from X would
act at its nearest point on C's outer face. If that point is a corner,
it lies on the containing circle and Section 1 forbids a neighbor there.
Otherwise a neighbor would be supported in x>=A+1. Its horizontal width
is at least one, so some point would have x>=A+2>R, impossible.
Thus both contact forces point toward X and have positive horizontal
component.

Their application points must therefore lie on the left face or its
corners. If |X_y|>1/2, only one of the two left corners has an inward
normal cone containing the direction toward X. Both contacts would
coincide, contradicting the physical ring. Hence |X_y|<=1/2.
A relative-interior left-face contact has horizontal normal and its
neighbor is again circle-clear by the cited inner-face lemma. The only
remaining possibility is one contact at each left corner. Their inward
normal slopes have magnitudes

```
rho_top=(1/2-X_y)/(X_x-A),
rho_bottom=(1/2+X_y)/(X_x-A),
rho_top+rho_bottom=1/(X_x-A)<1.
```

At least one slope is strictly less than 1/2. The shallow-corner lemma
of Section 6 makes that neighbor circle-clear as well, a contradiction.
This excludes k>1. We have therefore proved

```
A/(A+1)<=k<=1,
```

which places X in the closed radial-side square. Together with Sections
4--5, the concurrence theorem now covers every loaded ring body.

## 8. A convex polygon of physical contact points

Now apply the theorem to every loaded body. Let X_i be its
concurrence, and let p_i and f_i be the actual contact point and positive
force vector from body i toward body i+1. The preceding theorem gives
X_i in body i. Since each force line passes through both corresponding
concurrences,

```
p_i-X_i = s_i f_i,
X_(i+1)-p_i = t_i f_i,       s_i,t_i>=0.                  (3)
```

The nonnegative signs follow by projecting the points inside their own
squares onto the outward/inward supporting normal f_i.

Here is a useful exact description of the concurrence polygon. Let J be
counterclockwise rotation by pi/2 and let tau>0 be the common origin
torque. The strictly convex force polygon contains zero in its interior.
Its polar, scaled by tau and rotated back by J, is

```
Q={x: x cross f_i<=tau for every i}.                    (4)
```

The intersection of the two consecutive boundary lines belonging to
f_(i-1),f_i is precisely X_i. Thus Q is a bounded convex polygon with
vertices X_i in the same cyclic order, and zero in its strict interior.
One can see this without invoking polarity terminology: after applying J,
(4) is the intersection of the supporting inequalities
`(Jx) dot f_i<=tau`; every vertex f_i of the strictly convex force polygon
produces one nonredundant edge. Consecutive edges meet at the displayed
line intersections.

Strict convexity of the force polygon makes consecutive X_i distinct:
otherwise three successive force vertices would lie on one affine line
`X cross f=tau`. Equation (3) therefore places each p_i on the edge
[X_i,X_(i+1)], allowing p_i to coincide with one endpoint.

Let H=conv{p_i}. These points occur in cyclic order on the boundary of Q,
so their cyclic joins give a convex polygon, possibly with redundant
collinear vertices. Cutting each corner off Q along the chord
[p_(i-1),p_i] removes precisely the triangle

```
conv{X_i,p_(i-1),p_i}.
```

This triangle lies inside body i by convexity. Thus every piece of Q
outside H belongs to a loaded body. Also each chord [p_(i-1),p_i] lies
inside that same body. All these statements retain the original contact
points, including any endpoint coincidences in (3).

Every loaded body avoids the closed disk B(0,1/2), as proved in
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md). The
boundary of Q lies in the loaded bodies by (3), while Q contains zero.
Hence the entire half-radius disk lies inside Q. The removed corner
triangles cannot meet this disk, so it lies inside H as well.

In a subcritical ten-square packing the other three centers have norm
less than one. Each of their open inscribed half-radius disks meets
B(0,1/2), so its square's interior meets the interior of H. Its interior
cannot cross the boundary of H, whose edges lie in the loaded bodies.
Connectedness then puts the entire additional square in H, by taking
closures. Therefore H contains all three remaining unit squares.

The polygon H need not equal the actual free hole; it is a convex enclosure
of that hole sufficient for further containment bounds. No area or
circumradius bound strong enough to exclude three squares is asserted here.
