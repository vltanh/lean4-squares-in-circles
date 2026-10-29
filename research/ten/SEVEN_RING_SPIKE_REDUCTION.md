# Inner-corner disk and a local spike problem for loaded rings

**Status:** Sections 1–3 and 5 have independent mathematical reviews
(2026-10-29). The inner-corner bound, polygon reduction, and diameter-disk
cut are proved.
The final local inequality is an **unproved research target**. This note does
not exclude a nonuniform ring or establish the unrestricted n=10 bound.

Use the radius window and the physical loaded seven-ring of
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md). Section 1
applies to every loaded square. Sections 2--4 additionally assume the
one-chirality contact pattern of
[SEVEN_RING_ONE_CHIRALITY.md](SEVEN_RING_ONE_CHIRALITY.md).

## 1. All opposite corners lie in a disk of radius less than 6/5

Choose a loaded square's own orthonormal coordinates so its center is
`(a,b)`, with `a,b>=0`, and its farthest circle vertex is
`w=(a+1/2,b+1/2)`. Put `q=R^2`. Its opposite corner is
`A=(a-1/2,b-1/2)`, so

```
q=a^2+b^2+a+b+1/2,
|A|^2=q-2(a+b).
```

Writing `s=a+b` and using `ab>=0` gives

```
q=s^2-2ab+s+1/2 <= s^2+s+1/2,
s >= sqrt(q-1/4)-1/2.
```

Consequently

```
|A|^2 <= q+1-2sqrt(q-1/4).                         (1)
```

The right side increases for `q>5/4`, since its derivative is
`1-1/sqrt(q-1/4)>0`. In the working window `q<=9/2`, this proves

```
|A|^2 <= 11/2-sqrt(17) < 36/25.                    (2)
```

For the last strict inequality, `sqrt(17)>203/50` follows by squaring:
`17*2500-203^2=1291>0`. Equality in the first inequality of (2) requires
`q=9/2` and `ab=0`; these are precisely radial-side squares at the upper
radius. The bound allows either choice of the opposite corner when the
square has two farthest circle vertices.

This bounds the opposite corner, not every contact point or every point
of the free hole.

## 2. Outside that disk, the one-chirality hole consists of contact spikes

Retain the positively oriented frames `(u_i,v_i)`, the unique loaded
circle vertices `w_i`, and the physical contacts from the one-chirality
note:

```
p_(i-1)=w_i-u_i,
p_i=w_i-lambda_i u_i+v_i,      0<lambda_i<1,
0<delta_i=theta_i-theta_(i-1)<pi/2.
```

Define each opposite corner and remaining top-side length by

```
A_i=w_i-u_i+v_i,
t_i=1-lambda_i in (0,1).
```

The inner boundary follows the full unit side from `p_(i-1)` to `A_i`,
then the length-`t_i` side from `A_i` to `p_i`. It is the same physical
boundary construction as in
[REGULAR_SEVEN_LOADED_RING.md](REGULAR_SEVEN_LOADED_RING.md), Section 3;
no uniformity is needed for this construction. Nonneighbor loaded bodies
cannot touch, neighboring side/vertex contacts are single points, and the
paths on each body are simple. Thus the resulting polygon is simple.
Replacing the center/contact Jordan ring by these inner paths through the
squares preserves winding number about zero, because all loaded bodies
avoid the closed half-radius disk. The positively oriented polygon bounds
the central free hole, denoted `Omega`.

For each contact put

```
T_i=conv{A_i,p_i,A_(i+1)}.
```

These are nondegenerate counterclockwise triangles. Indeed,

```
p_i-A_i=t_i u_i,
A_(i+1)-p_i=v_(i+1),
(p_i-A_i) cross (A_(i+1)-A_i)=t_i cos(delta_(i+1))>0.
```

Let `rho^2=11/2-sqrt(17)`. Then

```
Omega \ D_rho  is contained in  union_i T_i.         (3)
```

Here is a proof that does not assume that the hole is star-shaped or that
the polygon through the `A_i` is convex. As oriented polygonal chains,

```
boundary(Omega)
 = (A_0 A_1 ... A_6 A_0) + sum_i boundary(T_i).
```

This is immediate by cancelling each chord `[A_i,A_(i+1)]`. For a point
outside the convex hull of the `A_i`, the first polygon has winding number
zero: a separating line puts its whole chain in a half-plane avoiding the
point. A point of `Omega` has winding number one, whereas each triangle
has winding number zero or one. Thus such a point lies in at least one
triangle. Every `A_i` lies in `D_rho` by (2), so the argument applies to
all points of `Omega` outside that disk. Boundary points follow by closure
and the finite union of closed triangles. This proves (3).

In particular, a vertex of any of the three inner unit squares that lies
outside `D_rho` must lie in one of these explicit triangles. The square
remains disjoint in interior from both loaded bodies that define that
triangle, and its center has norm less than one.

## 3. A six-variable local formulation

The remaining question can now be stated without the other five loaded
squares. Rotate so the first frame has `u=(1,0)`, `v=(0,1)`. Write

```
w=R(cos(a),-sin(a)),
u'=(cos(d),sin(d)),       v'=(-sin(d),cos(d)),
w'=R(cos(b)u'-sin(b)v'),
P=w'-u'=w-lambda*u+v,
A=w-u+v,                 B=P+v'.
```

The two loaded squares are

```
C=w+[-1,0]u+[0,1]v,
C'=P+[0,1]u'+[0,1]v'.
```

Require `0<d<pi/2`, `0<lambda<1`, and all four farthest-vertex sign
conditions

```
R cos(a)>1/2, R sin(a)>1/2,
R cos(b)>1/2, R sin(b)>1/2,
k=R cos(d-b)-cos(d)>0.
```

The positive branch in
[SEVEN_RING_ANGLE_ACTION.md](SEVEN_RING_ANGLE_ACTION.md), Section 1,
expresses `d` in terms of `(a,b,R)`; matching the first coordinate then
determines `lambda`. A third unit square is specified by its two center
coordinates and its angle. This gives six scalar parameters in total.
The third square must have center norm below one, be interior-disjoint
from `C,C'`, and have the vertex under consideration in `conv{A,P,B}`.
These are necessary conditions for an inner-square vertex in a ring spike.
The third square is automatically contained in `D_R`: its center norm is
below one and every vertex is at distance `1/sqrt(2)` from that center,
so its vertex norms are below `1+1/sqrt(2)<79/40<=R`. They do not impose
the rest of the ring or its positive stress equations.

## 4. Unproved local target and an exact limiting witness

A local inequality suggested by numerical exploration is

```
|z|^2 <= R^2-sqrt(2R^2-1)                           (4)
```

for a vertex `z` of the third square under all the conditions of Section 3.
**No proof of (4) is supplied here.** Numerical optimization is not used as
a premise of Sections 1--3.

At `R^2=9/2`, its proposed upper bound is

```
9/2-2sqrt(2) < 1+1/sqrt(2),
```

because the strict comparison is equivalent to `7<5sqrt(2)` and hence
`49<50`. Were (4) proved, (2)--(3) would place every vertex of each inner
square inside the test disk of radius `sqrt(1+1/sqrt(2))`. Convexity would
place the whole squares there. This would discharge the no-protrusion
hypothesis of
[THREE_CORE_INNER_STABILITY.md](THREE_CORE_INNER_STABILITY.md) for this
contact pattern; it would not by itself complete that remaining three-core
argument or classify all loaded rings.

The proposed bound has an exact witness at the boundary of the contact
pattern. Put `h=sqrt(2)-1/2` and `z=(h,-h)`. Take the three axis-parallel
unit squares

```
C =[h-1,h]   x [-h-1,-h],
C'=[h,h+1]   x [-h,-h+1],
K =[h-1,h]   x [-h,-h+1].
```

Their interiors are disjoint. The two outer squares have farthest vertices
`z-(0,1)` and `z+(1,0)`, respectively, with squared norms
`h^2+(h+1)^2=9/2`. The center of `K` is
`(sqrt(2)-1,-sqrt(2)+1)`, of squared norm `6-4sqrt(2)<1`, and

```
|z|^2=2h^2=9/2-2sqrt(2).
```

This is the limit `d=0`, `lambda=0`; it is not a stressed seven-ring
because the strict acute-turn and side-interior hypotheses fail. It only
shows why the constant in the candidate local inequality is natural.

## 5. A proved cut: every admissible vertex lies in the diameter disk

The local problem has a useful exact relaxation. In the notation of
Section 3, every vertex `z` of an interior-disjoint third unit square that
lies in `T=conv{A,P,B}` satisfies

```
(A-z) dot (B-z) <= 0.                               (5)
```

Equivalently, `z` belongs to the closed disk with diameter `[A,B]`.
This assertion uses only the two loaded bodies' unit side geometry and
interior disjointness. No circle containment or center bound is needed
for this step.

Translate `P` to zero for the proof. Put `t=1-lambda`, `s=sin(d)` and
`c=cos(d)`. Thus

```
A=(-t,0), B=(-s,c),
0<t<1, 0<s<1, c>0, s^2+c^2=1,
|A|=t<1, |B|=1, A dot B=t*s>0.
```

The side `[A,P]` belongs to the first unit square, whose interior is
immediately below it. The side `[P,B]` belongs to the second unit square,
whose interior is immediately to its other side. The relative interior
of the triangle is on the unoccupied side of both these segments.

Suppose for a contradiction that a vertex `z` of the third unit square
lies in `T` and has

```
D(z)=(A-z) dot (B-z)>0.
```

We first show that every point of `T` is at distance strictly less than
one from `z`, except for an irrelevant possible endpoint when `z=P`.
The point `P` cannot belong to the third square at all. Near `P`, the
first body's side-interior contact leaves only its upper half-plane free,
and the second body's vertex sector divides that half-plane into two free
sectors, of angles `d` and `pi/2-d`. Both are strictly below `pi/2`.
Neither can contain the connected local interior sector of a square at
`P`: that sector has angle `pi/2` at a
vertex, `pi` at a side-interior point, and `2pi` at an interior point.
Thus, in particular, `z!=P`.

The ray from `A` through `z` meets the opposite side `[P,B]` at `q=rB`,
with `0<=r<=1`. This is well defined since `D(z)>0` excludes `z=A` and
`z=B`. Along a ray `A+ell*e`, with unit direction `e`,

```
D(A+ell*e)=ell[ell-e dot (B-A)].
```

Once positive for `ell>0`, this stays positive at all larger `ell`.
Consequently `D(q)>0`. Since

```
D(rB)=(1-r)(A dot B-r),
```

we obtain `r<A dot B`. Hence

```
|q-A|^2=|A|^2+r^2-2r(A dot B)<=|A|^2=t^2<1.
```

As `z` lies between `A` and `q`, this proves `|z-A|<1`.
The same argument from `B` reaches a point `q'=r'A` on `[P,A]` and gives

```
D(r'A)=(1-r')(A dot B-r'|A|^2)>0,
|q'-B|^2=1+(r')^2|A|^2-2r'(A dot B)<=1.
```

If `r'>0`, the latter inequality is strict. If `r'=0`, then `q'=P`;
since `z!=P`, the point `z` lies strictly between `B` and `P`, and still
`|z-B|<1`. Finally, `|z-P|<1`: the triangle is the convex hull of two
points of norm strictly below one and the single unit-norm point `B`,
while `z!=B`. Convexity of the norm now places the entire triangle in the
open unit disk centered at `z`.

The third square's two unit edges starting at `z` therefore both leave
`T` before reaching their other endpoints. Neither can cross the relative
interior of `[A,P]` or `[P,B]`: that would enter the interior of one of
the two forbidden unit squares. If an edge lies along one of those sides, it can leave only through an
endpoint. The endpoint `P` is impossible by the preceding local-sector
argument; the other endpoints `A,B` lie on the base. Thus both edge
directions point into the closed cone from `z` through `[A,B]`.

But `D(z)>0` says that the angle between `A-z` and `B-z` is strictly less
than `pi/2`. Since `z` lies in the triangle and not on its base, this is
exactly the angle of that cone. It cannot contain two perpendicular unit
edge directions. This contradiction proves (5).

Thus the remaining analytic target can replace the third square by the
explicit necessary region

```
z in conv{A,P,B},        (A-z) dot (B-z)<=0.            (6)
```

It is essential to retain the triangle in (6): the full diameter disk can
extend far beyond the central free hole. The incoming-neighbor inequality
in [SEVEN_RING_FORCE_RATIO.md](SEVEN_RING_FORCE_RATIO.md) supplies further
physical restrictions, in particular `R cos(a)>1` and `R cos(b)>1` for
a complete one-chirality loaded ring. Bounding the farthest norm in (6)
under those restrictions remains an open analytic step here.
