# A radial-side central body cannot join SS and S paths

**Status:** exact conditional hand proof; two independent full mathematical
reviews passed on 2026-10-29.
This treats the remaining radial-side central case of the three-loaded
six-cycle `LLSLSS`. The force triangle and its orientation are proved
below rather than imported from an entirely loaded ring.

Let the whole positive component have three loaded bodies A,B,C, a direct
A--B edge, an SS path from C to A, and a single S transmitter from C to B.
Suppose C has two circle vertices. Work in `79/40<=R<=3/sqrt(2)` with
the physical positive stress and the usual selected contact normals.

**Theorem.** This configuration is impossible.

## 1. Central contacts and the width-one endpoint

Rotate so

```text
C=[L,L+1] x [-1/2,1/2],
R^2=(L+1)^2+1/4.
```

Sections 1--2 of
[SS_PATH_RADIAL_SIDE_DIAGONAL_EXCLUSION.md](SS_PATH_RADIAL_SIDE_DIAGONAL_EXCLUSION.md)
use only the existence of the SS path. After reflecting horizontally,
they give

```text
1<=L<17/16,             R^2>=17/4>4,                 (1)
```

and both path contacts on C lie on its left side, including its corners.

The S path cannot start in the relative interior of that side, or use
a horizontal outgoing normal at a corner. Its far endpoint contact
would be `(L-1,h)`, with `|h|<=1/2`, whose norm is below `9/16` by
(1). Every vertex of the endpoint square is within `sqrt(2)<23/16`
of that contact, hence has norm below two, contrary to its positive
circle load and R>2.

Thus the S path starts at a corner with a strictly nonhorizontal outgoing
direction. At an upper-left contact the outgoing normal is `(-p,q)`
and its origin torque is a positive multiple of `Lq+p/2>0`. At a lower-left
contact it is `(-p,-q)` and its torque is negative. At a side-interior
contact `(L,h)`, the outgoing normal is `(-1,0)` and its torque has
the sign of h. Circle forces have zero origin torque.

Consequently the two contacts lie on opposite halves of the left side.
Reflect vertically so the SS contact is above zero and the S contact
is the lower-left corner. Write the S direction as `(-p,-q)`, with
`p,q>=0`, `p^2+q^2=1`, and q>0. The
[strengthened endpoint height theorem](RADIAL_SIDE_S_HEIGHT_BOUND.md)
puts its loaded endpoint B wholly in

```text
y<-1/2.                                               (2)
```

## 2. A corner-starting SS path is already impossible

If the SS contact is the upper-left corner, write its direction as
`(-u,v)`, with u,v nonnegative and `u^2+v^2=1`. Its far contact on A
is `(L-2u,1/2+2v)`. A unit square supported there by the inward normal
`(-u,v)` extends downward by at most u. This is the elementary one-sided
support estimate: at a supported vertex only one incident edge can point
down, with downward component at most u; at a supported side its unit
tangent gives the same bound and inward normal translation raises height.
Thus every point of A has

```text
y>=1/2+2v-u>=-1/2.
```

This separates A from B by (2), contradicting their contact. Therefore
the SS contact must be a side-interior point

```text
P=(L,h),             0<h<1/2,
```

with outgoing normal `(-1,0)`. Its endpoint contact on A is

```text
Q=(L-2,h).                                             (3)
```

If A has no point below `-1/2`, it again cannot touch B. For the rest
of the proof assume A has a point with height below `-1/2`.

## 3. Every circle vertex of this SS endpoint lies below zero

Reflect the horizontal coordinate temporarily, so A is supported at

```text
Q'=(a,h),       a=2-L>0,
```

with inward horizontal normal. Every point of A has height greater
than -1, since its downward extent from Q' is at most one and h>0.

Suppose first that Q' is a vertex. Its two unit edges have the form

```text
(c,s), (s,-c),       c,s>=0,       c^2+s^2=1.
```

Both horizontal components are nonnegative because the support normal
is horizontal. The horizontal width is w=c+s. Containment and the
minimum horizontal coordinate a give

```text
w<=R-a=R+L-2<19/16<6/5,                              (4)
```

using `R<17/8` and `L<17/16`. At least one of c,s is less than 1/4.
Indeed, if both were at least 1/4, then

```text
c+s >= (sqrt(15)+1)/4 > 6/5,
```

because `sqrt(15)>19/5`, contradicting (4).

The assumption that A reaches below `-1/2` says `h-c<-1/2`, so c>1/2
and therefore s<1/4. Let

```text
T=Q'+(c,s),          F=Q'+(c+s,s-c).
```

The lower adjacent vertex `Q'+(s,-c)` has negative height, and

```text
F_y=h+s-c<s-1/2<0.
```

The two vertices with positive height are strictly dominated in norm
by F:

```text
|F|^2-|T|^2=1+2as-2hc>1-c>=0,
|F|^2-|Q'|^2=2+2a(c+s)+2h(s-c)>2-c>0.
```

Thus neither Q' nor T can lie on the containing circle. Every circle
vertex of A lies below zero.

If Q' is in a relative side interior, A is axis-parallel. Its horizontal
coordinates are positive. Its vertical interval contains h>0 and has
lower endpoint below `-1/2`; since that interval has length one, its
center height is negative. Its circle vertices therefore all have
negative height too.

Return to the original horizontal coordinate. All points of A have
negative x coordinate, and its circle vertices satisfy

```text
x<0,       -1<y<0,       x^2+y^2=R^2,       R>2.
```

Their polar angles, and hence that of their positive weighted circle-load
resultant `g_A`, lie strictly in

```text
pi < arg(g_A) < 7pi/6.                                (5)
```

## 4. The three circle resultants have the cycle's counterclockwise order

Write `g_C,g_A,g_B` for the outward circle-load resultants, each a nonzero
positive weighted sum of its body's circle vertices. Summing the component
force equations gives

```text
g_C+g_A+g_B=0.                                         (6)
```

The two circle vertices of C are `(L+1,+-1/2)`. Therefore its resultant
has an angle `theta_C` in `(-pi/6,pi/6)`.

The S endpoint contact on B is `(L-p,-1/2-q)`. Its first coordinate
is nonnegative by L>=1. Every point of B is within `sqrt(2)` of that
contact, so every B circle vertex has x coordinate at least `-sqrt(2)`.
By (2) its y coordinate is negative, and by R>2 its polar angle is
strictly greater than `5pi/4`. Thus

```text
5pi/4 < theta_B:=arg(g_B) < 2pi,
pi < theta_A:=arg(g_A) < 7pi/6.                        (7)
```

These angles place the resultants in strict cyclic order C,A,B. The only
potential ambiguity would be `theta_B>=theta_C+2pi` when theta_C<0.
In that case all three resultants would lie in the angle interval
`[theta_A,theta_B]`, of length strictly less than pi, contradicting (6).
Hence

```text
theta_C<theta_A<theta_B<theta_C+2pi.
```

No successive gap can be at least pi, since that would again put all
three nonzero resultants in a closed semicircle with one strictly inside,
contradicting (6). Their directions consequently make one strictly
counterclockwise circuit, with all three gaps in `(0,pi)`.

## 5. The force triangle contains the origin strictly

Orient the component as `C -> SS -> A -> B -> S -> C`. Let
`f_0,f_1,f_2` be its circulating force vectors on the SS path, direct
A--B edge, and S path respectively. They are nonzero. Body balance gives

```text
f_2-f_0=g_C,       f_0-f_1=g_A,       f_1-f_2=g_B.
```

Section 4 implies that the triangle with vertices `f_0,f_1,f_2` is
strictly convex and counterclockwise: its successive edge vectors are
`-g_A,-g_B,-g_C`, in that order.

Torque balance gives one constant cross product at every original
contact along the cycle. At P the SS force is `f_0=(-mu,0)`, with mu>0,
so that constant is

```text
tau=P cross f_0=mu*h>0.                               (8)
```

We check the hypotheses of the nearest-point argument in
[SEVEN_RING_FORCE_ORIGIN.md](SEVEN_RING_FORCE_ORIGIN.md), Sections 1--2.
Every loaded square lies strictly on the positive side of its own
resultant: `g_i dot x>0` for every point x in it. The cited proof uses
only the local center/load-angle estimates and therefore applies here.

The two original contact points on each of A and B are distinct. If they
coincided, aggregation at their common point and the local loaded-leaf
classification would make that body radial side or radial diagonal type.
A radial side body's inward support face cannot touch a loaded neighbor,
by Section 3 of the cited force-origin note. A radial diagonal body's
inward vertex has norm `R-sqrt(2)`. Any unit square containing that vertex
has every vertex of norm at most R; equality in the triangle inequality
is possible only at the radial body's own outer circle vertex. Two
interior-disjoint squares cannot share that circle point, so that neighbor
cannot be loaded either. Both A and B have a direct loaded neighbor,
which is a contradiction. C's contact points are already distinct:
one is at height h>0, the other at height `-1/2`.

Suppose zero lies outside the force triangle and take its nearest point.
At a nearest force vertex, the source's support-chain contradiction
applies to the direct edge. At either transmission force vertex, its
support chain is strictly stronger. If the path has direction f and
endpoint contacts q,r in cyclic order, with adjacent loaded circle means
m,n, then

```text
f dot m <= f dot q < f dot r <= f dot n,
f dot(r-q)=|f|*W>0,
```

where W is one or two. Nearest-point inequalities require the leftmost
quantity to be nonnegative and the rightmost nonpositive, impossible.

At a nearest point in a force edge belonging to body i, the source's
calculation puts the concurrence of its two actual force lines at

```text
X=[tau/(g_i cross f_previous)]*g_i,
```

a negative multiple of `g_i`. Both contact applications would then be
the unique nearest point of the same convex square to X. Their
distinctness gives a contradiction. This proves origin containment.

If zero were on a force edge, its endpoint forces would be antiparallel.
The two inward forces on the corresponding body would point in the same
direction. Aggregation again makes it radial side or radial diagonal
type. For A or B, the direct loaded-neighbor argument just given rules
this out. For C, both outgoing paths would have the same direction as
the horizontal SS path; the S endpoint would be circle-clear by Section 1.
No force vertex is zero. Thus zero lies strictly inside the triangle.

## 6. Positive concurrence contradicts the SS force line

Strict origin containment and counterclockwise orientation imply

```text
g_A cross f_0>0.
```

Consequently the two physical force lines on A concur at

```text
X_A=[tau/(g_A cross f_0)]*g_A,
```

a strictly positive multiple of `g_A`. Equation (5) makes its vertical
coordinate negative. But its SS force line is exactly `y=h>0`, by (3).
This contradiction excludes the last possible radial-side configuration
and proves the theorem.
