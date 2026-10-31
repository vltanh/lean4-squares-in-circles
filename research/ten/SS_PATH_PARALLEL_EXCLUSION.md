# Parallel transmissions with a width-two path are impossible

**Status:** independently reviewed exact conditional hand proof (2026-10-29).
This extends the parallel-direction reduction to the two remaining
three-loaded six-cycle words `LLSLSS` and `LLDLSS`. It does not by itself
close either whole signature.

Use the selected physical stress certificate in a ten-square packing with
`79/40<=R<=3/sqrt(2)`. Let the whole positive component consist of three
loaded bodies A,B,C, a direct A--B edge, and two unloaded degree-two paths
from C to A and B. One path is SS, of width two; the other has width one
or `sqrt(2)`. Suppose their outgoing directions at C are parallel.

**Theorem.** This configuration is impossible.

## 1. The central body is radial side type

If the directions are opposite, the endpoint squares lie beyond opposite
support faces of C, with additional gaps of at least one. Their
projections along that direction are separated by at least three, so
A and B cannot touch.

Otherwise rotate so both directions point right. Aggregate the two
positive forces on C at their positively weighted mean contact point.
The circle forces have zero torque about the origin, so the aggregate
force line is radial. The loaded-leaf classification used in
[PARALLEL_MIXED_FIVE_CYCLE.md](PARALLEL_MIXED_FIVE_CYCLE.md), Section 2,
applies without any restriction on the path lengths: C is radial side
type or radial diagonal type.

Radial diagonal type is impossible. Its right support consists of one
vertex P. The first body of the SS path is a side transmitter with
horizontal normal. If P were in the relative interior of its side, its
local open half-plane would overlap the first transmitter of the other
path, whose outgoing direction is also right. Thus P must be a vertex
of that side transmitter. C and it then have a point-only vertex/vertex
contact, but the selected horizontal normal is a side normal of the
transmitter. This violates the strict normal convention at such contacts,
as stated in
[COMMON_CORNER_MIXED_TRANSMISSIONS.md](COMMON_CORNER_MIXED_TRANSMISSIONS.md),
Section 1.

Consequently, with

```text
L=sqrt(R^2-1/4)-1,
C=[-L-1,-L] x [-1/2,1/2],
R^2=(L+1)^2+1/4,
```

both path contacts have the form `(-L,h)`, with `|h|<=1/2`.

## 2. The width-two endpoint forces L>=1

The endpoint square of the SS path lies in the half-plane `x>=2-L`.
The [cap theorem](TRANSMISSION_CAP_ANGLE_BOUND.md), Section 1, implies
that its cap offset satisfies

```text
sqrt(R^2-(3-L)^2)-1/2 >= 0,
R^2 >= (3-L)^2+1/4.
```

The theorem applies because `2-L>0` in the radius window. Subtracting
from `R^2=(L+1)^2+1/4` gives `8(L-1)>=0`. Thus

```text
1<=L<17/16,          R^2>=17/4>4.                    (1)
```

This inference needs only containment of the SS endpoint, not its load.

## 3. A width-one parallel endpoint cannot be loaded

If the other path has width one, its endpoint square contains the support
point

```text
Q=(1-L,h),           |h|<=1/2.
```

Equation (1) gives

```text
|Q|^2 < 1/256+1/4=65/256<81/256,
|Q|<9/16.
```

Every point of a unit square containing Q is within `sqrt(2)<23/16`
of Q. Hence all its vertices have norm below two, whereas (1) gives
`R>2`. This endpoint cannot have positive circle load, a contradiction.

## 4. A diagonal parallel endpoint cannot be loaded either

The other path is now a single diagonal transmitter, and its endpoint
square K is supported at

```text
Q=(x,h),       x=sqrt(2)-L,       |h|<=1/2,
```

with inward horizontal normal. By (1),

```text
0<x<=sqrt(2)-1<1/2.
```

We claim every vertex of K has squared norm at most `17/4`.

First suppose Q is a vertex. Both incident edges have nonnegative
horizontal components. The displacement to the opposite vertex is
`(w,d)`, where

```text
1<=w<=sqrt(2),       |d|<=1,       w^2+d^2=2.
```

Its squared norm is at most

```text
x^2+9/4+2xw+sqrt(2-w^2).
```

The function `2xw+sqrt(2-w^2)` is strictly decreasing for
`1<=w<sqrt(2)`: its derivative is

```text
2x-w/sqrt(2-w^2) <= 2(sqrt(2)-1)-1 < 0.
```

Its maximum is therefore `2x+1`, at w=1. Thus the opposite vertex has
squared norm at most

```text
(x+1)^2+9/4 <= 2+9/4=17/4.                           (2)
```

For Q and either adjacent vertex, `|Q|<sqrt(1/2)<3/4` gives vertex
norm below `7/4<R`; they cannot be circle vertices.

If Q is in a relative side interior, the horizontal support normal fixes
K to be axis-parallel. All its points have horizontal coordinate between
x and x+1, and vertical absolute coordinate at most `|h|+1<=3/2`.
The same estimate (2) follows.

If `L>1`, then `R^2>17/4`, so K is circle-clear. The only possible
loading equality has

```text
L=1,       R^2=17/4,       |h|=1/2.                  (3)
```

But then the diagonal transmitter starts at a corner of C, with horizontal
transmission direction. Its contact with C is point-only vertex/vertex:
the diamond lies on the right of the support line and C on the left,
with only that corner shared. The horizontal normal is a side normal of
C, again forbidden by the selected strict-normal convention. This
excludes (3) too.

Both possible types of the other path are excluded. Therefore parallel
directions cannot occur in either of the two indicated six-cycle words.
