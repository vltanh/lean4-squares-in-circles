# Eight centers outside the unit disk force four anchors

This strengthens [SHARP_EXTERIOR_RING.md](SHARP_EXTERIOR_RING.md). Unit squares
may have independent orientations. If eight of their centers have distance
at least `1` from the containing disk's center, and every square lies in the
disk of squared radius `9/2`, then four of the squares are the usual boundary
anchors. In particular, any hypothetical ten-square packing with squared
radius less than `9/2` must have at least three centers in the **open unit
disk**.

Use the constants and local coordinates

```text
Q = 9/2,
r = sqrt(1 + 1/sqrt(2)),
a = (sqrt(17)-1)/2,
u >= v >= 0,
A = u-1/2,    B = v-1/2,
U = u+1/2,    V = v+1/2.
```

Containment means `U^2+V^2<=9/2`. The new hypothesis is `u^2+v^2>=1`;
the square need not avoid the open disk of radius `1/2`.

## 1. Arc bound under the center condition

The square meets the circle `C_r` in a single arc of angle at least `pi/4`.
We retain the inner-edge inequality proved in Section 1 of
[SHARP_EXTERIOR_RING.md](SHARP_EXTERIOR_RING.md):

```text
asin(A/r)+asin(B/r) <= pi/4,
```

with equality exactly at `A=B=1/2`.

When `v<1/2`, the center condition gives `u>=sqrt(1-v^2)>sqrt(3)/2`.
Consequently `U>r`. One exact comparison is

```text
((1+sqrt(3))/2)^2 = 1+sqrt(3)/2 > 1+1/sqrt(2) = r^2.
```

The lower endpoint analysis from the exterior-square proof still applies:
`A<=3/sqrt(2)-1<r cos(pi/8)` and `B>=-1/2`. Therefore the arc is

```text
[asin(B/r), min(asin(V/r), acos(A/r))].
```

The same two endpoint arguments give angle at least `pi/4`, with equality
exactly at `v=0`, `1<=u<=a`.

When `v>=1/2`, the inequalities `A>=B>=0` and `A+B<=1` still hold. The
nearest corner has radius at most `1<r`, whereas the farthest corner has
squared radius

```text
u^2+v^2+u+v+1/2 >= 1+1+1/2 > r^2.
```

Thus the square meets `C_r` in a single first-quadrant arc. Opposite-edge
endpoints give angle strictly greater than `pi/4`. The two inward-edge
endpoints give angle at least `pi/4`, with equality exactly at `u=v=1`.

It remains to consider endpoints on both outward edges, `x=U` and `y=V`.
These require `U,V<=r`. Put

```text
alpha = asin(U/r),
beta  = asin(V/r).
```

The angular length is `alpha+beta-pi/2`. We claim
`alpha+beta>=3pi/4`. If the sum is at most `3pi/4`, increase the angles until
it equals `3pi/4`, while keeping each at most `pi/2`. This increases
`(r sin(alpha)-1/2)^2+(r sin(beta)-1/2)^2`, strictly if either angle changes.
Indeed `U,V>=1`, so both squared factors are positive and increasing.

On the line `alpha+beta=3pi/4`, write

```text
alpha = 3pi/8+t,
beta  = 3pi/8-t,
z = cos(t).
```

The upper angle bounds give `|t|<=pi/8`, so `0<z<=1`. Using
`r sin(3pi/8)=(1+sqrt(2))/2`, expansion gives

```text
(r sin(alpha)-1/2)^2 + (r sin(beta)-1/2)^2
  = 1+(1+sqrt(2))z(z-1) <= 1.
```

Therefore a strict inequality `alpha+beta<3pi/4` contradicts
`u^2+v^2>=1`. Equality in the arc bound requires `z=1` and hence

```text
u=v=1/sqrt(2).
```

This completes the arc bound.

## 2. A third equality type cannot occur in an eight-arc ring

There are now three equality types, specified by the polar angle `theta` of
their centers. Their arcs all have midpoint `theta` and angle `pi/4`.

* **S:** center `u e_theta`, `1<=u<=a`; one square edge is radial.
* **C:** center `sqrt(2) e_theta`; square edge directions are
  `theta-pi/4` and `theta+pi/4`.
* **D:** center `e_theta`; square edge directions are again
  `theta-pi/4` and `theta+pi/4`.

The S and C types are those from the exterior-square theorem. Type D is the
new outward-edge equality. In its own axes its coordinates range from
`(sqrt(2)-1)/2` to `(sqrt(2)+1)/2`, and its arc endpoints are

```text
((sqrt(2)+1)/2, 1/2), (1/2, (sqrt(2)+1)/2).
```

These endpoints lie strictly inside its outward sides. All equality arc
endpoints are therefore side-interior points. Their side-line directions,
modulo `pi`, are

| Type | Beginning side | Ending side |
| --- | --- | --- |
| S | `theta` | `theta` |
| C | `theta-pi/4` | `theta+pi/4` |
| D | `theta+pi/4` | `theta-pi/4` |

Eight squares with centers of norm at least `1` must tile `C_r` by their
eight arcs, just as in the exterior-square theorem. Consecutive midpoint
angles differ by `pi/4`. At a shared endpoint their side lines must coincide,
since otherwise their square interiors overlap in a small open wedge.

No type D can occur: if its midpoint is `theta`, its ending side has direction
`theta-pi/4`, while the next square's beginning-side direction is one of

```text
theta+pi/4, theta, theta+pi/2
```

for types S, C, D, respectively. None agrees modulo `pi`. The remaining
types must alternate S and C, which forces four corner squares sharing one
frame and centered at `(+-1,+-1)`.

## 3. Consequences and remaining case

Eight such centers already force squared radius `9/2`. If they belong to a
ten-square packing, the anchors trigger the full independently oriented
classification in
[ANCHORED_EQUALITY_CLASSIFICATION.md](ANCHORED_EQUALITY_CLASSIFICATION.md).

Thus a hypothetical subcritical packing must have at least three centers
of norm strictly less than `1`. It can have at most five such centers, as
follows. Every unit square contains the open radius-`1/2` disk about its
center, so distinct centers have distance at least `1`. If a center were
the origin, there could be no other center in the open unit disk. Otherwise,
among six centers in that disk two have polar angle difference at most
`pi/3`. Write their radii as `0<s<=t<1`. Their squared distance is at most

```text
t^2+s^2-ts = t^2+s(s-t) <= t^2 < 1,
```

a contradiction.

The remaining subcritical cases therefore have exactly **three, four, or
five centers in the open unit disk**. This is a stronger necessary condition
than having three squares intersect the central disk of radius `1/2`. It
does not by itself exclude the remaining configurations: three or four
disjoint unit squares can certainly have centers in the open unit disk.
