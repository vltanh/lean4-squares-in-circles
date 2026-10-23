# Eight exterior squares force four anchors

This is a hand proof for independently oriented unit squares. It sharpens
[CENTRAL_DISK_REDUCTION.md](CENTRAL_DISK_REDUCTION.md): eight exterior squares already force the target
squared radius and four boundary anchors. Consequently the unrestricted
ten-square theorem is proved whenever exactly two squares meet the open disk
of radius `1/2`. The case with at least three such squares remains open.

Put

```text
Q = 9/2,
R = 3/sqrt(2),
r = sqrt(1 + 1/sqrt(2)) = 1/(2 sin(pi/8)),
a = (sqrt(17) - 1)/2.
```

Call a square **exterior** if it avoids the open disk `B(0,1/2)`; contact with
its boundary is permitted. All squares below lie in the closed disk `D(0,R)`
and have pairwise disjoint interiors. Their orientations are arbitrary.

## 1. A two-variable inequality

Suppose `A,B >= -1/2`, `A,B <= r`, and

```text
(A+1)^2 + (B+1)^2 <= 9/2.
```

Then

```text
asin(A/r) + asin(B/r) <= pi/4,                         (1)
```

with equality exactly when `A=B=1/2`.

To prove this, put `alpha=asin(A/r)` and `beta=asin(B/r)`. Each angle is at
least `-pi/8`. If their sum is at least `pi/4`, decrease them, if necessary,
until their sum equals `pi/4`, while keeping each at least `-pi/8`. This can
only decrease `(1+r sin(alpha))^2+(1+r sin(beta))^2`, and decreases it strictly
if either angle changes.

On the line `alpha+beta=pi/4`, write

```text
alpha = pi/8 + t,
beta  = pi/8 - t,
z = cos(t).
```

The angle bounds give `|t|<=pi/4`, so `1/sqrt(2)<=z<=1`. Using
`r sin(pi/8)=1/2`, direct expansion gives

```text
(1+r sin(alpha))^2 + (1+r sin(beta))^2 - 9/2
  = (1-z) ((1+sqrt(2))(1+z)-2) >= 0.
```

The second factor is positive. Equality requires `z=1`, hence `t=0` and
`A=B=1/2`. This proves (1), including strictness when the angle sum is larger.

## 2. Every exterior square occupies an arc of angle `pi/4`

More precisely, the intersection of an exterior square with `C_r`, the circle
of radius `r`, is one closed arc of angular length at least `pi/4`.

Rotate the axes into the square's edge directions and reflect or interchange
them so that its center has coordinates `(u,v)` with `u>=v>=0`. Set

```text
A = u-1/2,    B = v-1/2,
U = u+1/2,    V = v+1/2.
```

Containment and exteriority are exactly

```text
U^2 + V^2 <= 9/2,                                    (2)
max(A,0)^2 + max(B,0)^2 >= 1/4.                      (3)
```

### Case `v<1/2`

Equation (3) gives `u>=1`. Thus `U>=3/2>r`, and the right edge cannot cut
`C_r`. Moreover

```text
A <= R-1 < (1+sqrt(2))/2 = r cos(pi/8).
```

Since `B>=-1/2`, the lower endpoint of the arc is therefore on `y=B`, rather
than on `x=A`. The arc is precisely

```text
[asin(B/r), min(asin(V/r), acos(A/r))].              (4)
```

Here `V<1<r`, and (1) ensures that the displayed interval has positive length.

If the upper endpoint is on `x=A`, its angular length is

```text
acos(A/r)-asin(B/r)
  = pi/2-asin(A/r)-asin(B/r) >= pi/4
```

by (1). Equality in this case is impossible, since `B<0`.

If the upper endpoint is on `y=V`, the endpoint chord has length at least
`V-B=1`. Since `2r sin(pi/8)=1`, the arc has angular length at least `pi/4`.
Equality requires a vertical chord, whose endpoints on a circle have
opposite `y` coordinates. Thus `v=0`. Conversely, for `v=0`, (2)--(3) say
`1<=u<=a`, and the points

```text
(r cos(pi/8), -1/2), (r cos(pi/8), 1/2)
```

lie strictly between the radial edges `x=u-1/2` and `x=u+1/2`. They are the
arc endpoints, so every such square has angular length exactly `pi/4`.

### Case `v>=1/2`

Now `A>=B>=0`. Equation (2), by the sum-of-squares inequality, gives
`A+B<=1`. Thus the nearest corner has radius at most `1<r`. Equation (3)
gives `A^2+B^2>=1/4`, and hence `A+B>=1/2`, so the farthest corner has squared
radius

```text
(A+1)^2+(B+1)^2 >= 1/4+1+2 = 13/4 > r^2.
```

The intersection with `C_r` is consequently a nonempty single arc in the
first quadrant. Its lower endpoint is on `y=B` or `x=U`, and its upper
endpoint is on `y=V` or `x=A`.

If the endpoints lie on opposite edges, their chord has length strictly
greater than `1`: distinct points on the first-quadrant circle have distinct
coordinates in both directions. The angular length is therefore greater
than `pi/4`.

If they lie on the two inward edges `y=B` and `x=A`, (1) gives length at least
`pi/4`, with equality precisely at `A=B=1/2`, or `u=v=1`.

The remaining possibility, endpoints on both outward edges, is impossible.
It would require `U,V<=r`, so

```text
A^2+B^2 <= 2(r-1)^2 < 1/4,
```

contrary to (3). For the strict inequality, observe that
`r<1+1/(2 sqrt(2))`: the square of the right side is `r^2+1/8`.

This completes the arc bound and its equality classification.

## 3. The two equality types

Every equality square has exactly one of the following forms, described
without choosing the square's axes.

* **Strip type S:** its center is `u e_theta`, where `1<=u<=a`, and one edge
  direction is radial, `e_theta`. Its arc has midpoint angle `theta` and
  endpoints `theta-pi/8`, `theta+pi/8`.
* **Corner type C:** its center is `sqrt(2) e_theta`, and its edge directions
  have angles `theta-pi/4` and `theta+pi/4`. Its arc has the same midpoint and
  endpoint angles. This square has farthest squared radius exactly `9/2`.

Every arc endpoint is strictly inside a square side, rather than at a vertex.
For type S this follows from the strict radial inequalities in Case 1. For
type C its two endpoint coordinates, in its own axes, are

```text
(r cos(pi/8), 1/2), (1/2, r cos(pi/8)),
```

where `1/2<r cos(pi/8)<3/2`.

At the beginning and end of the arc, respectively, the side-line directions
are as follows, with directions taken modulo `pi`:

| Type | Beginning side | Ending side |
| --- | --- | --- |
| S | `theta` | `theta` |
| C | `theta-pi/4` | `theta+pi/4` |

## 4. Eight exteriors force alternating types and four anchors

For disjoint square interiors, the relative interiors of their circle arcs
are disjoint. Eight exterior squares have total arc length at least `2pi`;
therefore all eight arcs have length exactly `pi/4` and tile the circle.
Their successive midpoint angles are

```text
theta_k = theta_0 + k pi/4,    k=0,...,7.
```

At a shared endpoint, both squares have that point in the relative interior
of a side. Their two side lines must coincide. Indeed, if the lines were
distinct, they would cross there, and the two local open half-planes occupied
by the square interiors would have a nonempty open wedge in common. This
would contradict disjoint interiors.

Adjacent S types cannot occur: their meeting side-line directions differ by
`pi/4`. Adjacent C types cannot occur either: the first ending side has
direction `theta_k+pi/4`, whereas the next beginning side has direction
`theta_k`. Thus the types alternate S,C,S,C,S,C,S,C.

The four corner centers have length `sqrt(2)` and successive directions
differing by `pi/2`; their square edge directions agree modulo `pi/2`.
After one common rotation they are exactly the four axis-parallel unit
squares centered at

```text
(-1,-1), (-1,1), (1,-1), (1,1).
```

In particular, eight exterior squares cannot fit in any strictly smaller
disk. There cannot be nine exterior squares even at radius `R`, since their
arcs would have total angular length greater than `2pi`.

## 5. Consequence for ten squares

Every ten-square packing in `D(0,R)` has at least two squares meeting
`B(0,1/2)`. If exactly two do so, the other eight are exterior and the preceding
theorem supplies the four anchors and forces squared radius `9/2`.
[ANCHORED_EQUALITY_CLASSIFICATION.md](ANCHORED_EQUALITY_CLASSIFICATION.md)
then classifies all ten squares: in a
common frame they are the four anchors, side-middle centers `(-u,0),(v,0)`,
and four central-column centers `(0,t_i)`, where

```text
1 <= u,v <= a,
-a <= t_1,
t_(i+1)-t_i >= 1,    i=1,2,3,
t_4 <= a.
```

Thus any hypothetical ten-square packing with squared radius less than
`9/2` must have at least three squares meeting `B(0,1/2)`. Excluding those
remaining configurations requires an additional argument; the arc bound
alone does not do so.
