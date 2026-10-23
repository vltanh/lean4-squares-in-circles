# A split core arc leaves no hidden ring gap

Work in any packing of unit squares contained in a disk centered at zero
with squared radius `q<=491/100`. Put

\[
 R=41/40,\qquad \rho=27/20.
\]

Call a square a core square when its center radius is less than `R`, and
a ring square otherwise. The preceding rational arc lemma gives every
ring square one circle arc at radius `rho` of length strictly greater than
`7/10`. All square centers have radius less than `5/3`.

**Theorem.** A core square can meet the radius-`rho` circle in two separate
components. The intervening gap cannot contain an interior circle point
of any ring square. Thus, for purposes of placing ring arcs, each core's
two components can be replaced by their single circular angular hull.
This applies to both the three-core and four-core cases; no stronger lower
bound on ring-center radius is needed.

## 1. Core circle topology

Choose a core square's own frame so its center is `(a,b)` with `a>=b>=0`.
Its coordinate intervals are `[a-1/2,a+1/2]` and `[b-1/2,b+1/2]`.

If `a<1/2`, the origin lies in the square. Every corner except possibly
the far positive corner has norm at most `sqrt(5)/2<rho`. The circle
intersection is consequently empty or one arc near that positive corner.

If `a>=1/2`, the circle intersection lies in the right semicircle.
The lower and upper bounds on its `y` coordinate and the lower bound on
its `x` coordinate first restrict the circle angle to one interval.
The remaining upper `x` bound either leaves that interval connected or
removes the central interval `(-eta,eta)`, where

\[
 A=a+1/2<\rho,\qquad \eta=\arccos(A/\rho).
\]

Thus there are at most two components. If both occur, then `b<1/2` and
the negative far corner must reach the circle:

\[
 A^2+(1/2-b)^2\ge\rho^2.                  \tag{1}
\]

In particular,

\[
 a>3/4,\qquad a<17/20,\qquad
 \eta\le\arcsin(10/27)<2/5.               \tag{2}
\]

The first inequality follows from
`A^2>=rho^2-1/4=629/400>(5/4)^2`. For the last strict inequality,
`sin(2/5)>=2/5-(2/5)^3/6=146/375>10/27`.
Both circle points with angles `-eta` and `eta` belong to the closed core
square; (1) gives the necessary `y` bounds for both.

The same statements allow a component to be a single tangent point.
The physical boundary issue needed for this endpoint case is handled next.

## 2. Ring arcs have no internal boundary point

For two closed squares with disjoint open interiors, no point of one
closed square can belong to the other's open interior. Otherwise a small
open ball in the second square around that point would contain a point
of the first square's open interior.

Moreover, the open-square intersection of a ring square with the circle
is a single open angular interval, obtained from its closed arc by deleting
only its endpoints. Here is a check of the possible internal tangencies.
In its own frame write the ring center as `(a,b)`, `a>=b>=0`. An internal
boundary point of a connected circle arc could occur only where a square
side is tangent to the circle. Near-side tangency at coordinate `rho`
would require `a` or `b` to equal `rho+1/2=37/20>5/3`; tangency at `-rho`
is impossible because both near coordinates are at least `-1/2`.
A far-side tangency `a+1/2=rho` gives `a=17/20`; then

\[
 b^2\ge R^2-(17/20)^2=21/64>1/4,
\]

so the point `(rho,0)` is outside the other coordinate interval. If
`b+1/2=rho`, then `a>=b=17/20`, so `(0,rho)` is outside the first
coordinate interval. These exhaust the four side types. Therefore no
internal tangency occurs.

Consequently the two closed core points at angles `-eta,eta` block a
connected open ring arc. If a ring arc met the open intervening gap,
its whole open arc would lie in that gap, and its closed arc would lie
in `[-eta,eta]`. This conclusion includes isolated core tangent points;
it uses physical disjointness, not only angular measure.

## 3. A ring arc cannot fit the intervening gap

Suppose a ring arc did fit. Its length is greater than `7/10`, so
`eta>7/20`. Equation (1) then gives

\[
 1/2-b\ge\rho\sin\eta>\rho/3=9/20,
 \qquad b<1/20.                           \tag{3}
\]

For the strict sine comparison,
`sin(7/20)>=7/20-(7/20)^3/6=16457/48000>1/3`.

Let `r` be the ring-center radius and `theta` its angle in the core's
chosen coordinates. Its inscribed open disk of radius `1/2` contains
the radius-`rho` circle points at angular offsets `+1/4` and `-1/4`
from its center ray. Indeed `cos(1/4)>=31/32`, and the squared distance
from either point to its center is bounded above by

\[
 \rho^2+r^2-2\rho r(31/32).
\]

This convex quadratic attains its maximum on `[R,5/3]` at an endpoint.
The two endpoint values are `2459/12800` and `3469/14400`, both strictly
less than `1/4`. Thus those points, and the intervening circle arc, lie
in the ring square's open interior.

Fitting them into the core gap forces

\[
 |\theta|<\eta-1/4<3/20.
\]

Write the ring center as `(x,y)` in the core frame. Then

\[
 |y|< (5/3)(3/20)=1/4,
 \quad x<5/3,
 \quad x>R(1-(3/20)^2/2)>17/20>a.
\]

Together with (2) and (3), these imply that the squared distance between
the two square centers is strictly less than

\[
 (5/3-3/4)^2+(1/4+1/20)^2
 =\frac{3349}{3600}<1.
\]

This contradicts the necessary center distance of at least one, and proves
the theorem.

## 4. An exhaustive cyclic occupancy reduction

Replace each nonempty core circle intersection by its single angular
hull, as justified above. Its hull is a proper connected closed arc; the
preceding proof handles any filled internal gap. A ring's open arc avoids
every such hull. The union of `k` core hulls has at most `k` connected
components. If it filled the circle, no ring could exist. Otherwise its
complement has at most `k` connected angular gaps. If all core hulls are
empty, treat the full circle as one gap.

Each connected open ring arc belongs to exactly one gap. Label the gaps
cyclically and record their nonnegative ring counts; empty gaps are retained.
Rotation and reflection of this cyclic list give equivalent labels.
The exact enumeration in `enumerate_core_gap_counts.py` yields:

| Core/ring count | Gap count | Cyclic count vectors up to dihedral symmetry |
| --- | --- | ---: |
| `(3,8)` | `1..3` | 16 |
| `(4,7)` | `1..4` | 33 |

These 49 rows are an exhaustive **coarse occupancy cover** of the two count
cases. They retain the original continuous square poses and all 55 physical
pair constraints. They do not assert realizability or prove a sharp bound
for any row.

Two useful coarser alternatives follow immediately:

- With three cores and eight ring squares, either one gap has at least
  four ring squares, or there are exactly three gaps with cyclic counts
  `(3,3,2)`.
- With four cores and seven ring squares, either one gap has at least
  three ring squares, or there are exactly four gaps with cyclic counts
  `(2,2,2,1)`.

Core hulls may overlap one another. Their widths must not be added without
an additional disjointness proof. The remaining work is to bound the
physical capacities of these gaps using the core geometry and ring poses.
