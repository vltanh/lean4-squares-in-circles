# At most six square centers lie in the radius 41 over 40 disk

**Theorem.** A family of pairwise open-interior-disjoint unit squares whose
centers have norm at most `41/40` has at most six members. If it has six,
exactly one square contains the origin in its open interior.

This theorem imposes no restriction on individual orientations. It does not
require an enclosing disk for the whole squares. Combined with
[RATIONAL_CORE_RADIUS.md](RATIONAL_CORE_RADIUS.md), it replaces the previous
five count cases by the four necessary alternatives

| Core centers of norm `<41/40` | Ring centers of norm `>=41/40` |
| ---: | ---: |
| 3 | 8 |
| 4 | 7 |
| 5 | 6 |
| 6 | 5 |

In the last row exactly one core square contains the origin. The remaining
rows are not asserted realizable or solved. All original pair constraints
remain required.

## 1. A unit-circle arc for every origin-avoiding square

Let a square avoid the origin in its open interior and have center norm
`r<=41/40`. In its own frame choose coordinates `a>=b>=0`; origin avoidance
means `a>=1/2`. Write `x=a-1/2`, `y=b-1/2`.

The far primary side satisfies `a+1/2>=1`, and `0<=x<=21/40<1`. The near
corner satisfies

\[
x^2+y^2\le r^2-r+1/2<1.
\]

For this bound, `1/2<=r<=41/40`; the convex quadratic has its maximum on
that interval at an endpoint, and both endpoint values are less than one.
The square therefore intersects the unit circle in a single connected arc,
with lower endpoint `asin(y)` and upper endpoint
`min(acos(x),asin(b+1/2))` when `b+1/2<=1`, or `acos(x)` otherwise.
These formulas include `a=1/2`, `b=1/2`, and all side tangencies.

The parallel-side difference is at least

\[
\arcsin(1/2)-\arcsin(-1/2)=\pi/3,
\]

with equality only when `b=0`. This follows by the same strict derivative
comparison for `b>0` used in the annular arc proofs.

The near-side difference is strictly greater than `pi/3`. To prove this,
maximize `asin(a-1/2)+asin(b-1/2)` at fixed `r` by writing
`a=r cos(theta)`, `b=r sin(theta)`, `theta<=pi/4`. Define

\[
K(z)=z\sqrt{1-(z-1/2)^2},\qquad s=a+b.
\]

The derivative of the arcsine sum has the sign of `K(a)-K(b)`, and

\[
K(a)^2-K(b)^2=(a-b)
\left[(3/4-r^2)s+\frac{s^2+r^2}{2}\right].       \tag{1}
\]

The bracket is at least `(3/4-r^2+r)s>0`, since `r<3/2` and `r>0`.
Both radicals are positive on the entire path toward the diagonal center.
Thus the arcsine sum is maximal at `a=b=r/sqrt(2)` and is at most

\[
2\arcsin\left(\frac{41}{40\sqrt2}-\frac12\right)
<2\arcsin(1/4)<\pi/6.
\]

For the first strict comparison, `41<30sqrt(2)` follows from `1681<1800`.
For the second, `sin(pi/12)=(sqrt(6)-sqrt(2))/4>1/4`, because
`sqrt(6)>sqrt(2)+1` is equivalent after squaring to `3>2sqrt(2)`.
Consequently the near-side arc length is greater than `pi/3`.

Every origin-avoiding square in this center disk therefore contributes
unit-circle angular measure at least `pi/3`. Equality occurs only when
`b=0`. In that equality case its center lies on one of its own frame axes,
and the arc is centered on the center ray, with half-width exactly `pi/6`.
Square-boundary points have zero circle measure.

## 2. Six origin-avoiding squares would overlap

Suppose six such squares all avoid the origin. Their open unit-circle
intersections are disjoint, so the six lower bounds `pi/3` must all be
equalities. Hence every center is radial in its own frame and the six arcs
have length exactly `pi/3`. They tile the circle without positive gaps.
Their cyclic consecutive center rays are therefore separated by exactly
`pi/3`.

Take two consecutive squares, with center radii `r,s` in `[1/2,41/40]`.
In the first square's radial frame the center difference has projections

\[
s/2-r,\qquad \sqrt3\,s/2.
\]

In the second square's radial frame the projection magnitudes are bounded
in the same way, with `r,s` interchanged. All four own-axis projections
have absolute values strictly less than one: the radial projections are at
most `41/40-1/4=31/40`, and the transverse ones are at most
`41sqrt(3)/80<1`, since `5043<6400`.

But every own-axis support separation of two unit squares requires projection
at least one. No one of the eight signed own-axis alternatives is feasible.
The separating-axis theorem therefore says that the two open square interiors
overlap, a contradiction. Thus at most five of these squares can avoid the
origin in their open interiors.

## 3. The count and its exact scope

At most one square in any packing can contain the origin in its open interior.
Together with the preceding bound of five origin-avoiding squares, this gives
at most six centers in the radius-`41/40` disk. A six-member family must have
one origin-containing square, which is unique.

The result includes closed center-radius endpoints. It is a geometric center
count, not a theorem that six such squares are realizable, rigid, or optimal.
For the eleven-square problem it closes the seven-core row after changing to
the new rational threshold. Lower bounds for the four remaining count rows
and all physical core-to-ring completions remain open.
