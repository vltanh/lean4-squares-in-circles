# Circle-contact squares cannot screen a unit square from the origin

## Scope

Assume a packing of unit squares with pairwise disjoint open interiors in
D_R, where

    sqrt(2)+1/2 < R < 2.

A boundary square is one meeting the containing circle. This note proves
that any other square has its open interior in the origin's component
of the complement of any selected collection of boundary squares.
It does not claim that the entire complement is connected: empty pockets
can remain. No contact-graph planarity or common-frame premise is used.

## 1. Center directions of outer squares are separated

Every unit square contains its open inscribed disk of radius 1/2. Hence
centers of different packed squares are at distance at least one. Also,
if p is any square center, the point p+(1/2)p/|p| belongs to its closed
inscribed disk when p is nonzero. Disk containment gives

    |p| <= R-1/2 < 3/2.                                    (1)

Suppose two centers p,q have norms at least one. Their smaller angular
distance is strictly greater than pi/5. Otherwise cos of that distance
is at least cos(pi/5)>4/5, and, writing r=|p|, s=|q|,

    |p-q|^2 <= r^2+s^2-(8/5)rs <= 9/10 < 1.                (2)

For the second inequality, the quadratic is separately convex in r and s
on [1,3/2]^2, so its maximum is at a corner. Its three distinct corner
values are 2/5,17/20,9/10. For the first strict trigonometric comparison,
cos(pi/5)=(1+sqrt(5))/4>4/5 follows from sqrt(5)>11/5.
This contradicts the center-distance bound, proving the assertion.

## 2. A boundary square occupies a narrow cone

Put a=1/sqrt(2), the circumradius of a unit square. If a square A meets
the containing circle and has center p_A, then

    |p_A| >= R-a > 1.

The circumdisk D(p_A,a) contains A and has angular half-width
asin(a/|p_A|) as seen from zero. The tangent-right-triangle calculation
therefore bounds the half-width of A by

    asin(a/(R-a)) < pi/5.                                  (3)

Here a/(R-a)<2-sqrt(2)<sin(pi/5). The second comparison has the exact
square check

    (2-sqrt(2))^2 < (5-sqrt(5))/8.

Rearranging and squaring positive quantities reduces this to
43*sqrt(5)<97, whose squared comparison is 9245<9409.

Combine (2) and (3). If T is any different packed square with center
|p_T|>=1, the entire ray {t p_T:t>=0} misses A. Indeed the angular
distance of their center directions is greater than pi/5, whereas
all points of A have angular distance less than pi/5 from p_A.

Thus we have proved a radial visibility statement:

> A packed square whose center has norm at least one sees the origin
> along its center ray without intersecting any other boundary square.

This concerns actual closed sets, not only their centers or contact points.

## 3. No boundary-only pocket can contain a whole unit square

Select any collection B of boundary squares. Let

    Omega = {x:|x|<R} minus the union of the closed squares in B.

Every point of a boundary square A has norm at least

    b=R-sqrt(2)>1/2,                                      (4)

because A has a point of norm R and diameter sqrt(2). Hence the open
disk D_b lies in Omega, in its component containing zero.

Let T be a packed square not in B. Its open interior is disjoint from
every closed square in B: if an interior point of T were a boundary
point of A, an open neighborhood inside T would contain interior points
of A as well. Also every interior point of T lies in the open disk
of radius R. Thus int(T) is a connected subset of Omega.

Suppose it belonged to a component not containing zero. It would avoid
D_b. Its open inscribed disk D(p_T,1/2) would avoid D_b too, giving

    |p_T| >= b+1/2 > 1.                                  (5)

By section 2 the segment from zero to p_T misses every square of B.
That segment lies in the open radius-R disk and hence in Omega. It
connects p_T to zero, contradicting the supposed component assignment.

Therefore every packed square not in B has its open interior in the
origin's component of Omega. In particular, a component cut off from
zero solely by circle-contact squares and the containing circle cannot
hold another packed unit square.

## 4. Consequence for cycle arguments

A cycle made solely of boundary squares may surround the origin; this
note does not exclude it. However an additional unit cannot occupy a
region on the opposite side of a genuine boundary-only barrier from
the origin. When a contact cycle also contains strictly interior squares,
those squares must be retained in any claimed pocket boundary. Deleting
them and still treating the pocket as closed would invalidate the argument.

The result is applicable throughout the analytical radius range of an
eight-square minimizer. It does not yet assign every unused square to a
particular contact gap, force degree two, or produce the five-corner chain.
