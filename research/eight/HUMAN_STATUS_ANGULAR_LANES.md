# Exact angular lanes forced by a full quadrant square or a triple side

## Theorems

Work in D_R, R^2<=98/25, with arbitrary independently
oriented, interior-disjoint unit squares.

**Quadrant-bisector theorem.**
Any complete unit square **omitting the origin in its closed set**
and lying in a closed origin quadrant, e.g.
{x>=0,y>=0}, intersects the open bisector ray {t(1,1):t>0} **through its open interior**.
In particular an exterior square served by both
central right and upper side axes RU must meet
the 45-degree origin ray through actual interior
points, and the corresponding RD, LU, LD statuses
meet their respective diagonal rays.

**Triple-half-disk angular-spread theorem.**
Suppose three complete pairwise interior-disjoint unit
squares lie in the origin half-disk {x>=0}.
Then **some actual vertex of one square** satisfies

    y > x/sqrt(3),

and **some actual vertex of one (possibly other)
square** satisfies

    y < -x/sqrt(3).                                (1)

Thus their union must have polar angular span
strictly greater than 120 degrees.
By rotation, a population of three whole
squares beyond any one positive-offset
central side has genuine vertices reaching
both open +/-30-degree cones, measured about
that central side's outward normal.

These are additional **geometric placement
necessities**, not a count exclusion beyond
the already proved capacity-three semicircle
bound. They do not assert that a center ray
has any particular angle, or that a chosen
angular extreme square must touch the circle.

## Hand proof: a quadrant square must cross its bisector

Let S lie in the positive origin quadrant **and omit zero**.
It is compact and convex and has a nonempty
open interior. Its set of polar angles is a
closed interval [alpha,beta] inside [0,pi/2]:
the angle map is continuous on S, and S
is connected and omits zero in its open set.

HUMAN_ORIGIN_SECTOR_REPLICATION.md proves that
**no unit square** in D_R can be wholly contained
inside any closed origin sector of opening
at most pi/4. Hence

    beta-alpha > pi/4.                              (2)

If beta<=pi/4 then beta-alpha<=pi/4,
contradiction. If alpha>=pi/4 then
beta-alpha<=pi/4, likewise. Therefore

    alpha<pi/4<beta.                                (3)

The extreme angles in (3) can be attained
by interior points after slightly moving
from their defining boundary points toward
a fixed interior point. Choose one interior
point with angle less than pi/4 and one
with angle greater. Their connecting
segment lies in the **open interior** of
the convex square. By continuity it contains
a point of polar angle exactly pi/4.
That point lies on the positive diagonal
ray and in int(S), proving the theorem.
Reflection proves the three other quadrants.

## Hand proof: three in one half-disk reach both extreme cones

Let S_1,S_2,S_3 lie in {x>=0}. Their union
has polar angle minima alpha and maxima beta,
with

    -pi/2<=alpha<=beta<=pi/2.

If beta-alpha<=2*pi/3, all three complete
squares would be contained in one closed
origin sector of opening <=2*pi/3.
The k=3 version of
HUMAN_ORIGIN_SECTOR_REPLICATION.md would
then give at most floor(7/3)=2 squares
there, a contradiction.

Therefore beta-alpha>2*pi/3.
Since alpha>=-pi/2, the upper extreme must
satisfy beta>pi/6; otherwise its span
would be at most pi/6+pi/2=2*pi/3.
Similarly alpha<-pi/6.

Hence there are actual points of the
three squares in each open region
y>x/sqrt(3) and y< -x/sqrt(3).
The two inequalities are linear in (x,y).
A linear function positive at some point
of a polygon is positive at some actual
vertex of that polygon. Thus each region
contains a true square vertex as claimed.
This proves (1), with no orientation
assumption or selection of separating axes.

## What has and has not been pruned

* A double-side central separator status is **not just**
  a square center in an angular quadrant: it guarantees
  a whole-square intersection with that quadrant's
  diagonal ray. This can be added to full SAT
  separator tests without approximating the square
  by its inscribed disk or its center ray.
* A triple side must be angularly spread over more
  than 120 degrees and reach both open 30-degree cones.
  This is a whole-square condition independent of
  the sharp three-square **radial cap inequality**.
* D2 (two adjacent double statuses) consequently puts
  two distinct whole square interiors across the
  two rays at +/-45 degrees about the shared side,
  while FORCED_CORNER_EXCEPTION_D2.md proves it needs
  at least one additional own-axis corner exception.
  These are simultaneous, exact constraints on the
  surviving geometric branch.

These facts are not the five-corner inequalities,
nor do they exclude every arrangement with those
status labels. The unrestricted sharp lower bound
R8>=Rhat remains OPEN.
