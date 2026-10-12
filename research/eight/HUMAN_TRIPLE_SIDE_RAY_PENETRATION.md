# Every triple central-side population forces a true diameter-crossing single-side square

## Theorem (arbitrary orientations; no contact hypotheses)

Suppose eight pairwise interior-disjoint unit squares lie in a disk
centered at zero with R^2<=9789/2500. Let C be the unique square
containing zero in its open interior and use its own orthonormal
side frame (a,b). Let n be one of its four signed unit side normals,
and m=Jn. Put h=1/2+n dot p_C>0.

If **three distinct exterior unit squares** lie wholly beyond this
central side, namely all belong to

    {x:n dot x>=h},                                      (1)

then **at least one of these three squares has an open-interior
intersection with the positive radial line**

    {t*n:t>0}.                                          (2)

Equivalently, at least one has a nonempty open chord on the
diameter line m dot x=0. That square is necessarily of the
**single-side separator status n** relative to C: it cannot
also be whole-square separated beyond either adjacent signed
side of C.

This is a new all-offset ray-penetration necessity for
every triple side, including 0<h<13/60 where the stronger
two-**whole-quadrant** witness theorem of
HUMAN_TRIPLE_CAP_ORTHOGONAL_WITNESSES.md does not apply.
It does not assert that only one square crosses the ray.

### Consequence for two adjacent double statuses

If the three squares beyond the positive right side include
two distinct double-side members RU and RD, then the
**third R square is a single-R status and necessarily intersects
the open positive x-axis ray through its open interior**.

Similarly, two adjacent double-status squares LU and LD plus a
third L square force the third L to cross the open negative x ray;
rotations and reflections cover the U- and D-sharing versions.

If **two perpendicular sides** both carry triples, then they
require two **distinct** single-side squares crossing the
respective outward cardinal rays. In the pure-single-side
branch S1=(3+0,3+1) this gives an actual ray-crossing witness
on both of its perpendicular triple directions, whatever the
central center offsets. This is a necessary geometric
structure, not a proof that S1 is impossible.

## Hand proof

Rotate so n=(1,0) and h>0. The three entire squares
S1,S2,S3 lie in the strict positive x half-plane
except possibly for their cap-edge boundaries, and
their open interiors lie in x>0.

Assume none has an open-interior point on the line
{(x,0):x>0}. The open interior of each square is
convex and hence connected. The continuous y coordinate
cannot change from positive to negative without
vanishing in that open interior. Therefore each
square's entire open interior lies in either y>0
or y<0; its closed square lies in either the
origin northeast or southeast closed quadrant.

The origin-quadrant capacity theorem
HUMAN_ORIGIN_SECTOR_REPLICATION.md proves that
**at most one complete packed unit square** can lie
in any origin quadrant when R^2<=98/25.
Thus the three squares can occupy at most two
different quadrants, with at most one per quadrant:
a contradiction. At least one S_i therefore meets
the ray (2) in its **open interior**.

A square beyond a perpendicular *upper* central side
lies in a half-plane m dot x>=1/2+m dot p_C>0,
so cannot intersect the line m dot x=0. The same
holds for the opposite *lower* side. Hence the
ray-crossing S_i admits **neither adjacent signed
central-owned side separator**. It is beyond the
n side by hypothesis and so has precisely the
single-side status n. The two-double consequences
follow because the RU and RD squares lie respectively
strictly above and below the horizontal diameter,
so the third R square is the ray-crossing one.

For simultaneous perpendicular triples, each
ray-crossing witness has a **single-side** status
for its own direction, and so a witness for the
other perpendicular side must be a distinct square.
This proves all assertions. QED.

## Relation to the remaining sharp proof

The theorem adds an **actual point-location constraint** to
every cardinality-three central side. In a D2 branch where
two adjacent double statuses share a triple side, it pins
the remaining member of that side to the perpendicular
diameter, leaving no choice about which of the three is
the transverse middle participant.

It does **not** make this member parallel to C, say that
its center lies on the ray, or prove that it has any
actual contact with another square. A chord crossing a
ray is weaker than whole-square separation on the
perpendicular central sides.

In particular it does not establish R8>=Rhat, and it
must not be used to reject the candidate equality
type S4=(2+1,2+2), which has no triple side.
