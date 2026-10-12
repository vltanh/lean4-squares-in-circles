# A forced four-diameter routing in the saturated two-triple branch

## Theorem: Type A has four distinct cardinal-ray-crossing squares

Work at q=R^2<=9789/2500 with a central unit square C containing
the origin in its open interior, and use its horizontal/vertical
side frame. Say a square is served by signed side R,L,U,D only if
its **entire closed square** lies beyond that central-owned side.

Assume the maximally saturated Type A pattern of
SATURATED_SIDE_STATUS_BRANCHES.md: after reflection there are
three whole R squares, one whole L square, three whole U
squares and one whole D square, with exactly seven distinct
exterior squares and exactly one RU double-side member.
The seven mutually exclusive statuses are therefore

    RU, R, R, L, U, U, D.                           (1)

Then there exist four **different** exterior squares
S_R,S_L,S_U,S_D such that the open interior of S_R
crosses the positive x-axis ray, S_L the negative x-axis
ray, S_U the positive y-axis ray, and S_D the negative
y-axis ray.

The four squares are genuine **single-side** status
members R,L,U,D, respectively; none is the RU double.

This is an exact ray-routing necessity across the full
central-center offset interval for Type A, including
offsets below the threshold of the triple
whole-quadrant witness theorem. No assumption on
square frame orientations, actual-contact edges,
stress, or which squares touch the circle is used.

## Proof of four-ray routing

The R side serves three whole exterior squares,
so HUMAN_TRIPLE_SIDE_RAY_PENETRATION.md provides
one of them, say S_R, whose **open interior**
intersects the positive x-axis ray. That theorem
also shows S_R must have single-side R status,
because either adjacent U or D whole-cap separator
would place it strictly above or below y=0.

The U side similarly serves three squares.
A quarter-turn gives a single-U status square
S_U whose open interior intersects the
positive y-axis ray. The statuses R and U
are distinct, so S_R and S_U are different
actual packed squares.

Let p_C=(a,b). The three-R sharp cap theorem
and q<2257/576 force its offset
h_R=1/2+a<7/24. Thus the opposite L central
side has positive offset

    h_L=1-h_R>17/24.

There is exactly one square S_L beyond L
in (1). The transverse lane theorem
HUMAN_DISTANT_SIDE_TRANSVERSE_LANE.md applies
at h_L>17/24 and proves that the **open
interior** of S_L crosses the negative x-axis
ray through zero. Its L status differs
from those of S_R and S_U.

Likewise the U triple has
h_U=1/2+b<7/24, forcing the opposite
D side offset h_D=1-h_U>17/24.
The unique D member S_D crosses the
negative y-axis ray in its open
interior. Its status differs from
R,U,L and so it is a fourth distinct
square. This proves the four-ray theorem.

The RU double member lies entirely in
x>=h_R>0, y>=h_U>0, so it cannot be any
of these four ray-crossing squares.
It also crosses the origin northeast
**diagonal** ray at 45 degrees through
its open interior, by
HUMAN_STATUS_ANGULAR_LANES.md.

The two remaining exterior labels
are the other single-R and single-U
square from (1). They are not identified
by the four-ray argument alone.

## Sharpening if both triple offsets exceed thirteen sixtieths

Suppose in addition

    h_R>=13/60,       h_U>=13/60.                  (2)

HUMAN_TRIPLE_CAP_ORTHOGONAL_WITNESSES.md proves
that the R triple has one **entire**
unit square in the open origin NE quadrant
and one in the open origin SE quadrant.
By the k=4 quadrant-capacity theorem,
the NE quadrant can contain at most one
whole packed square; the existing RU
double member is wholly NE. Thus the
NE R witness is precisely RU, and
the SE witness is the second single-R
square left after choosing S_R.

Similarly the U triple has one whole
NE and one whole NW square. The NE
member is RU and the NW witness is
the second single-U square.

Consequently under (2) the seven
exterior squares have the following
**forced exhaustive angular roles**:

| Square status | Geometrically compulsory role |
| --- | --- |
| RU | Entirely in origin NE quadrant; crosses NE diagonal ray |
| R (first) | Crosses open positive x-axis ray |
| R (second) | Entirely in open origin SE quadrant |
| U (first) | Crosses open positive y-axis ray |
| U (second) | Entirely in open origin NW quadrant |
| L | Crosses open negative x-axis ray |
| D | Crosses open negative y-axis ray |

Every row is a *distinct actual square*. The
first, third and fifth rows are whole-quadrant
members; the other four are cardinal-ray
intersections through **open interiors**.
This is a far sharper geometric normal form
than the count vector (3+1,3+1), obtained
without fixing any square's own orientation.

## Other saturated branches and the remaining gap

In saturated Type B (3+1,2+2), the triple
side and its opposite singleton also
force distinct opposite cardinal-ray
crossings by the same argument, but the
perpendicular 2+2 pair does not force
another full pair of ray crossings.
In saturated Type C (2+2,2+2) there is no
triple, so the four-ray result is not
asserted.

This theorem does **not** force a
five-square *parallel* contact cross:
the ray-crossing square frames may be
rotated, contacts may be absent, and the
four radial chords need not share a
common projected separator orientation.
No parallel-cross occupancy bound may be
substituted without proving that alignment.

To exclude Type A below Rhat, one must
still show that these seven compulsory
angular roles and the central square
cannot coexist at smaller radius, or
derive a sharp five-corner inequality.
The theorem is a rigorous restructuring
of the branch, **not** its exclusion.
