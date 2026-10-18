# An outer quadrant cell cannot contain both a parallel and a rotated unit square below radius two

## Theorem (one common frame, one arbitrary frame)

Let Q be an axis-parallel unit square, S an
arbitrarily rotated unit square, with disjoint
open interiors, both contained in the same
disk D_R centered at zero, where R<2.

Their centers **cannot both lie in any one
of the four closed outer-quadrant cells**

    x>=1/2, y>=1/2;
    x<=-1/2, y>=1/2;
    x<=-1/2, y<=-1/2;
    x>=1/2, y<=-1/2.                              (1)

There is no assumption that Q and S touch
one another or the disk boundary. The
result is sharper than center-radius and
center-distance bounds alone: two *both
rotated* squares can occupy such a quadrant,
so retaining the one-parallel hypothesis
is essential.

**Consequence for n=8.** If at most one
of the seven exterior squares departs
from a given common frame, no outer
quadrant cell in that frame can contain
two of the seven square centers. Thus the
four quadrant-cell occupancy bound Q<=4
from the completely parallel proof
remains valid with **one** freely rotated
exterior square. The horizontal and
vertical side-cell capacities require
separate analysis; they are not asserted
here. The rotated square may also have
its center in the open central cell.

## 1. Center differences in one outer quadrant are below 7/8

By reflections suppose both centers have
coordinates at least 1/2. The exact
farthest-vertex formula gives, for every
unit square center p in D_R with R<2,

    |p|^2+|p|+1/2<4.

Solving the quadratic yields

    |p|<(sqrt(15)-1)/2,
    |p|^2<4-sqrt(15)/2<21/10,                      (2)

because sqrt(15)>19/5.

If the two center abscissas differed by
at least 7/8, the larger would be at
least 1/2+7/8=11/8; that center's
other coordinate is at least 1/2.
Its squared norm would therefore be
at least

    (11/8)^2+(1/2)^2=137/64>21/10,                (3)

contradicting (2). Thus

    |p_S.x-p_Q.x|<7/8.                             (4)

The same argument bounds their y
difference, though that is not
needed for the contradiction below.

## 2. Use the arbitrary-frame two-unit span theorem

Let L=|cos theta|+|sin theta| be S's
vertical and horizontal projected
width in Q's axis frame, so
1<=L<=sqrt(2). The analytically
proved one-parallel projection lemma
in HUMAN_SCAFFOLD_CLOSURE.md, section 3,
says that for two disjoint unit
squares Q (parallel) and S (arbitrary)
with the center horizontal difference
at most 7/8,

    |p_S.y-p_Q.y|+(1+L)/2 >=2.                  (5)

Its proof is a four-axis separating
argument, including all orientation
signs, so (5) can be used without
assigning an unproved separating axis.

Write the two center ordinates y_S,y_Q,
each at least 1/2. There are two cases.

## 3. The rotated square has the higher center

If y_S>=y_Q, (5) gives

    y_S+L/2 >=y_Q+3/2>=2.                         (6)

But the uppermost vertex of S has
ordinate exactly y_S+L/2, whereas
every point of D_R has ordinate
strictly less than 2. Contradiction.

## 4. The parallel square has the higher center

If y_Q>y_S, (5) gives

    y_Q+1/2 >=y_S+2-L/2
             >=5/2-1/sqrt(2)
             >sqrt(3).                             (7)

For the strict comparison use
1/sqrt(2)<5/7 and sqrt(3)<7/4,
whose squared comparisons are
49<50 and 48<49; also
5/2-5/7=25/14>7/4 because 100>98.

The top-right vertex of Q has
coordinates (x_Q+1/2,y_Q+1/2).
By x_Q>=1/2, its squared norm
is greater than

    1^2+(sqrt(3))^2=4,

contradicting R<2.

Both center-height orders are
impossible. Reflection treats
the other three cells. QED.

## 5. Application and essential limitation

The parallel-center occupancy proof
HUMAN_PARALLEL_EIGHT_OPTIMUM.md uses
one-center-per-quadrant-cell and
one-center-per-positive/negative
side cell. This theorem extends only
its **quadrant** conclusion to a
configuration with one rotated
exterior square: any two centers
in the same quadrant must include
at least one of the six parallel
ones, so the theorem or the usual
parallel pair criterion excludes
them.

The same extension does **not**
hold in a horizontal side cell.
For example, an axis-aligned square
centered at (1/2,-49/100), and
a square rotated by negative angle
1/5 radians centered at
(29/25,49/100), have disjoint
closed sets with positive
separating-axis margin and both
fit in a disk of radius slightly
below 2; both centers satisfy
x>=1/2 and |y|<1/2. This is a
diagnostic counterexample rather
than a premise of the proof above.
One must retain the extra
side-cell branches.

In particular the present
quadrant result does not by
itself prove the global optimal
packing radius R8=Rhat or the
sharper conjecture that exactly
one tilted exterior square cannot
beat the parallel optimum.
