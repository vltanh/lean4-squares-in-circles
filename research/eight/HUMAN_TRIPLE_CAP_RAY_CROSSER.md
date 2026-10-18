# Every three-square central cap has an actual outward ray-crosser

## Theorem (all orientations and every positive side offset)

Let three unit squares S1,S2,S3 have pairwise disjoint open
interiors, lie inside D_R with R²<=98/25, and be contained
**whole** in the positive-offset half-plane

    n dot x >= h > 0,         |n|=1.                (1)

Then at least one of the three has an **open interior point
on the positive radial ray**

    {t*n : t>0}.                                    (2)

In particular any triple of whole exterior squares served
by the same outward side of the unique central square C
contains a genuine *radial ray-crosser*. This holds even when
h is very small; there is no hypothesis h>=13/60 or any
common square frame.

**Sharp status consequence.** Suppose both double-side
statuses RU and RD occur, and the common R side serves
exactly three whole squares. The remaining R-only square
necessarily crosses the **positive x-axis in its open
interior**. It cannot be the RU or RD square, since those
lie wholly in respectively y>0 and y<0.

## 1. One midpoint slice orders any number of cap squares

Rotate n to (1,0), and write rho for the containing disk
radius (rho²<=98/25, hence rho<2). Every contained square
has horizontal projection of length

    L=|cos theta|+|sin theta|>=1,

regardless of its frame. If a square is in the x>=h cap,
its horizontal projection is [l,r] with

    h<=l,       r<=rho,      r-l=L>=1.

Choose the **same** vertical slice

    X=(rho+h)/2.

Because rho-h<2, we have

    X-l>=L-(rho-h)/2>0,
    r-X>=L-(rho-h)/2>0.

Thus x=X passes through the *open interior* of every
cap square, producing an open vertical interval.
For pairwise interior-disjoint squares, these intervals
have disjoint interiors; their increasing vertical
order is unambiguous. This provides a canonical ordering
of one, two, or three squares in **any** outward cap,
without fixing their orientations or contact points.

The ray-crosser conclusion below is even simpler and
does not require the slice order, but the order supplies
a finite, exact case label for subsequent geometric work.

## 2. Quadrant replication forces a radial crossing

Suppose by contradiction that **none** of the three
square open interiors meets the positive x-axis.

Each square is contained in x>=h>0. Its open interior
is convex and connected, and the y-coordinate of an
open line segment varies continuously. If the interior
had one point with y>0 and another with y<0, the
segment joining them would lie in the open interior
and contain a point at y=0, contradicting the
hypothesis.

Therefore each entire *closed* square is contained
in one of the two **closed origin quadrants**

    {x>=0,y>=0}  or  {x>=0,y<=0}.                  (3)

To include possible boundary points: if the open
interior lies in y>=0, its closure—the whole
square—also lies in the same closed half-plane,
and similarly for y<=0.

The quadrant replication theorem
HUMAN_ORIGIN_SECTOR_REPLICATION.md proves that,
at R²<=98/25, **at most one entire unit square**
can lie in any one origin quadrant. Indeed two
such squares could be rotated by 90,180,270 degrees
to form eight disjoint units without a square
containing zero, contradicting the analytic
eight-square central-square theorem.

Three square labels placed into the **two**
quadrants (3) force two into the same quadrant,
contradicting its capacity one. Thus at least
one square open interior intersects the
positive x-axis. Reflection and rotation give
the arbitrary n conclusion, proving (2).

## 3. Consequences for the surviving macro-branches

**(a) D2, common side triple.** Suppose RU and RD
are occupied by distinct exterior squares,
and the R population is exactly three.
The RU square lies wholly in y>=h_U>0 and
the RD square wholly in y<=-h_D<0.
Neither meets the positive x-axis. The
third R-only square must, by the theorem,
intersect that ray *through its interior*.
This removes the hypothetical subcase
where all three R members stay entirely
above or below that diameter. The same
argument holds for any other shared side.

**(b) Pure single-side S1.** The S1 status type has
two perpendicular triples (after normalization
R and U) and **no** double-side square.
Therefore two **different** exterior squares,
one assigned exclusively R and the other
exclusively U, intersect the positive x-axis
and positive y-axis, respectively. This is
unconditional in their cap offsets, complementing
HUMAN_TRIPLE_CAP_ORTHOGONAL_WITNESSES.md, which
forces whole-quadrant members when the offsets
are >=13/60.

**(c) Saturated Type A.** In SATURATED_SIDE_STATUS_BRANCHES.md,
Type A has 3 R, 1 L, 3 U, 1 D memberships,
one RU double and no corner-only exceptions.
The present theorem forces a radial-crosser
among its R-only members and another among
its U-only members; RU itself cannot cross
either positive coordinate axis.

Moreover both opposite-side singletons L,D
are in caps at distances >17/24 from zero.
The far-cap singleton theorem
HUMAN_TWO_CAP_CENTER_SIGN_SPLIT.md, section 5,
forces the L square to cross the negative
x-axis openly, and the D square to cross
the negative y-axis openly. Consequently
**four distinct exterior squares** cross
the four respective positive/negative
central-frame outward origin rays, one on
each axis. This is a compulsory four-lane
structure, not a proof that Type A is
impossible.

No such crossing-square conclusion implies
that a square shares its frame with C, or
touches C, or is a particular stress vertex.
The sharp eight-square lower bound
R8>=Rhat remains open.
