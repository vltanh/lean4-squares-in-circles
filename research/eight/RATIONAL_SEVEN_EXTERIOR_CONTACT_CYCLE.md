# Seven exterior unit squares form an exact winding contact ring below the rational n=8 ceiling

## Theorem — an exact hand-checkable counterexample to a ring-only lower bound

Seven unit squares with pairwise disjoint open interiors, all
**avoiding the disk origin even in their closed sets**, fit in

    D_R,     R^2 = 1957/500 = 3.914,

and their actual-contact graph contains the complete cyclic ring

    0--1--2--3--4--5--6--0.

The polygonal contact path traversed in this order winds **once
positively around the origin**. Every consecutive pair really
shares a boundary point; all fourteen nonconsecutive pairs have
**strictly disjoint closed sets**. Every square lies strictly
inside the stated disk.

The squared radius 1957/500 is **strictly smaller than**
the established rational eight-square upper ceiling

    9789/2500 - 1957/500 = 1/625 > 0.

It is also numerically smaller than the Cantrell candidate
squared radius, approximately 3.9155341375. The latter
strict comparison is not used in the theorem: the present
purely hand-analytic family enclosure alone is too coarse
to certify it. The construction contains **seven**, not eight,
squares and therefore is not a counterexample to the
eight-square conjecture.

It proves something important about the remaining sharp
lower-bound route: a seven-exterior-square *contact ring
by itself*, even with positive winding and genuine edge
contacts, cannot be assumed to satisfy the eight-square
radius obstruction from disk containment alone. The
eighth central square and its separation constraints
must be retained in any general ring argument.

## 1. Rational centers and exact unit frames

Put

    c=99/101, s=20/101, e=(c,s), f=(-s,c),
    W=(1+c+s)/2=110/101,
    alpha=-23/40, beta=37/250, gamma=129/500.

The orthonormal identity is 99^2+20^2=101^2.

Squares 0 and 1 have side frame ((1,0),(0,1)).
Squares 2 through 6 have side frame (e,f).
Define their centers p_i recursively by

    p0=(503/1000,-51/1000),
    p1=(423/500,949/1000),
    p2=(423/500-W,1383/1000),

    p3=p2-e+alpha*f,
    p4=p3-f+beta*e,
    p5=p4-f+gamma*e,

    d=f dot(p0-p2)-alpha+2-W
      =-688131/10201000,

    p6=p5+e+d*f.                                   (1)

Each square is the convex hull of its four actual vertices

    p_i+(epsilon*e_i+eta*f_i)/2,
    epsilon,eta in {-1,1}.

All coordinates are rational. To make independent arithmetic
checks easy, here are the expanded centers:

| i | x_i | y_i |
|---|---|---|
| 0 | 503/1000 | -51/1000 |
| 1 | 423/500 | 949/1000 |
| 2 | -12277/50500 | 1383/1000 |
| 3 | -56027/50500 | 31379/50500 |
| 4 | -38701/50500 | -16641/50500 |
| 5 | -1593/5050 | -63561/50500 |
| 6 | 17466444/25757525 | -1160876491/1030301000 |

## 2. Exact full-circle containment and origin avoidance

For a square with center p and orthonormal frame
(a,b), its farthest squared vertex norm is **exactly**

    Q=|p|^2+1/2+|p dot a|+|p dot b|.               (2)

Its closed set omits the origin provided

    xi=max(|p dot a|,|p dot b|)-1/2>0.             (3)

Substitution of the rational data in (1) into (2)--(3)
gives the following deliberately rounded **strict rational
certificates**. In the two right columns all comparisons
use integers and rational coordinates only:

| Square i | 100000 Q_i is strictly less than | 1000 xi_i is strictly greater than |
|---|---:|---:|
| 0 | 130962 | 2 |
| 1 | 391132 | 448 |
| 2 | 391112 | 903 |
| 3 | 391016 | 464 |
| 4 | 218357 | 316 |
| 5 | 391335 | 671 |
| 6 | 390964 | 738 |

In particular, every Q_i<391335/100000<1957/500
and every xi_i>1/500>0.
Every whole square is contained in the disk because
the disk is convex and contains all its vertices.
The exterior conclusion follows directly from its
own two signed side-frame coordinates, not from
a visual inspection of the ring.

## 3. All seven consecutive contacts are genuine

The first pair 0--1 consists of parallel squares.
Their common horizontal boundary is

    y=449/1000,

and the common x interval has positive length:

    173/500 <= x <= 1003/1000.                    (4)

For pair 1--2, the rightmost vertex of square 2 is

    z12=(173/500,100183/101000).                 (5)

Square 1's left edge is x=173/500, and the
vertex's vertical displacement from its center is

    (z12)_y-(p1)_y=2167/50500,

strictly between -1/2 and +1/2. Thus this is
an actual vertex-to-edge contact.

For the four tilted side contacts 2--3,3--4,4--5,
5--6, their center differences in (1) give,
respectively,

    p3-p2=-e+alpha*f,
    p4-p3=-f+beta*e,
    p5-p4=-f+gamma*e,
    p6-p5= e+d*f.

The separation normals are e,f,f,e.
Each corresponding normal center difference has
absolute value exactly one, and each *transverse*
difference has absolute value strictly below one
since |alpha|,|beta|,|gamma|,|d|<1. Therefore
the two supporting side intervals overlap with
positive length and each pair has a genuine
parallel-edge contact.

Finally, take the bottom-right vertex of square 0,

    z60=(1003/1000,-551/1000).

Its projections in the frame of square 6 satisfy

    f dot(z60-p6)=1/2,
    e dot(z60-p6)=4411557/10201000,

and

    -1/2<4411557/10201000<1/2.

Thus z60 belongs to the **relative interior**
of square 6's positive-f side while also
being a vertex of square 0. It is a genuine
6--0 vertex-to-edge contact.

All seven ring contacts have now been exhibited
as actual points or positive-length side
overlaps. Equal projections have not been
mistaken for physical contacts.

## 4. Nonconsecutive squares have strict rational separating lines

For a pair i,j, and one of their side axes n,
the exact separating-axis margin is

    g_ij(n)=|n dot(p_j-p_i)|
       -( |n dot e_i|+|n dot f_i|
         +|n dot e_j|+|n dot f_j| )/2.            (6)

A strictly positive margin separates the two
**closed** squares. Direct fraction substitution
gives the following exact witnesses. Each displayed
margin is strictly greater than 1/10; the simple
lower bound may be confirmed by clearing the
positive denominators.

| Pair | Chosen axis | Exact g_ij |
|---|---|---|
| 0--2 | f_2 | 2367853/5100500 |
| 0--3 | e_0 | 52857/101000 |
| 0--4 | e_4 | 428983/2040200 |
| 0--5 | f_0 | 11971/101000 |
| 1--3 | e_3 | 227608/255025 |
| 1--4 | e_4 | 1898643/2550250 |
| 1--5 | f_1 | 112971/101000 |
| 1--6 | f_1 | 50826107/51515050 |
| 2--4 | f_4 | 23/40 |
| 2--5 | f_5 | 63/40 |
| 2--6 | f_6 | 8377353/5100500 |
| 3--5 | f_5 | 1 |
| 3--6 | f_6 | 10889131/10201000 |
| 4--6 | e_6 | 129/500 |

Together with the seven actual side or vertex
contacts in section 3, this covers all
C(7,2)=21 unordered square pairs. Every
open interior is disjoint from every other;
exactly the seven listed ring pairs touch.

## 5. Positive winding about the origin

Choose one common contact point for each consecutive
pair in circular order. The following seven
points, respectively belonging to the contacts
0--1,1--2,...,6--0, are all rational:

    z01=(3/5,449/1000),
    z12=(173/500,100183/101000),
    z23=(-8538/12625,202441/202000),
    z34=(-11841/12625,7369/50500),
    z45=(-54631/101000,-40101/50500),
    z56=(3736539/20606020,-2457648013/2060602000),
    z60=(1003/1000,-551/1000).                   (7)

The z23,z34,z45,z56 points are the *midpoints of
the overlapping support-edge intervals* from
section 3. In every square, join its incoming
and outgoing contact points by their straight
chord. Convexity keeps the resulting polygonal
curve within the seven closed squares, and
each square omits zero by section 2.

The signs of the y coordinates in (7) are

    +,+,+,+,-,-,-.

The only polygon edges crossing the horizontal
line y=0 are z34--z45 and z60--z01.
The first has both endpoint x coordinates
strictly negative, hence its crossing is on
the *negative* x ray. The second has both x
coordinates strictly positive and crosses
the *positive* x ray with y increasing.
Thus, crossing the **positive** x ray,
there is exactly one transversal upward
crossing and no other intersection.
The oriented winding number about zero is +1.
No assumption that the polygon is convex
or a regular heptagon is used.

## 6. Consequence for the eight-square target

The seven-square construction (1) is a full,
positively winding actual-contact ring, fits
strictly below the rational eight-square
construction ceiling, and leaves origin
outside all seven closed squares. The central
unit square is **not** included.

Consequently the existence of such a contact
ring—even combined with the exterior
condition, winding, and all seven contact
equalities—is not enough to derive the
numerical sharp eight-square obstruction
unless the eighth square is kept as a
geometric obstacle.

This pinpoints what the remaining global
ring proof must exploit: a central square
of side one and its **simultaneous separation**
from all seven ring units. The weaker
assertion that the ring surrounds an
unoccupied point at the origin does not
encode that obstacle.

The unrestricted sharp lower bound
R8>=R_hat has **not** been proved by this
counterexample or by any previous
ring-only inequality.
