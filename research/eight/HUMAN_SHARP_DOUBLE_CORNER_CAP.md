# Sharp corner-cap radius and exclusion of opposite double-side corner statuses

## Theorem 1: one arbitrary square wholly beyond two perpendicular half-planes

Let hx,hy>=0. Suppose a unit square S of **arbitrary orientation**
lies entirely in the closed quadrant cap

    {x>=hx, y>=hy}

of a disk centered at the origin with radius R.
Then

    R^2 >= (hx+1)^2+(hy+1)^2.                         (1)

The bound is **sharp**. Equality holds precisely for the
axis-parallel square

    [hx,hx+1] times [hy,hy+1],                        (2)

with its lower-left vertex at (hx,hy), modulo square frame
symmetries. No common frame, contact graph, positive stress,
or numerical search is used.

This theorem is stronger than merely saying that at most
one square fits the origin quadrant, since it gives an
explicit radius penalty for each specified pair of cap offsets.

## 1. Reduce the center to the southwest admissible position

Let theta denote the square's unsigned angle modulo quarter
turns. Reflect x and y across the line x=y if necessary;
the inequality (1) is symmetric in hx,hy. Thus we can
choose its frame with

    e=(c,s), f=(-s,c), c=cos(theta),s=sin(theta),
    0<=theta<=pi/4,  L=c+s,  1<=L<=sqrt(2).

Its horizontal and vertical half-widths are L/2, so
the square center (x,y) must obey

    x>=hx+L/2,  y>=hy+L/2.                           (3)

Keep the frame but reduce the center coordinatewise to

    p0=(hx+L/2,hy+L/2).

All vertices of the resulting square S0 lie in the first
quadrant, since its leftmost and bottommost coordinates
are hx and hy, both nonnegative.

Each actual vertex of S is obtained from the corresponding
vertex of S0 by the same coordinatewise **nonnegative**
shift (x,y)-p0. Thus neither coordinate of any vertex
decreases, and both are initially nonnegative. Therefore
each squared vertex norm can only increase. Consequently

    max_(v vertex S) |v|^2 >= max_(v vertex S0) |v|^2. (4)

No simultaneous motion of other packing squares is
asserted; this is a one-square containment comparison.

## 2. Two actual vertices and an exact nonnegative average

Among the four true vertices of S0, select

    V_T=(hx+c,hy+L),     V_R=(hx+L,hy+s).            (5)

Put

    Q_axis=(hx+1)^2+(hy+1)^2,
    Q_T=|V_T|^2,  Q_R=|V_R|^2.

These are **actual** square vertices, not independently
maximized x and y coordinates.

Choose the coefficients

    alpha=(1-s)/c = c/(1+s),   beta=1-alpha.

They obey 0<alpha<=1 and 0<=beta<1 for
0<=theta<=pi/4. The identity c^2+s^2=1
gives, after expanding Q_T and Q_R,

    alpha*Q_T+beta*Q_R-Q_axis
       = [2*hx*(1-c)*(1-s)
          +s*(1-s)+c^2*(1-c)]/c >=0.               (6)

Every term in the numerator is nonnegative, since
hx>=0 and c,s in [0,1]. If theta>0, then s>0,
0<s<1, so s*(1-s)>0. Thus (6) is **strict**
for every non-axis-parallel square.

Since alpha,beta form convex weights,

    max(Q_T,Q_R)>=alpha*Q_T+beta*Q_R>=Q_axis.      (7)

Equations (4) and (7) establish (1).
For theta>0 the inequality is strict, so equality
forces theta=0 up to square symmetries. At theta=0
the farthest vertex is the northeast corner
(x+1/2,y+1/2). Equality in (1), with
x>=hx+1/2, y>=hy+1/2, forces both coordinates
to attain their lower bounds; this is exactly
square (2). It achieves equality by direct
vertex calculation. QED.

The decisive identity (6) was discovered/tested by
symbolic algebra, but the proof itself is the
displayed two-vertex expansion and the signs of
its three elementary nonnegative terms.

## Theorem 2: opposite central double-side statuses are impossible

Assume eight unit squares fit a disk with squared
radius

    q=R^2 <=q_plus=9789/2500<9/2,

and let C be the unique square whose open interior
contains the disk center. Work in its own horizontal
and vertical frame, with center p_C=(a,b),
|a|,|b|<1/2.

A square served by both the **right** and **upper**
outward central-owned side separators lies entirely
in the corner cap

    x>=a+1/2,   y>=b+1/2.

Theorem 1, applied with hx=a+1/2>0,
hy=b+1/2>0, forces

    q >= (3/2+a)^2+(3/2+b)^2.                    (8)

Likewise a square served by the opposite **left**
and **lower** central sides forces

    q >= (3/2-a)^2+(3/2-b)^2.                    (9)

If both distinct corner statuses RU and LD were
occupied, adding (8) and (9) and dividing by two
would give

    q >=9/2+a^2+b^2 >=9/2 >q_plus,              (10)

a contradiction. Thus RU and LD cannot both occur.
Reflecting vertically gives the second exclusion:

    RD and LU cannot both occur.                        (11)

Among four adjacent-side statuses RU,RD,LU,LD,
any three distinct statuses contain one of these
two opposite pairs. Hence **at most two**
of the four double-side statuses can occur in
an eight-square packing under the search ceiling;
if two occur, they must be adjacent corners
sharing one central side (for example RU and RD).

This sharpens the older quadrant sector-capacity
result, which gave at most one square *per*
double-side status but did not exclude two
**opposite** statuses.

## Theorem 3: a pair of adjacent double-side statuses forbids 2+2 on their common axis

Suppose both RU and RD occur, so two distinct squares
are wholly beyond the positive **right** central side,
and one beyond each of its upper and lower sides.
By Theorem 1, the two require

    q >= (3/2+a)^2 + (3/2+b)^2,
    q >= (3/2+a)^2 + (3/2-b)^2.

Taking the larger right-hand side gives

    q >= (3/2+a)^2 + (3/2+|b|)^2
      >= (3/2+a)^2+9/4.                           (12)

At q<=q_plus<2257/576, this implies

    a < -5/24,                                       (13)

since a>=-5/24 would make
(3/2+a)>=31/24 and hence
q>=(31/24)^2+9/4=2257/576.

But if **two whole exterior squares** also lay
beyond the opposite *left* central side,
HUMAN_EXTENDED_TWO_SQUARE_CAP.md would give

    |a|<5/24

by the 2+2 opposite-side pruning theorem in
PATTERN_REJECTION_MATRIX.md. That contradicts (13).

Therefore in the RU+RD double-status branch
there are at most **one** whole square beyond
the left central side. Reflection and quarter
turns give all four versions: two double-side
statuses sharing a signed central side forbid
a population of two on its opposite side.

## 4. Numerical-free diagonal offset condition for one double corner

Equation (8) expands to

    q>=9/2+3*(a+b)+a^2+b^2.

Since a^2+b^2>=0 and q<=q_plus,
a square of status RU necessarily forces

    a+b <=(q_plus-9/2)/3=-487/2500.              (14)

In fact strict inequality holds because the
central center (a,b) cannot be (0,0) while
the right-hand side is negative.

The other three double corners have analogous
signed constraints:

    RU:  a+b < -487/2500,
    RD:  a-b < -487/2500,
    LU: -a+b < -487/2500,
    LD: -a-b < -487/2500.                           (15)

These are orientation-free *necessary inequalities*
for the central square's location. Two opposite
ones add to 0< -974/2500 and are immediately
impossible, recovering Theorem 2.

They are **not** sufficient for realizing any
double-side status; the full square must still
fit the disk, avoid the other seven squares,
and satisfy its actual separating-axis branch.

## 5. Remaining global gate

At the n=8 search ceiling there are now at most
two populated double-side statuses, and they
must share a central side. Their central-center
position is quantitatively forced away from
that side, excluding the opposite 2+2 cap
population. These rules eliminate many
12-status assignment patterns entirely and
apply to arbitrary square frames and contacts.

The one-square corner-cap theorem is exact and
orientation-independent but does **not** force
the seven-exterior contact ring, two aligned
end squares, or the five-corner projected
inequalities. Central corner-owned separators
and all surviving mixed side populations
remain genuine branches; no unrestricted
conclusion R8>=Rhat is claimed.
