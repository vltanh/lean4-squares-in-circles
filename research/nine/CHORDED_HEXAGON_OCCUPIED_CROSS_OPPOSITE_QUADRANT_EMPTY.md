# An occupied cross has no extra unit opposite the containing-circle center

Date: October 27, 2026.

**Status: accepted complete uniform geometric theorem after full root and separate independent reviews.**
Reviewed mathematical SHA-256: `c824dd96ba8b9505de653248b9bd99bbf429eb706f84f5288d58657db6f9abf7`. Root review: REVIEW_GENERAL_OCCUPIED_CROSS_NINE_UNIT_ROOT_2026_10_27.md. Separate review: REVIEW_OCCUPIED_CROSS_OPPOSITE_QUADRANT_ROOTED_BLOCKS_2026_10_27.md. No original graph/load gate or ledger
is changed. This source does not claim a complete capacity theorem for
a cross without physical boundary-arm hypotheses.

Put Q=1105/256. Let five actual unit squares form the aligned occupied
cross: one central unit and the four units sharing its four full sides.
All five and every further actual unit lie in a common disk of radius
at most sqrt(Q), with pairwise disjoint open interiors. No force, degree,
load, normal selection or physical circle-contact premise is imposed.

Use the actual cross frame, with its central unit centered at the
coordinate origin. Write o=(o_x,o_y) for the containing-circle center.
The cross is the union of the two closed rectangles

    V=[-1/2,1/2] times [-3/2,3/2],
    B=[-3/2,3/2] times [-1/2,1/2].                    (1)

**Theorem.** No further actual unit can have center (x,y) in a quadrant
weakly opposite o in both coordinates:

    x*o_x<=0,       y*o_y<=0.                         (2)

In particular, every cross has at least one completely empty quadrant
for extra centers. If the circle center lies on one cross axis, both
opposite-side quadrants are empty. If it is the central cross center,
there is no extra unit at all. These statements concern extra units
contained in the stated disk; they do not require any boundary arm.

## 1. Center localization reduces the problem to a northeast unit

Every contained unit has center distance from o strictly less than

    M=91/60,                                         (3)

because its farthest-corner squared radius is at least r^2+r+1/2 and

    M^2+M+1/2-Q=31/57600>0.

Reflect the two cross axes independently so that a putative center
satisfying (2) has x,y>=0 and o_x,o_y<=0. Then

    x^2+y^2 <= |(x,y)-o|^2 < M^2.                    (4)

The open radius-1/2 incircle of the extra unit is disjoint from the
open interiors of both rectangles in (1). If 0<=x<=1/2, its distance
from V can be at least 1/2 only if y>=2, contradicting (4). The same
argument interchanges x,y. Thus x,y>1/2.

Neither can be at least 3/2: that would give
x^2+y^2>9/4+1/4=5/2>M^2. Hence x,y<3/2. The nearest point of V
to the center is now (1/2,y), so incircle separation gives x>=1.
The corresponding argument with B gives y>=1. Therefore

    1<=x,y<3/2.                                      (5)

Every point of the extra unit consequently has both coordinates
positive: its halfwidth in either cross axis is at most 1/sqrt(2)<1.
Since o has nonpositive coordinates, the distance of each such point
from the cross center is no greater than its distance from o. Thus
the entire extra unit is also contained in the origin-centered disk
D_(sqrt(Q)). We may use that necessary containment below, while keeping
the actual cross and extra unchanged.

## 2. The complete separating-axis cover

By the symmetries of a square and, if needed, exchanging the two cross
coordinates, choose the actual extra frame as

    u=(c,s), v=(-s,c),
    c>=s>=0, c^2+s^2=1,
    h=(c+s)/2, k=(c-s)/2.                            (6)

This covers both original tilt signs: exchanging x and y reverses
the tilt modulo the square's own quarter-turn symmetry, and preserves
(1), (4), and (5). The extra's halfwidth in either cross axis is h.

For either rectangle [-ell,ell] times [-m,m], with ell,m>=1/2,
the separating-axis theorem gives a separator on a cross axis or on
one of the actual axes +/-u,+/-v. A normal is directed from the
rectangle towards the extra. The negative cross axes and -u cannot
separate, since their center projections are nonpositive while the
sum of the two positive halfwidths is positive.

The own-axis alternative v=(-s,c) implies

    -s*x+c*y >= ell*s+m*c+1/2.

It implies the ordinary upper cross-axis separation y>=m+h, because

    1+2s(x+ell)-c(c+s)
      =s^2+s[2(x+ell)-c]>=0.                         (7)

Here x>=1 and ell>=1/2. Likewise -v=(s,-c), if it can separate,
implies the ordinary right cross-axis separation x>=ell+h. For s>0
the same calculation after exchanging coordinates is

    1+2c(y+m)-s(s+c)
      =c^2+c[2(y+m)-s]>0;                            (8)

when s=0 the proposed downward normal cannot separate at all.

Thus every possible separator is covered by a positive cross axis
or by the single actual northeast own normal u=(c,s).

For V, upper separation y>=3/2+h is impossible by (5). For B,
right separation x>=3/2+h is impossible. The remaining choices are

    V: x>=1/2+h, or c*x+s*y>=1/2+c/2+3s/2;
    B: y>=1/2+h, or c*x+s*y>=1/2+3c/2+s/2.           (9)

The second B alternative is impossible. Indeed c>=1/sqrt(2)>7/10,
so it would give

    |(x,y)| >= c*x+s*y > 1/2+(3/2)(7/10)
                         =31/20 > M,

contrary to (4). Consequently every actual extra satisfies

    y>=y_0:=1/2+h,                                   (10)

and its V separation is one of the two complete alternatives in (9).
This is a full SAT cover, including all aligned and own-axis endpoints.
No contact between the extra and a cross arm is assumed.

## 3. Both cross-axis separations already require radius squared at least 9/2

First suppose x>=y_0 as well as (10). The actual far corner with
center displacement (k,h) gives the lower radius bound

    Q >= (x+k)^2+(y+h)^2
       >= (1/2+c)^2+(1/2+c+s)^2.                     (11)

The last expression is at least 9/2. To check this on the entire
closed orientation interval, put t=1-c>=0. When s=0 it equals 9/2.
When s>0, we have s<=1/sqrt(2)<4/5 and

    c^2-(1-s/2)^2=s-(5/4)s^2>0.

Both sides being nonnegative, c>1-s/2, so s-2t>0. Therefore

    (1/2+c)^2+(1/2+c+s)^2-9/2
      =3(s-2t)+(s-t)^2+t^2>0.                       (12)

In either case (11) contradicts Q<9/2. This excludes every extra
whose two required separations are ordinary cross-axis separations.

## 4. The complete remaining own-axis alternative gives the same contradiction

It remains the genuine V own-axis condition in (9). Put the actual
center coordinates in the frame (6) as

    U=c*x+s*y,       W=-s*x+c*y,
    U>=U_0:=1/2+c/2+3s/2.                           (13)

If s>=1/2, then c>7/10 gives U_0>8/5>M, impossible. Thus

    0<=s<1/2,       c>sqrt(3)/2>17/20.               (14)

By (5), W>c-(3/2)s>1/10, and U is positive. The actual corner
in the positive u,v directions consequently has squared norm

    (U+1/2)^2+(W+1/2)^2.                            (15)

Equation (10) is y=sU+cW>=y_0, so

    W >= (y_0-sU)/c >0.                             (16)

The strict sign follows from y_0>=1, U<M and s<1/2:
y_0-sU>1-M/2=29/120>0. Thus (15) is at least

    F(U)=(U+1/2)^2+[(y_0-sU)/c+1/2]^2.              (17)

This quadratic is strictly increasing for U>=U_0. Its unique
critical point is

    U_*=s*y_0-(c^2-sc)/2.

Since c>s and y_0<5/4, it satisfies U_*<5/8. But U_0>17/20
by c>7/10. Therefore U>=U_0>U_* throughout the actual domain,
and F(U)>=F(U_0).

The point with own coordinates U_0 and (y_0-sU_0)/c has cross
coordinates

    y=y_0,
    x=x_0:=y_0+(s/c)(1-c).                          (18)

This is just an algebraic evaluation of (17); no new physical unit
or contact is introduced. Its positive u,v corner has coordinates

    x_0+k=1/2+c+(s/c)(1-c) >=1/2+c,
    y_0+h=1/2+c+s.

Consequently

    F(U_0) >= (1/2+c)^2+(1/2+c+s)^2 >=9/2,           (19)

by the already proved complete comparison (12). Equations (15)--(19)
again contradict Q<9/2. This excludes the last possible SAT branch.

## 5. Whole geometric conclusion and limits

Sections 1--4 exclude every actual extra center satisfying (2), for
every orientation and every weak contact with the occupied cross.
There is no physical boundary-arm premise and no force equation.

The theorem leaves the other center quadrants unrestricted. In
particular it does not assert that each other quadrant has capacity
one or that every cross in this radius window has total capacity
eight. The separate complete source
`CHORDED_HEXAGON_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md` has its own
additional premise of two adjacent physical boundary arms and its
own complete capacity proof; that source remains unchanged.

No numerical pose, finite orientation subdivision, normal reselection,
force deletion, Lean compilation, CI, workflow or shared-ledger edit
is used.
