# A central tilted S root and a four-body boundary path leave room for at most two extras

Date: October 27, 2026.

**Status: complete force-free hand capacity theorem, submitted for full
root and separate independent review.** This excludes the entire
high-radius C5 S1234 domain whose tilted root has longer radial
coordinate at most 4/5. No endpoint force, circle-weight ratio,
contact owner or numerical pose is prescribed.

## 1. Actual six-body geometry and the whole capacity statement

Retain the same original nine interior-disjoint unit squares in the
closed circle, with

    sqrt(17)/2<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,       1<=d<61/60,
    r=R-sqrt(2).

Suppose six distinct actual squares are H,L,B_1,B_2,B_3,B_4.
The root and its real radial S leaf have the exact own-frame chart

    H=[U-1,U] times [V-1,V],
    P=(U,V),       U>=V>0,       U^2+V^2=d^2,
    U<=4/5,
    e=(U,V)/d,       f=(-V,U)/d,
    L=P+[0,1]e+[-1/2,1/2]f.                            (1)

All four B_i physically touch the original containing circle.
Their actual physical contacts are

    H--B_1--B_2--B_3--B_4--H.                            (2)

Any additional zero-stress contacts remain allowed, as do all
physical circle masks and every frame of the B_i.

**Theorem.** At most two further arbitrary unit squares can be
added to these six inside the same circle. In particular the
original three completion units cannot all exist.

The proof uses the actual root and leaf shapes, the real path
contacts and circle containment. It uses no force equation at
any body, no canonical minimizer and no post-extraction change.

## 2. Every other unit has one complete forty-degree inner arc

From (1),

    V^2=d^2-U^2>=1-16/25=9/25.

Hence

    3/5<=V<=U<=4/5.                                    (3)

All four own side margins of H are at least 1/5. Thus H
contains the closed disk D_(1/5). Every other actual closed
unit E has

    dist(O,E)>=1/5.

Indeed a point of E in the open disk would lie in int(H),
and a neighboring point of int(E) would give interior overlap.
The actual radius-1/2 incircle also gives

    |c_E|>=7/10>2/3.                                   (4)

Set

    rho=9/8,       delta=2pi/9.

The complete accepted
FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md applies,
since the clearance in (4) is strictly greater than 1/8.
Every one of L, all four B_i, and each further unit therefore
meets the radius-rho circle in a **single connected open
interior arc longer than delta**, containing the radius-rho
point in its actual center direction.

These actual arcs are pairwise disjoint. Each open arc of a
further unit avoids the entire closed circle intersection of
each of the six given units: a point interior to one square
cannot belong even to the closed boundary of another square
without neighboring interior overlap. This observation retains
all tangencies and all circle-arc endpoint degeneracies.

## 3. Every boundary-neighbor center is within one hundred degrees of the leaf

Let T be any physical boundary unit touching H, and choose an
actual point p in H intersect T. This point lies on the
boundary of H. Every point of a physical boundary unit has
norm at least r. The exact original radius bound gives

    r^2>=25/4-sqrt(34)>419/1000,

using sqrt(34)<5831/1000.

If p is on the north or east side of H, its distance to P is
at most one. If it is on the west side, its first coordinate
is U-1, with absolute value at most 2/5. Consequently

    p_y^2>=r^2-(U-1)^2>259/1000>1/4.

Its height is at least V-1>=-2/5, so p_y>1/2.
By (3),

    0<=V-p_y<3/10,
    |P-p|^2=1+(V-p_y)^2<109/100<(21/20)^2.

The south side is identical with x and y interchanged. These
four sides cover every corner and every possible shared-side
application. Thus, uniformly,

    |P-p|<21/20,
    |c_T-P|<=|c_T-p|+|p-P|
             <1/sqrt(2)+21/20<9/5.                    (5)

Every boundary center has norm greater than 27/20. One exact
verification is

    R>=sqrt(17)/2>103/50,
    1/sqrt(2)<71/100,
    |c_T|>=R-1/sqrt(2)>27/20.                          (6)

Let phi in [0,pi] be the minor angle from the actual leaf
direction e to c_T. If cos(phi)<=-1/6, then d>=1 and (6)
give

    |c_T-P|^2
      =|c_T|^2+d^2-2d|c_T|cos(phi)
      >(27/20)^2+1+(1/3)(27/20)
       =1309/400>81/25,

contradicting (5). The last reserve is 13/400. Therefore

    cos(phi)>-1/6,       phi<5pi/9.                    (7)

For the final angular comparison, sin(pi/18)>1/6 follows
from sin(pi/6)=1/2 and the increasing function 3x-4x^3
on [0,1/2]: its value at 1/6 is 13/27<1/2.
Thus cos(5pi/9)=-sin(pi/18)<-1/6, proving (7).

In particular the two endpoint centers c_(B_1),c_(B_4)
both satisfy this strict one-hundred-degree bound. No force,
endpoint degree, proper concurrence or circle multiplier was
used in this complete physical estimate.

## 4. The actual boundary path leaves all extra centers in the leaf gap

Use the established physical angular-neighbor theorem
CIRCLE_CONTACT_ANGULAR_ORDER.md. The three successive actual
boundary contacts in (2) traverse center directions in one
common circular orientation. At an internal path body its two
distinct boundary neighbors occupy its two neighboring positions;
a reversal would revisit the preceding body. Each contact
uses its minor consecutive center gap, shorter than 2pi/5.
The total three-edge span is therefore less than 2pi.

The actual boundary leaf L is not on this path. Its center
direction cannot lie between either touching pair. After
reflection if necessary, cut angles at e and choose lifts

    0<beta_1<beta_2<beta_3<beta_4<2pi.                  (8)

The beta_i are the original B_i center directions. Distinct
physical boundary centers are more than delta apart by
CENTERED_INNER_ARC.md, so

    beta_4-beta_1>3delta=2pi/3.                         (9)

Equation (7) puts each endpoint in the union

    (0,5pi/9) union (13pi/9,2pi).

Both endpoints cannot lie in the same one of these intervals,
since each has length 5pi/9<2pi/3 and (9) holds. Their order
in (8) therefore forces

    beta_1<5pi/9,       beta_4>13pi/9.                 (10)

Now use the complete force-free theorem
BOUNDARY_CONTACT_EXCLUDES_INTERMEDIATE_UNIT_CENTER.md.
By (4), every actual further unit center has norm greater
than 2/3. None can lie on the closed minor angular arc
between B_i and B_(i+1), for any i=1,2,3. The union of
these actual gaps is exactly the interval in (8).
Therefore every further center lies in

    (0,beta_1) union (beta_4,2pi).                      (11)

This step applies to physically clear completion units as
well as to boundary ones. It does not falsely assign them
a circle load or a boundary-center annulus. Its proof uses
their actual center distances and the original B_i--B_(i+1)
contacts.

## 5. The real leaf splits that gap into two intervals of capacity one

The actual closed radius-rho intersection of L is symmetric
about e and has half-width

    alpha=min(arccos(d/rho), arcsin(1/(2rho)))
          =min(arccos(8d/9), arcsin(4/9)).              (12)

The radial outer side is inactive because d+1>rho.
The two inequalities in (12) are exactly the original
inner-side and transverse-side conditions, so no subarc
or frame model is substituted for the real leaf.

Both entries in the minimum are strictly greater than pi/9.
Indeed

    d/rho<122/135<15/16<cos(pi/9),

where the last inequality follows by comparing
4(15/16)^3-3(15/16)=495/1024<1/2 with cos(pi/3).
Also sin(pi/9)<sqrt(31)/16<4/9. Thus

    alpha>pi/9=delta/2.                                (13)

Take any further actual square E. Its single open radius-rho
arc from Section 2 contains its own center direction. If that
direction belongs to the first interval in (11), the whole
arc lies in

    (alpha,beta_1).

To leave this interval it would have to cross either the
closed occupied leaf arc or the radius-rho point in the
open interior of B_1 at angle beta_1. Both are forbidden
by actual disjoint interiors and connectedness. Likewise,
a center in the second interval has its whole arc in

    (beta_4,2pi-alpha).

The two enclosing intervals have respective lengths strictly
less than

    5pi/9-pi/9=4pi/9=2delta,                            (14)

by (10) and (13). These are enclosing intervals; the actual
B_1,B_4 arcs and any further physical contacts can only
shorten them.

Each further square contributes a disjoint open arc longer
than delta. Two such arcs cannot fit in either interval of
(14). Hence there is at most one further unit in each interval,
and at most two further units in total. This proves the
capacity theorem, including all weak contact and containment
endpoints.

## 6. Exact original S1234 consequence

In the original positive C5 component with one genuine S leaf,
all four nonroot bodies loaded, and true root degree three,
the actual graph is precisely (2) plus HL. A tilted root can
be oriented as (1), with U>=V>0. Whenever d>=1 and U<=4/5,
all physical hypotheses of this theorem hold. Its original
packing has three further units, not two. The entire domain
is therefore excluded.

This conclusion retains every original force, mean and circle
mask simply because none is modified or specialized in the
physical proof. Together with the separately complete ordered
root theorem for U>4/5, it covers the full high-radius tilted
S1234 root, once the two direct sources and their exact join
receive their full reviews. The aligned and strict-low
domains remain separate obligations for the complete family.

The theorem does not assert a uniform three-near-unit capacity
bound or any force-only contradiction for an unrealized core.
It uses its actual four-body boundary path at exactly the point
where (8)--(11) are established. It may not be transferred to
a path containing an unloaded or physically clear intermediary.

No shared metadata, original pose, selected normal, actual mean,
remote state, compilation or CI is changed.

