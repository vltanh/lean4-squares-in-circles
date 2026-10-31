# Four near-origin physical units allow at most eight units in the circle

Date: October 27, 2026.

**Status: accepted complete hand proof at its stated original scope; full root and separate independent source/scope reviews passed.**

Accepted reviews: REVIEW_FOUR_NEAR_ORIGIN_CAPACITY_LEAF_PAIR_2026_10_27.md and
REVIEW_NEAR_ORIGIN_AND_ATTACHMENT_CLOSURES_ROOT_2026_10_27.md.
Their mathematical-source pins precede this acceptance-only header update. No original gate or central ledger is changed.

Keep all actual interior-disjoint closed unit squares in the radius-R disk,
where

    R <= sqrt(1105)/16.

The squares may have arbitrary orientations, physical contact graphs,
circle masks, positive degrees and force systems. Suppose four distinct
physical squares each meet the closed disk D_(1/60) about O.

**Theorem.** There are at most eight physical unit squares in total.
Consequently such four units cannot occur in the original nine-square
problem. This is a force-free physical capacity theorem; it deletes or
changes no certificate data.

## 1. Exact center bounds and their separation

Every unit contains its open radius-1/2 incircle. Thus the centers of any
two distinct physical units have Euclidean distance at least one.

If c is a unit center and u,v its orthonormal side axes, its farthest
corner has squared norm

    |c|^2 + 1/2 + |c.u| + |c.v|
      >= |c|^2 + 1/2 + |c|.

Circle containment therefore gives

    |c| <= sqrt(R^2-1/4)-1/2 < M,       M=91/60.          (1)

The strict final bound is the exact upper-window inequality
sqrt(1041)/16<121/60, obtained by squaring positive quantities.

If a unit meets D_(1/60), its center is within distance 1/sqrt(2)
of that actual point. Hence its center satisfies

    |c| <= 1/sqrt(2)+1/60 < a,          a=76/105.         (2)

Indeed a-1/60=99/140 and 99^2=9801>9800=140^2/2.

Let c_1,c_2,c_3,c_4 be the four named centers. Each is nonzero: a zero
center would be at distance less than a<1 from the other named centers.
Their directions are distinct by the same separation. Define

    C=1-1/(2a^2)=527/11552,
    delta=arccos(C),
    p=48/73.                                            (3)

All constants in this source are fixed rational bounds or angles defined
from them; no sampled configuration enters the argument.

## 2. Four central directions and a lower bound on every central radius

The smaller angular separation of any two central directions is strictly
greater than delta. To verify this, fix an angle theta<=delta. For radii
r,s in [0,a], the squared distance r^2+s^2-2rs cos(theta) is separately
convex in r and s, so its maximum is at a corner of that rectangle.
The four values are 0,a^2,a^2,2a^2(1-cos(theta)), all at most one.
For the actual strictly smaller positive radii in (2), the value is
strictly less than one. This contradicts the center separation.

List the four directions cyclically and let gamma_i be their consecutive
positive angular gaps, whose sum is 2pi. Each gap is greater than delta;
therefore every gap also satisfies

    gamma_i < G,             G=2pi-3delta.               (4)

At any one central direction, the sum of its two adjacent gaps is less
than 2pi-2delta, because the other two gaps exceed delta. Thus at least
one of its two neighbors has angular distance theta<pi-delta.

Let r be this center's radius and s<a the selected neighbor's radius.
Since cos(theta)>-C and C>0, their distance satisfies

    1 <= |c_i-c_j|^2
       < r^2+a^2+2raC.

But the exact rational identity is

    1-(p^2+a^2+2paC)=362639/1116292275 > 0.              (5)

The expression in r on the right is increasing for r>=0. Equation (5)
therefore forces

    p < |c_i| < a,             i=1,2,3,4.               (6)

This lower radius bound uses the entire four-center angular cover,
including every possible asymmetry among the four physical units.

## 3. Every further center lies strictly outside the unit disk

We first record elementary coarse angle bounds. Since

    0<C<1/4<cos(5pi/12),

we have 5pi/12<delta<pi/2 and consequently G<3pi/4.
Every direction therefore lies at angular distance less than 3pi/8
from one of the four central directions, by (4).

Also

    a < 2 cos(3pi/8)=sqrt(2-sqrt(2)).                    (7)

For example a^2<4/7<2-sqrt(2), using sqrt(2)<10/7,
proves (7) by positive squaring.

Let z be the center of any further unit. Suppose |z|=s<=1, and choose
the central center c with angular separation theta<3pi/8. Its radius
r lies in (0,a). For s in [0,1], the separately quadratic expression

    |z-c|^2=s^2+r^2-2sr cos(theta)

is at most the larger of its endpoint values r^2 and
1+r^2-2r cos(theta). Both are strictly less than one: use a<1 for
the first and r<a<2cos(theta) from (7) for the second. If z=O,
the first endpoint is already the direct contradiction, so no direction
choice is needed. Thus all additional physical centers satisfy

    1 < |z| < M.                                         (8)

## 4. Four short angular sectors contain all further centers

Define the exact rational constant and its angle

    Q=(M^2+p^2-1)/(2Mp)=33239449/38263680,
    alpha=arccos(Q).                                    (9)

For any further center z and any central center c_i, write s=|z|,
r=|c_i|, and let theta be their smaller angular separation. Their
distance at least one implies

    cos(theta) <= (s^2+r^2-1)/(2sr).                     (10)

For fixed r<1 the right side is strictly increasing with s>0, since
its derivative has the positive numerator s^2-r^2+1. Replacing s<M
by M therefore increases it. At fixed M it is strictly decreasing
in r in the interval [p,a], since r^2<M^2-1. Replacing r>p by p
again increases it. Hence (10) gives

    cos(theta)<Q,        theta>alpha.                   (11)

Each further direction thus lies between two consecutive central
directions, at distance greater than alpha from both endpoints.
There are at most four such remaining angular sectors. By (4), each
has width strictly less than

    w=2pi-3delta-2alpha.                                (12)

The exact rational comparisons Q^2>3/4 and Q<7/8 show
pi/8<alpha<pi/6. Together with the bounds on delta in Section 3,
these give

    pi/6 < w < pi/2.                                    (13)

The next exact inequality is the quantitative point of the proof:

    cos(w) > T,               T=1-1/(2M^2)=6481/8281.  (14)

Here is a complete rational verification, without a decimal angle
estimate. Put

    A=(4C^3-3C)(2Q^2-1),
    B=2Q(1-4C^2),
    K=(1-C^2)(1-Q^2).

The trigonometric addition formulas and (12) give

    cos(w)=A+B sqrt(K).

All of B,K,T-A are strictly positive: 0<C<1/4, 0<Q<1,
2Q^2-1>0 and A<0. At the exact rational values (3),(9), direct
fraction multiplication gives the identity

    B^2 K-(T-A)^2
      = 212838658184275860130098266447348906558891
        /296531047841154208394844776497444772904960000
      >0.                                               (15)

Positive squaring of (15) proves B sqrt(K)>T-A, which is (14).
This displayed integer comparison is a uniform rational identity in
the fixed constants, not an interval check on an unproved pose family.

## 5. Each sector contains at most one further unit center

Take two hypothetical further centers in one remaining sector. Their
angular separation is less than w<pi/2. By (14) the cosine of that
separation exceeds T. Their radii lie between 1 and M by (8), so
their squared distance is strictly less than

    f(s,t)=s^2+t^2-2stT,             1<=s,t<=M.

This expression is separately convex, so its maximum on the rectangle
is at a corner. The four corner values satisfy

    f(1,1)=2(1-T)<1,
    f(M,M)=2M^2(1-T)=1,
    f(1,M)=f(M,1)=1+M^2-2MT<1.

For the last strict inequality use the exact rational comparison

    T-M/2=24149/993720>0.

Thus the actual two-center distance would be strictly less than one,
contradicting their disjoint open unit incircles. Each of the at most
four sectors contains at most one further center. There can therefore
be at most four further units in addition to the four named units,
for a total of at most eight.

All nine original units, if present, enter this physical count. No
positive graph is reduced, no physical unit is moved, and no force,
normal, side mean, boundary mask or individual corner weight is changed.
The proof uses no Lean compilation, CI, floating-point premise or
numerical pose certificate.
