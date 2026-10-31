# A boundary contact with a five-sixths-radius unit leaves no intermediate center

Date: October 27, 2026.

**Status: complete force-free hand theorem, submitted for full root and
separate independent review.** Every center, contact and unit is an
original physical one. The second contact body and the excluded third
body need not touch the circle or carry a positive circle load.

## 1. Exact physical scope

Let A, B and E be three distinct interior-disjoint unit squares
contained in the original circle, where

    sqrt(17)/2<=R<=sqrt(1105)/16.

Suppose A physically touches the circle, A physically touches B, and

    |c_B|>=5/6,       |c_E|>=2/3.

Then the center direction of E does not belong to the closed minor
angular arc from c_A to c_B. Moreover the minor angle between c_A
and c_B is strictly between pi/6 and pi/2.

All orientations, physical circle masks, arbitrary actual contact
points and side intervals are included. No force equation is used.

Put

    M=91/60,       P=27/20,       K=5/6.

The standard actual farthest-corner bound gives |c|<M for every
contained unit. Indeed

    |c|^2+|c|+1/2<=1105/256,
    M^2+M+1/2−1105/256=31/57600>0.

The actual boundary corner of A gives

    |c_A|>=R−1/sqrt(2)>103/50−71/100=P.

The real A--B contact gives |c_A−c_B|<=sqrt(2). Distinct
actual centers are at distance at least one, by their radius-one-half
incircles.

## 2. Both exact angular bounds

First,

    |c_A|^2+|c_B|^2>P^2+K^2>2>=|c_A−c_B|^2,

so the two center vectors have positive dot product. Their minor
angle is strictly less than pi/2.

If that angle were at most pi/6, then sqrt(3)>5/3 would give

    |c_A−c_B|^2
      < x^2+y^2−(5/3)xy,

where x lies in [P,M] and y lies in [K,M]. The right side is
convex in each coordinate separately, so its maximum on this
rectangle is at a corner. The four corner values are

    2311/3600,       9593/10800,
    2557/3600,       8281/10800,

all strictly less than one. This contradicts the actual center
separation. Thus the minor angle is strictly greater than pi/6.

## 3. The unchanged weighted-distance identities

Suppose the ray through c_E lies on the closed minor arc. It meets
the actual center segment at

    Y=t c_A+(1−t)c_B=y v,
    c_E=rho v,       |v|=1,       0<=t<=1.

Here y>0 and 2/3<=rho<M. Put

    V=t(1−t)|c_A−c_B|^2,       0<=V<=2t(1−t)<=1/2.

The two actual variance identities are

    y^2+V=t|c_A|^2+(1−t)|c_B|^2<M^2,                 (1)

    t|c_A−c_E|^2+(1−t)|c_B−c_E|^2
       =(y−rho)^2+V.                                  (2)

The left side of (2) is at least one. We show the right side is
strictly less than one, retaining t=0 and t=1.

If rho<=y, (1) gives

    (y−rho)^2+V
      <=M^2+rho^2−2rho sqrt(M^2−V)
      <=M^2+rho^2−2rho sqrt(M^2−1/2).

This is the same convex quadratic used in
BOUNDARY_CONTACT_EXCLUDES_INTERMEDIATE_UNIT_CENTER.md.
At rho=2/3 it is strictly below 3481/3600, since
sqrt(M^2−1/2)>4/3. At rho=M it is

    M/[M+sqrt(M^2−1/2)]<1.

It is consequently below one throughout [2/3,M].

For rho>=y define the exact lower weighted radial bound

    S=tP^2+(1−t)K^2.

Then y^2>=S−V, and S−V>=K^2−1/2>0. Because rho<M
and y<M, the right side of (2) is bounded above by

    (M−sqrt(S−V))^2+V
       =M^2+S−2M sqrt(S−V)
       <=M^2+S−2M sqrt(S−2t(1−t)).                    (3)

It remains to prove that the last expression is below one.
Both sides of the equivalent square comparison are positive.
Its exact difference is the quadratic

    4M^2[S−2t(1−t)]−(M^2+S−1)^2
      =385719/160000
       −(27050053/2160000)t
       +(222001079/12960000)t^2.                       (4)

Completing the square, its minimum on the whole real line is

    24353087759/199800971100>0.                         (5)

Thus (3) is strictly below one. This contradicts (2) in the
second case as well, and proves the complete closed-arc exclusion.

The arithmetic in (4)--(5) is an exact quadratic identity, not a
numerical optimization or sampled check.

## 4. Exact physical path export

Consider an actual four-body path

    B_1--B_2--X--B_4,

where B_1,B_2,B_4 physically touch the circle and |c_X|>=5/6.
Suppose all other actual bodies under consideration have center
norm at least 2/3. For the first edge use the complete boundary-pair
theorem BOUNDARY_CONTACT_EXCLUDES_INTERMEDIATE_UNIT_CENTER.md;
for the other two use this theorem.

No other center can occur on any of the three closed minor edge
arcs. In particular, at each internal path vertex its two neighbors
lie on opposite angular sides. Otherwise, because both edge arcs
are shorter than pi/2, the nearer neighbor direction would lie on
the other edge's forbidden minor arc. The three arcs therefore
continue in one circular orientation.

Their total length is less than

    2pi/5+pi/2+pi/2<2pi.

Here the boundary--boundary edge has the original strict upper
bound 2pi/5. The original boundary-center separation gives its
strict lower bound 2pi/9; Section 2 gives pi/6 for each of the
other two. Thus the complete path span is strictly greater than

    2pi/9+pi/6+pi/6=5pi/9.                              (6)

If a distinct actual radial leaf has center radius at least 2/3,
its center direction belongs to none of the three edge arcs.
Cutting there and choosing the path orientation gives four strictly
ordered lifts in (0,2pi). Every other actual center of radius
at least 2/3 is outside their whole traversed interval.

A caller that uses complete circle-intersection arcs must still
establish their connectedness and center-point property. This
source states an angular center theorem; it does not replace an
actual square by its center or infer a new circle load.

No physical square, original normal, application mean, positive
force, zero circle weight, shared metadata or remote state is changed.

