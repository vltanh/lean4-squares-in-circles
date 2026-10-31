# A boundary contact cannot pass an intermediate unit center of radius at least two thirds

Date: October 27, 2026.

**Status: complete force-free hand theorem, submitted for full root and
separate independent review.** All centers are actual physical centers;
the third unit need not touch the circle, carry load, or have any
specified degree.

Work with actual interior-disjoint unit squares contained in the original
circle, with

    79/40<=R<=sqrt(1105)/16,       M=91/60.

Let A and B physically touch the circle and physically touch each other.
Let E be a distinct actual unit whose center satisfies |c_E|>=2/3.

**Theorem.** The center direction of E is not on the closed minor angular
arc between c_A and c_B.

## 1. Unchanged physical center bounds

The standard farthest-corner formula gives every contained unit center c

    |c|^2+|c|+1/2<=1105/256.

Since M^2+M+1/2 exceeds 1105/256 by 31/57600,

    |c|<M.                                                (1)

The two physical boundary centers have

    |c_A|,|c_B|>5/4.                                       (2)

This follows from |c_A|>=R-1/sqrt(2), and the original lower
radius bound, exactly as in CIRCLE_CONTACT_ANGULAR_ORDER.md,
Section 1. Distinct unit centers are at distance at least one
by their actual radius-1/2 incircles. The real A--B contact gives

    |c_A-c_B|<=sqrt(2).                                    (3)

Their minor center angle is strictly below pi, and in fact below
2pi/5 by the complete physical angular-neighbor theorem. No
circle or force premise is assigned to E.

## 2. One exact weighted-distance calculation

Suppose its direction lies in the closed minor arc. The ray through
c_E then meets the actual center segment at a point

    Y=t c_A+(1-t)c_B,       0<=t<=1,
    c_E=rho v,       Y=y v,       |v|=1.

Put

    V=t(1-t)|c_A-c_B|^2,       0<=V<=1/2.

The two exact variance identities are

    y^2+V=t|c_A|^2+(1-t)|c_B|^2<M^2,                      (4)

    t|c_A-c_E|^2+(1-t)|c_B-c_E|^2=(y-rho)^2+V.           (5)

Every squared distance on the left of (5) is at least one.
Its left side is consequently at least one, including t=0 or t=1.
We now show its right side is strictly below one.

If rho<=y, then (4) gives y<sqrt(M^2-V), and hence

    (y-rho)^2+V
      <=M^2+rho^2-2rho sqrt(M^2-V)
      <=M^2+rho^2-2rho sqrt(M^2-1/2)=:F(rho).             (6)

Here 2/3<=rho<M. The quadratic F is convex, so its maximum
on [2/3,M] is attained at an endpoint. Since

    M^2-1/2=6481/3600>16/9,

the first endpoint satisfies

    F(2/3)<M^2+4/9-16/9
           =3481/3600<1.                                (7)

At the other endpoint rationalization gives

    F(M)=2M[M-sqrt(M^2-1/2)]
         =M/[M+sqrt(M^2-1/2)]<1.                         (8)

Thus (6) is strictly below one throughout this first case.

If rho>=y, then (2)--(4) instead give

    y^2>25/16-V>=17/16>1.

Together with rho<M this yields

    (rho-y)^2+V<(M-1)^2+1/2
                =2761/3600<1.                           (9)

Both cases contradict (5). This proves the theorem, including a
third center exactly on either endpoint ray.

## 3. Exact path export

Suppose B_1,...,B_k form an actual physical path of boundary units
in the established consecutive circular order, and every other
unit under consideration has center norm at least 2/3. Each
minor center gap between B_i and B_(i+1) contains none of those
other center directions, by the theorem. Therefore no such
center lies on the open angular interval traversed by the
whole boundary path. The conclusion includes physically clear
units and makes no statement about their circle weights.

For example, if another actual root contains the closed disk
D_(1/5), every distinct unit E avoids its open interior and has
dist(O,E)>=1/5. Its actual radius-1/2 incircle then gives
|c_E|>=7/10>2/3. The path theorem applies to all those units.

The theorem is a statement about actual center directions. It
does not itself locate the entire physical units in a pocket,
nor assert that a whole circle-intersection arc lies in a free
gap. A caller using an inner-circle capacity must separately
establish connectedness and the center-point property of each
actual arc. Those hypotheses are kept explicit in the C5 caller.

No pose, separating normal, circle mask, force, actual mean,
shared metadata, compilation, CI or remote state is changed.

