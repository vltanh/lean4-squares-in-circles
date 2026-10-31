# A radial side point forces every boundary neighbor beyond the near support for the full radius range

Date: October 28, 2026 UTC. Author: house continuation.

**Status: complete proposed force-free hand theorem, submitted for full root and separate independent review.** This removes the high-radius restriction from the radial-side boundary-neighbor half-plane theorem. It uses no force, degree, support-owner, normal-selection, concurrence, circle-weight or other-square premise.

The geometric statement is stronger than its boundary-neighbor application: it proves that every square in the alleged violating position is strictly inside the circle, by a complete convex reduction in two actual own-frame coordinates.

## 1. Exact theorem and full physical scope

Let d be any real number with

    d>1/sqrt(2),
    R=sqrt((d+1)^2+1/4).

Let n,f be any orthonormal frame about the fixed circle origin. Let E be an actual closed unit square. Suppose E contains an actual point Q satisfying

    Q.n>=d, Q.f=1/2.                                (1)

If E also contains any point with n projection at most d-1, then

    |z|<R for every z in E.                          (2)

In particular, if E is a contained physical boundary unit in D_R, then the whole closed unit satisfies

    z.n>d-1 for every z in E.                        (3)

The same conclusions hold with Q.f=-1/2, by reflecting the f coordinate. The point Q may be any actual point of E, including an unchanged application or an endpoint-valued shared-side mean. No assumption is made about which feature of E contains it.

For every R>=2, the actual value d=sqrt(R^2-1/4)-1 satisfies the theorem's strict threshold. Indeed

    sqrt(15)/2-1>9/10>1/sqrt(2),

as follows from 15/4-(19/10)^2=7/50>0 and (9/10)^2>1/2. There is no upper-radius restriction in the theorem.

If Q is an actual point on either side f=+/-1/2 of a physical radial S square

    [d,d+1]n+[-1/2,1/2]f,

then (1) is automatic for any actual neighboring boundary unit containing that same point. The full physical two-circle mask, either zero individual coefficient, all original forces and the original application remain unchanged. The proof does not require the radial S unit to be present.

## 2. The actual vertical slice contains the fixed lower point

Choose Cartesian coordinates

    x=z.f, y=z.n.

Suppose, for contradiction to (3), that

    min_E y<=d-1.

Write Q=(1/2,q), q>=d. We first prove the purely geometric fact

    P=(1/2,d) belongs to E.                         (4)

The vertical section E intersect {x=1/2} is a nonempty closed interval, since it contains Q and E is convex. Its upper endpoint has height at least d.

Its lower endpoint has height at most min_E y+1. To see this directly for a nonaligned unit, take its unique lowest vertex and its two adjacent vertices. Both edges from the lowest vertex point upward, and each vertical component is at most one. The lower hull of the square consists of those two edges; every point of that lower hull is therefore at height at most min_E y+1. The lower endpoint of every nonempty vertical section lies on that hull. For an aligned unit the lower hull is its horizontal bottom side, and the same assertion holds.

Thus the section's lower endpoint has height at most d, while its upper endpoint has height at least d. This proves (4), including q=d, a section endpoint and equality min_E y=d-1.

The point P is used only for this force-free geometric description. It does not replace Q or any original mean in a force or torque equation; no such equation is used.

## 3. Complete aligned case

If E is aligned with the x,y axes, its vertical height is one. The original q>=d and min_E y<=d-1 force

    min_E y=d-1, q=d.

Because its horizontal unit interval contains x=1/2, every actual point has

    -1/2<=x<=3/2,
    d-1<=y<=d.

Since d>1/2, this implies |x|<=3/2 and |y|<=d. Hence

    |z|^2<=d^2+9/4
         <d^2+2d+5/4
         =R^2,                                     (5)

with strict reserve 2d-1>0. This proves (2) for all aligned frames and every possible horizontal position of the actual mean.

The rest of the proof assumes the square is nonaligned. The aligned case is handled directly rather than discarded through a strict-angle assumption.

## 4. One complete convex parameter triangle for every tilted frame

Let the two actual inward axes at E's unique lowest vertex be

    e=(c,s), g=(-s,c),
    c,s>0, c^2+s^2=1.

By (4), there exist actual u,v in [0,1] such that

    E=P-u*e-v*g+[0,1]e+[0,1]g,
    P=(1/2,d).

The lowest height is d-u*s-v*c. Thus the alleged violation is exactly

    u*s+v*c>=1.                                    (6)

For this fixed actual frame, define

    a=s/(1+c)=(1-c)/s,
    b=c/(1+s)=(1-s)/c.

Both a,b lie strictly between zero and one. The entire closed domain

    0<=u,v<=1, u*s+v*c>=1

is precisely the triangle with vertices

    (u,v)=(1,1), (1,b), (a,1).                     (7)

For each of the four actual corner labels i,j in {0,1}, its position is the affine expression

    Z_ij(u,v)=P+(i-u)e+(j-v)g.

Its squared norm is a convex function of (u,v). Therefore if all four corners at each of the three parameter vertices in (7) have squared norm strictly below R^2, then the same is true at every point of the entire parameter triangle. The strict statement follows because the value at an arbitrary point is at most the corresponding convex combination of three values, all strictly below R^2.

This is a complete analytic convexity reduction, not a sample of square orientations. The original continuous variables c,s remain arbitrary throughout Sections 5 through 7.

## 5. Every corner at (u,v)=(1,1)

At this parameter vertex,

    E=P-e-g+[0,1]e+[0,1]g.

Its entire coordinate ranges are

    1/2-c<=x<=1/2+s,
    d-c-s<=y<=d.

The first gives -1/2<=x<=3/2. The second gives |y|<=d because c+s<=sqrt(2)<2d. Consequently every corner, and indeed every point, satisfies the same strict inequality (5).

The threshold d>1/sqrt(2) is used here to cover the entire actual lower vertical span without an orientation restriction.

## 6. Every corner at (u,v)=(1,b)

Here b=c/(1+s), and the identities

    c-b*s=b, b*c=1-s, c-b=b*s

give the four actual corners

    Z_00=(1/2-b,       d-1),
    Z_10=(1/2+b*s,     d-1+s),
    Z_01=(1/2-b-s,     d-1+c),
    Z_11=(1/2-s*(1-b), d-1+c+s).                    (8)

For Z_00,Z_10,Z_01, each horizontal coordinate lies in [-3/2,3/2] and each height lies in [d-1,d]. Since d>1/2, all three therefore satisfy (5).

For the remaining corner Z_11,

    |(Z_11)_x|<=1/2,
    0<d<= (Z_11)_y=d-1+c+s<d+1.

Here c+s>=1 and c+s<2. Thus

    |Z_11|^2<1/4+(d+1)^2=R^2.                      (9)

Every parameter endpoint b and every tilted orientation has been included in these coordinate comparisons.

## 7. Every corner at (u,v)=(a,1)

Here a=s/(1+c). The four corners are

    Z_00=(1/2+a,       d-1),
    Z_10=(1/2+a+c,     d-1+s),
    Z_01=(1/2+a-s,     d-1+c),
    Z_11=P+(1-a)e.                                 (10)

The last expression uses

    1-c=a*s, s-a*c=a.

The corners Z_00,Z_01 satisfy |x|<=3/2 and |y|<=d, so again satisfy (5).

The two remaining corners require the following exact coupled comparisons.

### 7.1. The lower right corner Z_10

Using a*(1+c)=s, direct expansion gives

    R^2-|Z_10|^2
      =2d*(2-s)-1-c+a-a^2
      =4d-1-(2d*s+c)+a-a^2.                        (11)

Since a in [0,1], the last term is nonnegative. By Cauchy and c^2+s^2=1,

    2d*s+c<=sqrt(4d^2+1).

Consequently

    R^2-|Z_10|^2
      >=4d-1-sqrt(4d^2+1)>0.                       (12)

The final strict inequality holds for d>2/3: both quantities compared before squaring are positive, and

    (4d-1)^2-(4d^2+1)=4d*(3d-2)>0.

Our standing d>1/sqrt(2)>2/3 satisfies it. No radius upper bound is used.

### 7.2. The upper right corner Z_11

Using Z_11=P+(1-a)e and the same identities, direct expansion gives

    R^2-|Z_11|^2
      =4d-(2d+1)c-(2d-1)s+a-a^2.                  (13)

Cauchy yields

    (2d+1)c+(2d-1)s
       <=sqrt((2d+1)^2+(2d-1)^2)
       =sqrt(8d^2+2).

Therefore

    R^2-|Z_11|^2
      >=4d-sqrt(8d^2+2)>0,                         (14)

because d>1/2 and

    (4d)^2-(8d^2+2)=8d^2-2>0.

This covers the final corner for every actual tilted frame.

## 8. Whole-domain conclusion and physical half-plane

Sections 5 through 7 put all twelve corner values at the three vertices of the complete parameter triangle strictly inside D_R. Section 4's convexity then puts every actual corner of the original E strictly inside D_R. Convexity of the disk, or the maximum of the squared norm on the actual unit, gives (2) for every point of E.

A physical boundary unit has an actual point of norm R. It cannot satisfy (2). Hence its alleged point with y<=d-1 does not exist, proving the strict whole-unit conclusion (3).

The argument includes:

* q>d as well as q=d;
* equality of the hypothetical minimum support with d-1;
* aligned frames and all tilted frames;
* a point Q on a vertex, a side, an endpoint-valued shared side or the interior;
* either sign Q.f=+/-1/2;
* both physical circle masks and every individual zero circle coefficient;
* arbitrary actual forces, true degrees, additional contacts and completion units.

No force, moment, support owner or loading premise is imposed anywhere. The containing-circle origin and the actual unit E remain fixed.

## 9. Relation to the existing radial-side source and proof limits

The earlier source

RADIAL_SIDE_BOUNDARY_NEIGHBOR_HALFPLANE.md

proves the same boundary half-plane conclusion in the high subwindow sqrt(17)/2<=R<=sqrt(1105)/16 by a center-box estimate. The present proof is a new self-contained geometric argument and has no mathematical dependency on that estimate or on its positive high-radius margin.

In every original caller with an actual physical boundary unit E and an actual point Q satisfying (1), its half-plane conclusion is now available throughout R>=2, including the low portion 2<R<sqrt(17)/2. The stronger d>1/sqrt(2) statement is proved explicitly above.

This removes only that particular radius restriction. Every other original feature, owner, load, force and actual-contact premise of a caller remains to be proved at its own scope. The theorem does not itself close an original D02, house, pentagon or coarse graph family, and no gate or ledger is changed.

No sampled pose, numerical optimization, orientation mesh, finite pose certificate, Lean compilation, CI, workflow, replacement application, shared-ledger mutation or remote action is used. All comparisons are exact convexity, elementary coordinate identities and Cauchy inequalities.

