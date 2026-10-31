# Two genuine S roots beyond one wall: complete near-feature kernel

Date: October 27, 2026.

**Status: complete proposed uniform physical kernel, frozen for full
root and separate independent review.** The wall need not bound an
origin-containing square. Both oblique and wall-parallel endpoint
frames are included. No force or application is changed.

## 1. Precise physical inputs and conclusions

Put d=1+epsilon, where 0<epsilon<1/60. Keep actual unit squares A,C
with disjoint open interiors, wholly in x<=h, where

    -epsilon<=h<=epsilon.

Choose actual right-wall vertices p_A=(h,y_A), p_C=(h,y_C) with

    0<=D:=y_A-y_C<3/4.                              (1)

The vertical coordinate is oriented so A is the upper root. If D=0,
use the upper physical square as A; the common-point argument in
Section 2 shows that both squares are then parallel to the wall and
lie on opposite sides of the horizontal line through that point.
Exchanging the labels or reflecting the vertical coordinate is
permitted before fixing this chart; no physical unit is moved.

Use their actual inward orthonormal frames

    A=p_A+[0,1]u+[0,1]v,
    u=(-a,b), v=(-b,-a), a,b>=0, a^2+b^2=1,

    C=p_C+[0,1]u'+[0,1]v',
    u'=(-c,s), v'=(-s,-c), c,s>=0, c^2+s^2=1.       (2)

For an oblique square its right-wall vertex is unique. For a square
parallel to the wall, a chosen right-wall endpoint is only a physical
coordinate origin for (2); it is not asserted to be an original force
application. In particular an original shared-side mean stays where
it was. Condition (1) must be checked at the actual chosen vertices.

Each root has its own distinct actual radial S leaf with direction
e_A or e_C. The precise physical data used here are

    |e_i|=1,
    d*e_i in root i,   max_(root i)(e_i.x)=d,
    epsilon*e_i in root i,
    c_(leaf i)=(d+1/2)*e_i.                         (3)

The two leaves are distinct actual units with disjoint open interiors.
These are the usual genuine S-root data; no equation at either root
is used in Sections 2--6. Equivalently the third condition follows
from the first two by moving one unit inward from the actual support
point along e_i. It is recorded explicitly to leave its scope clear.

**Physical conclusions.** The whole original configuration satisfies

    b,c>99/100,
    a,s<(10/3)*epsilon<1/18,
    |y_A|,|y_C|<(10/9)*epsilon.                     (4)

Moreover the complete genuine-leaf support cover is

    A: owned +u axis, or strict vertex p_A+u;
    C: owned +v' axis, or strict vertex p_C+v'.      (5)

Thus the upper root has its north leaf type and the lower root has
its south leaf type. Every possible west leaf type is impossible
because its two actual S leaves would overlap. Owned-axis endpoints,
a=0 and s=0 remain in (5).

Section 7 records a further conditional force consequence for an
oblique A at its unchanged actual wall port, when A and its true
other neighbor form a physical triangle with a wall-side square.
That statement uses the full actual A3 equation and preserves every
possible owned-side mean of the other contact.

## 2. Exact separating-axis calculation for the actual squares

Set

    K=ac+bs>=0, L=bc-as, K^2+L^2=1.

First retain D=0 explicitly. If either root is oblique to the wall,
the strict west ray at the common vertex lies in its open tangent
sector and belongs to the other root's closed tangent sector. This
would put a point of the other closed square in its open interior,
and hence give interior overlap. Thus both are wall-parallel. Their
disjoint interiors place one above and the other below the common
horizontal line. With the upper-root convention in Section 1,
a=s=0, b=c=1; the projection calculations below apply directly.

The physical separating-axis theorem for these two convex squares
uses one of their own axes. A horizontal axis cannot separate them:
both have rightmost coordinate h and positive width to the left.
Choose the sign of a separating axis to have positive vertical
component. Since p_A is no lower than p_C, A must be on its positive
side when D>0. At D=0 the preceding complete parallel-frame case
has the same property. Thus the projection inequalities below give
the complete alternatives in both cases.

Testing the four possible positive-y own axes gives exactly:

| Physical separating axis | Necessary inequality |
| --- | --- |
| u=(-a,b) | b*D>=K+max(0,-L) |
| -v=(b,a) | a*D>=1+max(0,-L) |
| u'=(-c,s) | s*D>=1+max(0,-L) |
| -v'=(s,c) | c*D>=K+max(0,-L) |

For the first row, min_A(u.x)=u.p_A while
max_C(u.x)=u.p_C+K+max(0,-L). For the second row,
min_A(-v.x)=(-v).p_A-1 and
max_C(-v.x)=(-v).p_C+max(0,-L). The third and fourth follow
by interchanging the original rectangles and reversing the sign.
This uses their full unchanged sides, including touching projections.
A row with zero vertical component cannot be a separator. The
displayed inequalities may still record equality on a repeated
horizontal axis, but do not introduce a new separating possibility.

The second and third rows require D>=1 and are excluded by (1).
If L<=0, then K-L>=1 because K>=0 and K^2+L^2=1. The first and
fourth rows would again require D>=1. Consequently

    L>0,
    D>=K/max(b,c).                                 (6)

In particular b,c cannot vanish. One may also see this directly:
b=0 makes a=1 and L=-s<=0; c=0 makes s=1 and L=-a<=0.

Write a=cos(theta_A), b=sin(theta_A), c=cos(theta_C),
s=sin(theta_C), with angles in [0,pi/2]. Then L>0 means
theta_A>theta_C. If b<=13/20, the angle difference is at most
theta_A, so

    K>=cos(theta_A)=a>=sqrt(231)/20>3/4.

This contradicts (6),(1). If c<=13/20, the difference is at most
pi/2-theta_C, and the same argument gives K>=s>3/4. The exact
squared reserve is 231/400-9/16=3/200. Thus

    b,c>13/20.                                     (7)

The case K=0 is retained: it forces a=s=0, b=c=1. It is the two
parallel endpoint frames facing north and south. No strict
obliqueness or nonzero vertical gap has been assumed in this case.

## 3. The two actual near points force the small slopes

Put r_A=a/b, r_C=s/c and r=r_A+r_C. For A's actual point
epsilon*e_A, its horizontal deficit from the wall is

    t_A=h-(epsilon*e_A)_x, 0<=t_A<=2*epsilon.

Writing that point p_A+xi*u+eta*v, its height is at least
y_A-r_A*t_A. Indeed a*xi+b*eta=t_A, xi,eta>=0, and
b*xi-a*eta>=-(a/b)*t_A. Since its height is at most epsilon,

    y_A<=epsilon+2*epsilon*r_A.

The reflected calculation at C's actual point gives

    y_C>=-epsilon-2*epsilon*r_C,
    D<=2*epsilon*(1+r).                             (8)

But K=bc*r, so (6)--(7) give D>=min(b,c)*r. If r>0, combining
this with (8) yields

    r<2*epsilon/(13/20-2*epsilon)
       <(120/37)*epsilon<(10/3)*epsilon<1/18.       (9)

For r=0 the same strict upper bounds hold trivially since epsilon>0.
Thus a,s<=r obey (4). Squaring gives

    b,c>99/100,

using 1-(1/18)^2-(99/100)^2=13619/810000>0. Finally (8),
y_C<=y_A and r<1/18 give

    |y_A|,|y_C|<(1+2/18)*epsilon=(10/9)*epsilon,

as asserted. These are bounds on actual physical vertices, derived
without changing any original mean or inferring a force equation.

## 4. The complete genuine-leaf feature cover

At A, p_A has norm at most |h|+|y_A|<(19/9)*epsilon<d,
so it cannot be its actual radial leaf support d*e_A. The opposite
vertex p_A+u+v has x-coordinate less than -59/60, because
a+b>=1 and h<=epsilon<1/60. Its y-coordinate is greater than

    99/100-1/18-(10/9)*(1/60)>4/5,

with reserve 313/2700. Therefore its squared norm exceeds d^2:

    (59/60)^2+(4/5)^2-(61/60)^2=43/75>0.

It cannot be the radial leaf support either. The two near owned
axes -u,-v have support heights bounded in absolute value by
|h|+|y_A|<d. The remaining complete support cover is precisely

* north: the owned +u axis or strict vertex p_A+u;
* west: the owned +v axis or strict vertex p_A+v.

Here a strict vertex means its actual leaf direction lies strictly
inside that vertex normal cone. A normal on a cone boundary is
already in the corresponding owned-axis case; its actual radial
application may be any original point on that owned side.

Reflecting vertically gives the complete C cover:

* south: the owned +v' axis or strict vertex p_C+v';
* west: the owned +u' axis or strict vertex p_C+u'.

This proof permits a=0 or s=0. It is a physical support cover,
not a claim that the leaf direction is necessarily an own axis.

## 5. A west leaf forces the common wall too far west

Suppose first that A has its west type. In both alternatives,

    (e_A)_x<0,
    |(e_A)_y|<(40/9)*epsilon<3/40.                 (10)

For an owned +v leaf its vertical component has magnitude a.
For a strict vertex leaf, d*e_A=(h-b,y_A-a), and (4) gives
the displayed bound. The last strict comparison has reserve
3/40-(40/9)*(1/60)=1/1080.

We claim in both alternatives that

    h<-(5/6)*epsilon.                              (11)

For an owned +v leaf, the unchanged exact support identity is
1-b*h-a*y_A=d. Hence

    h=(-epsilon-a*y_A)/b
      <=-epsilon+(100/27)*epsilon^2
      <-(76/81)*epsilon<-(5/6)*epsilon.

The numerator is negative because |a*y_A|<(100/27)*epsilon^2
and epsilon<1/60. Since b<=1, replacing its denominator by one
is an upper bound. This includes b=1 without a strict division.

For a strict west vertex, the actual radius equation gives

    h=b-sqrt(d^2-(y_A-a)^2)
      <=1-sqrt(d^2-((40/9)*epsilon)^2).

The exact square comparison is

    d^2-((40/9)*epsilon)^2-(1+(5/6)*epsilon)^2
      =epsilon*[1/3-(1600/81-11/36)*epsilon]
      >epsilon*(179/19440)>0.

This proves (11). Reflection gives the same (10),(11) for a west
leaf at C, with its unchanged original direction and support point.

## 6. The two distinct actual west-side leaves would overlap

Assume one root has a west leaf. Call its direction e and the other
root's direction f. Equation (10) gives

    e_x<0, |e_y|<3/40, -e_x>199/200,

where 1-(3/40)^2-(199/200)^2=87/20000>0. The other actual near
point epsilon*f lies in x<=h. Equation (11) therefore gives

    f_x<-5/6, |f_y|<sqrt(11)/6<5/9.

The last squared reserve is (5/9)^2-11/36=1/324. Consequently

    e.f>(199/200)*(5/6)-(3/40)*(5/9)=63/80,
    |e-f|^2<17/40.

The two distinct actual S leaf centers are (d+1/2)*e and
(d+1/2)*f. Their squared distance is strictly less than

    (91/60)^2*(17/40)=140777/144000<1,

with reserve 3223/144000. Their open inscribed disks of radius
one half would overlap, contradicting actual unit nonoverlap.

Thus neither root can have a west leaf. This proves exactly the
complete remaining cover (5), with all original leaves retained.
In particular

    e_A.v<=0, e_A.u>0,
    e_C.u'<=0, e_C.v'>0.                            (12)

## 7. Conditional actual-A3 boundary-port consequence

Additionally suppose a>0, so A is oblique to the wall. Let an actual
unit H lie in x>=h and physically touch A at its rightmost vertex
p_A. Let an actual unit K physically touch both A and H. Assume A
has its full unchanged clear true-degree-three equation

    lambda*e_A+mu*n_AH+gamma*n_AK=0,
    lambda,mu,gamma>0.                             (13)

There are precisely these three original pair forces, including the
real leaf; no circle load or fourth force has been omitted. Let Q be
the unchanged actual AK application. The actual AH normal supports
A at p_A, so n_AH.u<=0 and n_AH.v<=0, whether it is an own axis
at an endpoint or a strict vertex normal. By (12),(13),

    n_AK.v>=0.                                     (14)

Use the actual physical wall separator e_x for the physical contact
triangle H,A,K. This is only a geometric separator; it does not
replace the original n_AH in (13). The complete side-normal and
support-span theorem is

    UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md
    SHA256 b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207.

Its geometric statement permits every physical separator, arbitrary
degrees and all actual side means. Since a,b>0, e_x.u=-a<0 and
e_x.v=-b<0. It forbids n_AK=+u or +v in this physical triangle.

If n_AK.v=0, (14) leaves n_AK=+u or -u; only -u remains. Its
actual application Q can be anywhere on the whole unchanged side
[p_A,p_A+v]. If n_AK.v>0 and n_AK.u<0, it strictly exposes the
actual vertex p_A+v. Equality n_AK.u=0 would be the excluded
owned +v normal. If n_AK.u>0, its point is the opposite vertex
p_A+u+v and n_AK.e_x<0. At that minimum-n_AK support point of K,
the strict support-span lemma gives

    max_K(x)<(p_A+u+v)_x+1=h-a-b+1<h.

This contradicts the actual physical HK contact, because H lies in
x>=h. Thus every possibility in (14) has been checked, and

    Q in [p_A,p_A+v],
    |Q_y|<=|y_A|+a<(40/9)*epsilon<3/40.            (15)

No endpoint mean is changed: in particular the zero projection in
(14) retains the full side [p_A,p_A+v], not just its far vertex.

If K physically touches the containing circle and R>2, this gives a
contradiction. Its actual HK contact has x-coordinate at least h,
whereas its actual AK contact Q has x-coordinate at most h. Every
point of a unit square is within 1/sqrt(2)<71/100 of its center.
Writing that actual center (X,Y),

    h-1/sqrt(2)<=X<=h+1/sqrt(2),
    |X|<epsilon+71/100<3/4,
    |Y|<3/40+71/100<4/5.

Hence |c_K|^2<9/16+16/25. A physical circle point of K gives
|c_K|>=R-1/sqrt(2)>2-3/4=5/4. The exact squared contradiction
has reserve 25/16-9/16-16/25=9/25.

Section 7 needs the actual HK physical contact and the complete
clear A3 equation (13). They are not consequences of Sections 1--6.
In particular this section cannot be applied to a four-cycle merely
by naming its opposite boundary vertex K, or to a genuine A4 root
by deleting one of its three original nonleaf forces.

## 8. Scope and provenance

Sections 2--6 give a complete physical separating-axis and genuine-
leaf feature theorem under the exact wall and actual-vertex gap
premises (1)--(3). They remain valid at a wall x=epsilon whose
right-hand unit avoids O, and for parallel endpoint frames a=0 or
s=0. The upper/lower physical vertices must still be established
without replacing any original mean.

The proof develops the same-wall calculation in the accepted
THREE_S_ROOTS_SAME_HUB_SIDE_INTERFACES_EXCLUSION.md, but does not
import that theorem's genuine hub leaf, old true B2/D2 premises,
parallel-frame exclusions or narrower 11/30 port bound. Its complete
new premises, constants, axis endpoints and force consequence are
proved above. The sole external mathematical input is the pinned
degree-free physical triangle theorem in Section 7, unchanged at
publication boundary 8304072dbc91bcbe726d651c10403351f9566853.

This file makes no original fine/coarse cell-closure claim. It uses
no pose sampling, angle subdivision, Lean run, workflow, remote
mutation or shared-ledger change.
