# A boundary unit cannot touch three units within 1/60 of the origin

Date: October 27, 2026.

**Status: fresh complete hand local theorem and one complete original
C1.4.b3 caller, submitted for independent and root review.** This is
a new proof with explicit rational constants. It does not claim
recovery of any lost earlier contact-lens source. No shared metadata
or original gate is changed.

Let actual interior-disjoint unit squares be contained in the disk
of radius R about O, where R>=79/40. Suppose K physically touches
the circle. Then K cannot physically touch three distinct actual
units A_1,A_2,A_3 which each meet the closed disk D_(1/60).
The statement is force-free: every orientation, contact feature,
physical boundary mask, zero weight and degree is allowed.

## 1. Actual centers reduce to one fixed contact lens

Put

    a=29/40,       b=63/50,       rho=sqrt(2).

The center z_i of a unit meeting D_(1/60) satisfies

    |z_i|<=1/sqrt(2)+1/60<a,

because (a-1/60)^2-1/2=(17/24)^2-1/2=1/576>0.
The boundary unit center c satisfies

    |c|>=R-1/sqrt(2)>79/40-5/7
        =b+1/1400>b.                                    (1)

Rotate the whole configuration so c=(q,0), q>b. The actual
physical contact between K and A_i implies |z_i-c|<=sqrt(2),
since a common point is within 1/sqrt(2) of either center.
For |z_i|<=a and q>=b>a, the squared distance to (q,0)
strictly increases with q. Consequently every z_i lies in
the fixed closed lens

    E={z:|z|<=a, |z-(b,0)|<=rho}.                        (2)

The centers of distinct actual units have distance at least one,
by their disjoint open radius-1/2 incircles. We prove that the
closed upper half E_+ of E has diameter strictly below one.
The same then holds for its reflected lower half. Among three
centers in E, two belong to one of these halves, contradicting
their actual separation. Centers on the dividing axis cause no
exception to this two-half pigeonhole argument.

## 2. The complete boundary of the upper lens

The upper circle intersection is Z=(x_0,y_0), where

    x_0=(b^2+a^2-rho^2)/(2b)=647/14400,
    y_0=sqrt(a^2-x_0^2)>0.

The upper lens boundary consists of the axis segment from

    B=(b-rho,0)       to       A=(a,0),

the O-centered arc from A to Z, and the (b,0)-centered left
arc from B to Z. Both arc angles lie strictly between zero
and pi/2: 0<x_0<a and 0<b-x_0<rho. These inequalities
follow directly from the displayed constants and circle
intersection identity. In particular both arcs have angular
length below pi.

Every pair on the O-centered arc is at distance at most |A-Z|,
and every pair on the other arc is at distance at most |B-Z|.
It remains to check a pair on different arcs, rather than
assuming a triangle contains the curved lens.

Fix Q on the B-to-Z arc. For a point P=a(cos theta,sin theta)
on the A-to-Z arc, 0<=theta<=theta_0<pi/2, the distance
|P-Q| is maximal where

    Q_x cos theta+Q_y sin theta

is minimal. If Q_x<=0, this expression is nondecreasing on
that interval, so its minimum is at theta=0. If Q_x>=0,
it is concave, so its minimum is at one of the two endpoints.
Thus the farthest P is A or Z.

Write Q=(b-rho cos phi,rho sin phi), 0<=phi<=phi_0<pi/2.
Because b>a,

    |Q-A|^2=(b-a)^2+rho^2-2rho(b-a)cos phi

is increasing with phi. Hence |Q-A|<=|Z-A|. Also |Q-Z|
is a chord of the same short circle arc and is at most |B-Z|.
This exhausts the cross-arc pairs. For a point on the axis
segment, convexity of squared distance reduces its comparison
to the endpoints A,B. Finally convexity reduces the maximum
distance on the whole compact convex lens half to its boundary.
We have therefore proved

    diameter(E_+)<=max(|A-B|,|A-Z|,|B-Z|).                 (3)

## 3. All three endpoint distances are strictly below one

The exact longest-circle-chord comparison is

    |A-Z|^2=2a(a-x_0)=1-4003/288000<1.                  (4)

For the other arc,

    b-x_0=6/5+217/14400>6/5,
    |B-Z|^2=4-2sqrt(2)(b-x_0)<1,                        (5)

where the last strict inequality already follows from
sqrt(2)>5/4. For the axis segment,

    b-a=1/2+7/200>1/2,
    |A-B|=sqrt(2)-(b-a)<1,                              (6)

using sqrt(2)<3/2. Equations (3)--(6) give the required
uniform strict diameter bound. It applies to all closed arc,
axis, side and vertex endpoints. This proves the theorem.

No common square orientation, equal center radius, positive
circle weight or sampled pose has been imposed. The only
contact estimate was the exact square circumradius bound at
an actual common point.

## 4. Whole C1.4.b3 diamond with leaves at a hub and both tips

Keep the original nine squares and the same compatible selected
radius/Phi-minimizer and minimum-positive-original-atom certificate
in 79/40<=R<=sqrt(1105)/16. Let the actual four-body block be
the diamond with hubs H,K and tips B,D, with block edges

    HK, HB, KB, HD, KD.

Suppose its three actual bridges are genuine leaves at H,B,D.
The true degrees are H4,K3,B3,D3 and the three leaves have
degree one. The two other physical squares remain arbitrary
and present. Every original S/D leaf combination and load
mask is retained.

Each of H,B,D is a genuine leaf root. Its actual inward radial
unit segment gives an O point for d<=1 or a point of norm at
most epsilon=d-1<1/60 for d>1, with the D-root alternative
also included. Thus all three distinct actual roots meet
D_(1/60). These are the original genuine-root facts used,
for example, in Sections 1--2 of
THREE_GENUINE_LEAVES_WITH_A_TRANSMITTER_ROOT_EXCLUSION.md;
their physical scope does not impose degree two at these roots.

The actual K has exactly the original neighbors H,B,D, and H
physically touches both B and D. The local complete theorem
NO_UNLOADED_DIAMOND_HUB.md therefore forces K to carry a
positive circle load, with every other body's degree and force
unchanged. In particular K physically touches the circle.
But K physically touches the three distinct near units H,B,D,
contrary to Sections 1--3.

This excludes that entire original three-leaf attachment,
including all genuine terminal types, radius endpoints,
shared means and zero-weight physical masks. No equation at
the decorated degree-four hub H is shortened. It is one
whole attachment of C1.4.b3, not the entire coarse cell.
