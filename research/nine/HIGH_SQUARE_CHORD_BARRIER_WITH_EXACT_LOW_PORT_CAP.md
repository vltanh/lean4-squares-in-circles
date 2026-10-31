# A lower high-square barrier using the exact whole-unit low-port cap

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed force-free theorem, frozen for separate full
independent review.** This strengthens the available geometric barrier to
top height 69/100 by retaining the actual lower-port cap 49/75. It also
includes the whole lower-route length theorem at that new height. No
original graph/load family or ledger flag is declared closed here.

## 1. Complete physical statement

Let H and B be actual unit squares with disjoint open interiors, contained
in the same original circle about O, with

    R^2=(2+epsilon)^2+1/4<=1105/256,
    0<=epsilon<1/60,
    H=[h-1,h] times [g-1,g],
    h<=epsilon, 69/100<=g<=1.                         (1)

Then B cannot contain actual points P,V satisfying

    P_x<h, P_y<49/75,
    h-1<=V_x<=h, V_y>=g.                             (2)

Both horizontal endpoints and V_y=g are included. Neither point has to
be a vertex, a force application or a positively weighted circle point.
There is no degree, force, original HB edge or physical-circle-mask premise.
All actual squares and their original circle remain fixed.

Here and below we use the proved complete cap: any contained actual unit
in x>=1-epsilon has every actual height of absolute value less than
49/75. Its full proof is Section 2 of the exact signed-support barrier
pinned below, from the actual center and whole-width bounds. Reflection
gives the same cap for a unit in x<=-(1-epsilon). No separate two-unit
or force theorem is being used as a substitute for this whole-unit fact.

## 2. Every possible separator is an actual B-owned Northwest axis

Write A0=1-h>59/60 and U=(-A0,g), the actual top-left H corner.
Convexity puts the entire chord PV in B. If P_x>-A0, this chord
enters int H just below height g: both abscissas are in the closed
H strip, P is strictly inside its right endpoint, and P_y<49/75<g.
The same statement holds when V is at either endpoint or V_y=g.
Thus

    P_x<=-A0.                                        (3)

Two rectangles with disjoint open interiors have a weak separating axis
owned by one of the rectangles. This follows by separating O from the
open Minkowski difference; its edges have exactly the two rectangles'
own-axis normals. The weak version includes actual touching endpoints.
This is an auxiliary geometric separator, not a new force normal.

No H-axis separation works. P excludes right and above, V excludes
below, and a whole B on the left would have x<=h-1<=-(1-epsilon),
whose complete cap contradicts V_y>=g>49/75. For a B-owned separator
n from H toward B, P excludes Northeast, while V excludes Southwest
and Southeast. The axis endpoints have already been excluded. Therefore
the entire remaining direction is

    n=(-s,c), t=(c,s), s,c>0, s^2+c^2=1,
    B=[k,k+1]n+[ell,ell+1]t,
    H0=U.n=A0*s+g*c,
    T0=U.t=-A0*c+g*s,
    k>=H0>0.                                        (4)

Equations (2),(3) give P.t<T0<=V.t, so T0 belongs to B's actual
closed tangent interval, including the possible V=U case.

## 3. A continuous far-corner estimate excludes every separator

The actual far-side point (k+1)n+T0*t belongs to B. Hence

    R^2>=(k+1)^2+T0^2
        >=A0^2+g^2+2H0+1,
    H0<15/16.                                       (5)

For the last implication, the exact positive reserve is

    (59/60)^2+(69/100)^2+1+2*(15/16)-1105/256
        =2359/1440000>0.

The concave function

    (59/60)s+(69/100)sqrt(1-s^2)

on [1/3,1] has its minimum at an endpoint. Its right endpoint is
59/60>15/16. Its left endpoint exceeds
(59/60)/3+(69/100)(14/15)>15/16. Thus (5) forces

    0<s<1/3, c>9/10,
    T0<-(59/60)(9/10)+1/3<0.                        (6)

Set eta=g-49/75>=11/300. Because P.n>=k>=H0 and P_y<49/75,

    P_y-g=c(P.n-H0)+s(P.t-T0)<-eta,
    ell<=P.t<T0-eta/s<0.

Consequently the same actual B's far corner Z=(k+1)n+ell*t satisfies

    |Z|^2>(H0+1)^2+(T0-eta/s)^2.                   (7)

The two positive square-root expressions increase with A0 and g.
For the second use

    -T0+eta/s=A0*c+g*c^2/s-(49/75)/s.

At A0=59/60 and g=69/100 it is positive, since (6) gives the
lower bound (59/60)(9/10)-(69/100)/3+(11/300)*3>0.
It therefore suffices in (7) to use these two lower endpoint values.

Put A=59/60, G=69/100, E=11/300 and

    K=1+A^2+G^2-2GE=5383/2250.

The resulting exact square expansion is

    [1+A*s+G*c]^2+[A*c-G*s+E/s]^2
       =K+2A*s+2G*c+2AE*(c/s)+E^2/s^2.

By c>9/10 and the arithmetic-geometric mean inequality,

    2A*s+2AE*(c/s)
       >2A*s+2AE*(9/10)/s
       >=2 sqrt((2A)*(2AE*(9/10)))>7/10.

The final squared reserve is exactly 1541/75000. Also
2G*c>621/500. Dropping only the positive last term gives

    |Z|^2>K+621/500+7/10
           =3901/900
           =1105/256+1039/57600.                   (8)

This contradicts containment of the original actual corner Z. It proves
the complete barrier (1),(2), with every stated closed endpoint intact.

## 4. The whole lower-route theorem at the new height

Add an actual unit square A, with open interior disjoint from those of
H and B, in the same circle. Let ell0,eta0>0 satisfy

    ell0+eta0>sqrt(2),
    min_A x>=h-1,
    min_A y>g-1+eta0.                               (9)

Suppose the actual B contains P with

    P_x<=h-ell0, P_y<49/75.                         (10)

Then A and B cannot physically touch. Here the minimum bounds are on
the entire actual A, not just a conveniently chosen point.

Indeed, if V belongs to the actual A intersection B, then
V_x>=h-1 and V_y>g-1. A point with h-1<V_x<h and V_y<g
would lie inside H. At V_x=h-1 and V_y<g, nearby interior A
points have x>h-1 by the whole-A minimum and would enter int H
too. Thus every V with h-1<=V_x<h must have V_y>=g, and is
excluded by Sections 1--3. At V_x=h and V_y>=g the same barrier
includes that endpoint. At V_x=h and g-1<V_y<g, the actual B
segment toward P immediately enters int H.

Only V_x>h remains. Its actual chord from P crosses x=h at a
unique point E0 strictly between P and V. If E0_y<=g-1, then

    |P-E0|>=h-P_x>=ell0,
    |E0-V|>=V_y-E0_y>eta0,
    |P-V|=|P-E0|+|E0-V|>ell0+eta0>sqrt(2).

This contradicts the diameter of the same actual B. The argument adds
lengths of two collinear subsegments, not two projections of a single
unbroken vector; the closed case E0_y=g-1 is included. If
g-1<E0_y<g, the chord toward P enters int H. If E0_y=g, it also
enters because P_y<49/75<g. The remaining E0_y>g meets the proved
barrier at the closed right endpoint E0_x=h. This exhausts all V.

In particular (9) applies with ell0=2/3 and eta0=3/4. Their sum
is 17/12 and (17/12)^2-2=1/144>0. It also permits any other
literal pair of whole-unit height/left-gap bounds satisfying (9).
The auxiliary E0 is only an actual B point, never a substituted force
application or a changed shared mean.

## 5. Exact input scope and preservation

| Source | SHA256 | Literal use |
| --- | --- | --- |
| HIGH_SQUARE_LOW_LEFT_PORT_BARRIER_WITH_SIGNED_SMALL_SUPPORT.md | e2463dea33c2e66b97046c5727562be354e09f3f065e3dc04028e3a79a79dc58 | Section 2 complete whole-unit support cap; the rest of the geometric barrier is freshly proved with the new constants |
| HIGH_SQUARE_CHORD_BARRIER_WITH_LOWER_ROUTE_LENGTH.md | 11e9eb7ba47bb8e8042aed44536046dba6c98f50961e663986935e0ea41cd9a1 | Predecessor lower-route structure only; Section 4 freshly checks every endpoint at the new top and low-port thresholds |

This root-authored strengthening was motivated by the aligned roof
perpendicular-contact chart supplied by roof_resume. No proof discovery
was supplied by the independent reviewer. A future caller must establish
the actual complete A extents, actual C/B port cap and unchanged H chart.
All-nine-unit callers retain every other unit, original degree, full force
and torque equation, normal, application, mean, mask and zero coefficient.

No sampled pose, angle grid, finite geometric exclusion packet, normal
reselection, force deletion, Lean compilation, CI, metadata change or
remote write is used. Exact scalar arithmetic only checks the printed
rational reserves; it is not a computational geometric certificate.
