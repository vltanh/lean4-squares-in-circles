# Three actual near units force long center components for every completion square

Date: October 29, 2026 UTC. Author: block_roots continuation.

**Status: complete new uniform physical lemma and exact three-real-leaf
angular budget, frozen for full independent review.** The results apply
to the same nine actual squares. They use no contact graph, positive
degree, force equation, normal choice or circle coefficient. They do
not by themselves prove total capacity eight for every three-root pose.

Put

    Q=1105/256, delta=1/60, rho=9/8,
    phi=acos(9/10), s=6577/10000.

All squares below are actual closed unit squares with pairwise disjoint
open interiors, contained in the original disk of squared radius at
most Q. A center component means the connected component of a square's
open-interior intersection with |z|=rho containing its actual radial
center point. This does not assert that its entire intersection is
connected.

## 1. The uniform nine-square statement

Suppose three distinct actual units U_1,U_2,U_3 meet the closed disk
D_delta and belong to an actual nine-unit collection. Then every one
of the other six actual units E satisfies

    |c_E|>s>13/20,                 dist(O,E)>delta.       (1)

Its actual center component on |z|=rho exists and has angular length
strictly greater than phi. At least five of those six units have
center radius strictly greater than 3/4, and their center components
have length strictly greater than 2pi/9.

In particular, if three of those six units are the actual three
genuine radial-S leaves of U_1,U_2,U_3, at least two of the remaining
three actual completion units have center components longer than
2pi/9. The third has a component longer than phi, including when
its complete open-interior circle intersection has more than one
component.

The proof retains arbitrary root degrees and masks, all nine actual
units, every zero-weight physical contact and every original equation.
No unit is moved, reconstructed from center data or removed.

## 2. A center-only consequence of three near units

Every contained actual center satisfies

    |c|<M=91/60.                                        (2)

Indeed its farthest actual corner has squared norm at least
|c|^2+|c|+1/2, whose excess above Q at M is 31/57600.
Distinct actual centers are separated by at least one, because their
open radius-1/2 incircles are disjoint.

The three specified near centers have radii strictly below

    m=3619/5000.

Their distances from a chosen actual point of D_delta are at most
1/sqrt(2). The exact comparison follows from

    m-1/60=10607/15000,
    (10607/15000)^2-1/2=8449/225000000>0.

I reproduce the needed four-small-center angular argument from the
accepted four-near-unit source, at its actual center-only scope.
Suppose another actual center had radius at most s. These four
centers would all have radii at most m. None can be O, because its
distance to any of the others would be less than one.

For two positive radii a,b and minor angular separation omega, their
distance condition gives

    cos(omega)<=(a^2+b^2-1)/(2ab)=f(a,b).

On 0<a,b<=m<1, f is strictly increasing in either variable. Put
c=57/1250 and alpha=acos(c). The exact comparisons are

    f(m,m)=597161/13097161<c,
    57*13097161-1250*597161=86927>0;

    f(s,m)=-4354427/95208652<-c,
    1250*4354427-57*95208652=16140586>0.

Thus every pair of the four directions has minor angle greater than
alpha. Each consecutive cyclic gap is greater than alpha as well.
No gap can reach pi, since alpha>pi/3 and the other three gaps
would sum to more than pi. Consequently all consecutive gaps are
minor angles.

At the center of radius at most s, each adjacent gap is greater than
acos(-c)=pi-alpha, by the second comparison. The other two gaps
exceed alpha. Their sum would exceed 2pi, impossible. Therefore
every actual center other than the three specified centers has
radius strictly greater than s. This deduction requires no fourth
near-square hypothesis.

The accepted complete physical four-near-unit theorem supplies the
second assertion of (1). If any other E met the closed D_delta,
there would be four such actual units and total capacity at most
eight, contradicting the retained nine-unit hypothesis. Hence the
clearance in (1) is genuinely strict.

## 3. At most four actual centers can have radius at most three quarters

This elementary fact is independent of the near-unit hypothesis.
For positive a,b<=3/4, the same monotonicity gives

    cos(omega)<=f(3/4,3/4)=1/9.

Moreover

    cos(2pi/5)=(sqrt(5)-1)/4>1/4>1/9.

Thus every pair of such centers has minor angular separation greater
than 2pi/5. Every consecutive cyclic gap is consequently greater
than 2pi/5, whether or not that gap is minor. Five such centers
would have total gap sum greater than 2pi. A center at O cannot
coexist with even one other center in that disk, so it causes no
exception. There are at most four actual centers in the closed
radius-3/4 disk.

All three near centers lie strictly below m<3/4. Therefore at most
one of the other six centers can be at most 3/4, and at least five
are strictly larger. The complete centered-forty-degree theorem
applies to each of those five, at its original arbitrary-orientation
and arbitrary-circle-mask scope. Its closed arc lies inside the
actual open square; the containing center component is therefore
strictly longer than 2pi/9.

## 4. A standalone small-center component theorem

The remaining geometric statement is stronger than needed for the
nine-square application.

**Lemma.** Let an actual unit E be contained in D_(sqrt(Q)) and satisfy

    13/20<|c_E|<3/4,          dist(O,E)>1/60.             (3)

Then its center component on |z|=rho has length strictly greater
than phi=acos(9/10).

Choose signs and order of E's actual orthonormal own axes, without
translating O, so its center is (x,y), x>=y>=0. Set

    r^2=x^2+y^2, E=[A,a] x [B,b],
    A=x-1/2, a=x+1/2, B=y-1/2, b=y+1/2.

The positive distance in (3) forces x>1/2 and A>0. We always have

    A<1/4, B<1/4, a>=b>=1/2.

The actual point rho*c_E/r lies in the open incircle of E, because
5/8<13/20<r<3/4 and therefore |rho-r|<1/2. Hence the center
component exists. All intervals below are actual own-coordinate
circle intersections, not chosen application points.

The elementary angle comparisons used throughout are

    0<phi<pi/6,
    sin(phi)=sqrt(19)/10<7/16,
    sin(phi)<4/9.

Their positive squared reserves are respectively 3/50, 9/6400
and 61/8100.

### 4.1. The whole outer-face domain a>rho

Define

    alpha=acos(A/rho), beta=asin(B/rho), eta=asin(b/rho).

Here b<rho: x>5/8 and r<3/4 give y<sqrt(11)/8<5/8.
The entire open-interior circle intersection is the single interval

    (max(-alpha,beta), min(alpha,eta)).                  (4)

Indeed its first own coordinate must be positive and the outer
first face is beyond the whole circle. The two actual transverse
inequalities and the inner first face give precisely (4).

Since A/rho<2/9 and B/rho<2/9,

    alpha>pi/3, beta<pi/6, eta>=asin(4/9)>phi.

Thus alpha-beta, 2alpha and alpha+eta all exceed phi. The fourth
endpoint difference is the actual full unit-strip angle

    eta-beta=asin(b/rho)-asin((b-1)/rho)
             >=2asin(4/9)>phi.

The minimum is at b=1/2: its derivative is nonnegative for
1/2<=b<rho. Thus every upper-minus-lower difference in (4)
exceeds phi. This proves the lemma throughout a>rho.

### 4.2. The outer-face domain a<=rho with B>=0

Now 0<=B<=A<=1/8 and a,b>=1. Put

    theta=acos(a/rho), eta=asin(b/rho),
    alpha=acos(A/rho), beta=asin(B/rho).

The positive-quadrant component is exactly

    (max(beta,theta), min(alpha,eta)).                  (5)

Its inner/inner difference is at least pi/2-2asin(1/9)>pi/3.
Each complete unit-strip difference is at least asin(8/9)>phi.
Finally its outer/outer difference satisfies

    eta-theta>=pi/2-2acos(8/9)>pi/6>phi,

because 8/9>sqrt(3)/2. All four differences in (5) therefore
exceed phi. Actual equality at a=rho, b=1 or either zero inner
coordinate is included. The center point belongs to this positive
component, by the actual incircle argument.

### 4.3. The outer-face domain a<=rho with B<0

The original strict clearance now reads A>1/60, so

    31/60<x<=5/8.

Set r0=13/20 and

    y0=sqrt(r0^2-x^2), b0=y0+1/2, t=x+y0.

Since r>r0, the actual y is strictly greater than y0. The whole
closed comparison interval has

    4/5<t<11/12.                                       (6)

To verify (6), x+y0 decreases on this x interval because x>y0.
At its two endpoints the sums are

    5/8+sqrt(51)/40>4/5,
    31/60+sqrt(35)/15<11/12,

using sqrt(51)>7 and sqrt(35)<6 respectively.

An exact expansion at the unchanged comparison x gives

    a^2+b0^2-(7/8)*a*b0
      =(23/16)*r0^2+(9/16)*(t+1/2)-(7/16)*t^2.         (7)

This is concave in t. At the enlarged endpoints 4/5 and 11/12
its values are 271/256 and 14927/14400. Both exceed

    rho^2*cos(phi)^2=6561/6400,

with exact reserves 107/3200 and 659/57600. By (6)--(7) and
sin(phi)<7/16, therefore

    a^2+b0^2-2sin(phi)*a*b0>rho^2*cos(phi)^2.            (8)

The positive sign needed to reverse the squaring is retained:

    b0>27/40, a*sin(phi)<63/128,
    b0-a*sin(phi)>0.

Consequently (8) gives

    b0>a*sin(phi)+cos(phi)*sqrt(rho^2-a^2).

Here theta=acos(a/rho)<pi/6 and theta+phi<pi/3, so sine is
strictly increasing on the required interval. Since b>b0, we obtain

    eta-theta=asin(b/rho)-acos(a/rho)>phi.               (9)

The actual positive component is now

    (theta, min(alpha,eta)), alpha=acos(A/rho).

Its other endpoint difference alpha-theta is at least asin(8/9),
by the increasing full unit-strip formula for 0<=A<=1/8.
Thus (9) proves that this actual component is longer than phi.
The actual radial center point has positive coordinates and lies
in the open incircle, so it belongs to this component.

There can be an additional negative-angle component in this last
domain. It has not been discarded from the actual square or declared
absent; the argument needs only the just proved center component.
The cases 4.1--4.3 exhaust (3), proving the standalone lemma.

## 5. Proof of the complete nine-square statement

Equations (1)--(2) follow from Section 2. If one of the other six
centers is below 3/4, the lemma of Section 4 applies literally.
Every other such center is covered by the complete centered-forty-
degree theorem, which is stronger than phi since phi<pi/6<2pi/9.
The threshold r=3/4 belongs to that latter theorem. Section 3 gives
at least five centers strictly above 3/4. This proves Section 1,
including every physical contact and every center-radius endpoint.

## 6. Exact occupied arcs of the three real high-S leaves

Apply the accepted whole high-S reduction to three distinct genuine
roots of arbitrary positive degrees, each with its real genuine leaf.
It excludes the whole low/critical/D alternatives and gives

    d=1+epsilon, 0<epsilon<1/60,
    S(e)=[d,d+1]e+[-1/2,1/2]Je.

The three roots meet D_epsilon and thus meet D_delta. Their three
leaves are distinct actual units, distinct also from the roots.
Each actual leaf center has radius d+1/2>3/4. In a hypothetical
nine-unit collection, the remaining three actual units satisfy the
center-component conclusions of Section 1, at least two of them
with length strictly greater than 2pi/9.

On |z|=rho the complete closed intersection of each real S leaf is
the closed arc centered at its actual e direction with halfwidth

    alpha(d)=min(acos(d/rho), asin(1/(2rho))).           (10)

The outer radial face is beyond the whole circle; the actual inner
face and two transverse faces give exactly (10). Its open-interior
intersection is the corresponding open arc. Thus neither an actual
leaf nor its transverse endpoints is replaced by an abstract ray.

Uniformly in the complete high radius range,

    alpha(d)>alpha0=acos(122/135).                     (11)

The first expression in (10) exceeds alpha0 because d<61/60.
For the second, the exact comparison is

    (122/135)^2-(sqrt(65)/9)^2=259/18225>0,

and cos(asin(4/9))=sqrt(65)/9. This proves (11) with strict
reserve even at the original closed upper radius endpoint.

## 7. The uniform root budget and the precise remaining capacity obligation

Let mu_i be the full angular measure of int(U_i) on |z|=rho;
its actual intersection need not be connected. All original square
interiors give disjoint measurable circle sets. The three complete
leaf arcs have total length 6alpha(d). The other three units supply
three disjoint center components, two longer than 2pi/9 and the
third longer than phi. Therefore every surviving nine-unit pose
necessarily satisfies

    mu_1+mu_2+mu_3
       <2pi-6alpha(d)-4pi/9-phi
       <2pi-6alpha0-4pi/9-phi.                        (12)

This is a single actual angular budget for every remaining genuine-
three-root graph, without prescribing any root degree or deleting
another positive force at a heavy root.

There is also a literal gap-routing export. Remove the full closed
circle intersections of the three actual roots and three actual
leaves. Each completion unit's chosen center component lies in one
connected component of this actual open complement. An interior
point of a completion square cannot lie on any of those closed
occupied arcs, since an interior neighborhood would meet the open
interior of that actual occupied square. Connectedness of the chosen
component supplies the routing even when the completion square has
additional components elsewhere on the circle.

A capacity caller must still show that these actual gaps cannot
hold all three routed components, with two lengths greater than
2pi/9 and the third greater than phi, or must contradict (12) by
an actual root measure bound. Neither root containment of O nor
pairwise-disjoint abstract root quadrants is supplied by the present
theorem. A root with a broad transverse interval remains in the
domain. No whole house, fan, three-root class or coarse row is
declared closed by this budget alone.

## 8. Exact operative sources and verification boundary

| Source | SHA256 | Exact consumed role |
| --- | --- | --- |
| FOUR_NEAR_ORIGIN_UNITS_CAPACITY.md | 63560c355c1b4c385618f412f6b6c01946f664684e843aa4fef85d78cba07190 | Whole actual four-near capacity for the strict distance in (1); its center-only angular argument is reproduced completely in Section 2 |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Complete closed centered arc at every actual center radius at least 3/4, arbitrary orientation and physical mask |
| THREE_GENUINE_LEAF_ROOTS_HIGH_S_REDUCTION.md | 41c6686127871c7c99ab69c84292f04c995a8530eb02cde0235cdacc181ae73f | Only Sections 6--7: full original low/critical/D cover, strict high-S geometry and three actual near points |

All three complete source manuscripts were read. The new low-center
arc proof, the at-most-one low completion center conclusion, and the
actual real-leaf budget require their own full independent review.
The checks of printed rational identities do not sample square poses
or certify any omitted continuous feature.

No original force, mean, normal, true degree, circle coefficient or
physical unit is changed. No original flag, metadata or ledger is
edited. No pose sampling, angle mesh, packing certificate, Lean/Lake,
CI/workflow, remote mutation or merge was used.
