# Three real S-leaf roots with two-epsilon vertices have total capacity at most eight

Date: October 29, 2026 UTC. Author: block_roots continuation.

**Status: complete new uniform physical exclusion, frozen for full
independent review.** The theorem keeps arbitrary root degrees and all
nine actual units. It excludes the entire stated small-vertex geometry,
including its attained vertex bounds. It does not claim that every
three-genuine-root configuration has the required three small vertices.

## 1. Actual physical statement and original-degree export

Retain pairwise interior-disjoint actual unit squares in the original
disk, with

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60.

Let X_1,X_2,X_3 be three distinct actual roots of three distinct real
radial-S leaves. Precisely, for each root there is an actual unit

    L_i=[d,d+1]e_i+[-1/2,1/2]Je_i,

distinct from all roots and other leaves, and X_i has the actual radial
point P_i=d*e_i as a maximum-e_i support point. These are the physical
facts supplied by a genuine positive degree-one S leaf. No equation
at X_i or degree restriction at any root is assumed in the proof.

Suppose each X_i has an actual vertex W_i with

    |W_i|<=2epsilon.                                   (1)

**Theorem.** These six actual units cannot belong to a nine-unit
collection in the same disk. Every other actual unit may have arbitrary
orientation, contact pattern, physical circle mask and circle weights.

For three original distinct genuine roots in the full closed original
window 79/40<=R<=sqrt(1105)/16, the accepted high-S reduction first
excludes all low, critical and D-leaf alternatives. In the remaining
high range the theorem applies exactly when all three original roots
satisfy (1). Thus every surviving original three-genuine-root domain
must have at least one root whose four actual vertices are all strictly
farther than 2epsilon from O.

This last conclusion does not replace the accepted theorem giving two
vertices within 4epsilon. Two 4epsilon vertices do not imply the
three 2epsilon vertices required here.

## 2. Every root in (1) has a complete small-corner own chart

Work with one actual root X, its genuine direction e, support point
P=d*e and small actual vertex W. If e is an own side axis, X has
radial interval [epsilon,d] and therefore avoids closed O.

Otherwise P is a strict actual vertex. It is not W, because d>1
while |W|<=2epsilon<1/30. It is not the opposite vertex either:

    |P-W|<=d+2epsilon=1+3epsilon<21/20<sqrt(2).

Thus P and W are adjacent. If O belonged to closed X, choose inward
unit own axes u,v at W so P=W+u and write W=-a*u-b*v with a,b>=0.
The actual radial norm would give

    d^2=1-2a+|W|^2<=1+4epsilon^2.

But d^2-(1+4epsilon^2)=epsilon*(2-3epsilon)>0. This contradiction
proves that closed O is outside X in the nonaligned case as well.

In the aligned case rotate e to East. The transverse interval contains
zero because P belongs to the actual root. Reflect that own coordinate
if necessary to put the small vertex at the lower near endpoint. The
actual chart is then

    X=[a,1+a] x [-beta,1-beta],
    a=epsilon, beta>=0,
    W=(a,-beta), |W|^2=a^2+beta^2<=4epsilon^2.           (2)

In the nonaligned case direct both own axes toward P. Both coordinates
of P are positive and have squared sum d^2. Because O is outside the
closed root, one coordinate is strictly greater than one. There is at
most one, since d<61/60<sqrt(2). Use that coordinate first and reverse
the other own axis. The actual root becomes

    X=[a,1+a] x [-beta,1-beta],
    0<a<=epsilon, beta>0,
    P=(1+a,-beta), (1+a)^2+beta^2=d^2.                 (3)

Here beta^2<d^2-1<121/3600, so beta<11/60. The two far vertices
have first coordinate greater than one, and the other near vertex
has ordinate 1-beta>49/60. Therefore the vertex satisfying (1) must
be exactly W=(a,-beta). There is no unexamined near-corner choice.

Both (2) and (3) imply the following uniform bounds:

    epsilon-(3/2)epsilon^2<=a<=epsilon,
    0<=beta<(7/4)epsilon.                              (4)

For (2), beta^2<=3epsilon^2<(49/16)epsilon^2. For (3), the exact
radial identity is

    d^2=1+2a+|W|^2.

It gives the lower bound on a. That lower bound is positive, and

    beta^2<=4epsilon^2-a^2
      <=3epsilon^2+3epsilon^3-(9/4)epsilon^4
      <(61/20)epsilon^2<(49/16)epsilon^2.

The last rational reserve is 49/16-61/20=1/80. This proves the
strict beta bound, retaining equality in the original vertex condition.

## 3. Each actual root occupies one uniformly long inner-circle arc

Put rho=9/8. In each unchanged actual root frame from (2)--(3),
the open first-quadrant arc

    acos((1+a)/rho)<theta<asin((1-beta)/rho)             (5)

lies in int(X). Its two far-face inequalities are exactly the two
endpoint conditions in (5). Its first coordinate is at least
sqrt(rho^2-1)=sqrt(17)/8>1/2>a, and its second coordinate is
positive, so both remaining own-face inequalities are strict.

Neither the full root intersection nor any extra square's full
intersection is assumed connected. Only the actual contained arc (5)
is used. Its endpoints are on actual faces and are not counted as
open-interior points.

By (4), the length of (5) is bounded below by

    f(epsilon)=asin((1-(7/4)epsilon)/rho)
       -acos((1+epsilon-(3/2)epsilon^2)/rho).            (6)

This function decreases on the entire closed comparison interval
0<=t<=1/60. To verify it without an angle sample, differentiate:

    f'(t)=-(7/4)/sqrt(rho^2-(1-(7/4)t)^2)
       +(1-3t)/sqrt(rho^2-(1+t-(3/2)t^2)^2).

The negative term has magnitude at least
(7/4)/sqrt(rho^2-(233/240)^2). The positive term is at most
1/sqrt(rho^2-(61/60)^2). The former is strictly larger, since

    (49/16)*(rho^2-(61/60)^2)
       -(rho^2-(233/240)^2)=5951/15360>0.

All denominators are positive throughout this closed interval. Hence
f'(t)<0, and the actual epsilon<1/60 gives

    length(5)>L0=asin(233/270)-acos(271/300).            (7)

The strictness also follows from the strict beta bound, but no such
extra strictness is needed for the decreasing endpoint comparison.

Define

    C=11159/13500, delta0=acos(C).

The angle L0 lies in (0,pi/2): positivity follows from
(233/270)^2+(271/300)^2>1. Its exact cosine is

    cos(L0)
      =[sqrt(1366810451)+sqrt(898971551)]/81000
      <(36971+29983)/81000=11159/13500=C.               (8)

The strict integer square reserves for (8) are 44390 and 8738.
Cosine decreases on (0,pi/2), so L0>delta0. Consequently every
one of the three actual roots has an open occupied arc of length
strictly greater than delta0.

## 4. The other six actual units have their full original angular budgets

The genuine radial point gives an actual inward segment of length
one in each root, so the root contains epsilon*e_i. This elementary
unit-support property holds at a side point or strict vertex: the
components of the inward unit normal along the two inward unit edges
lie in [0,1]. Thus the three roots meet the closed D_(1/60).

Assume a nine-unit collection for contradiction. Apply the complete
uniform center-component theorem

    THREE_NEAR_UNITS_COMPLETION_CENTER_COMPONENT_ARCS_AND_REAL_S_LEAF_BUDGET_2026_10_29.md.

It preserves every actual completing square and every disconnected
circle intersection. Of the three completion units beyond the roots
and their three actual leaves, at least two have center components
longer than 2pi/9. The third has its center component longer than

    phi=acos(9/10).

Each actual S leaf has the complete open circle arc of halfwidth

    alpha(d)=min(acos(d/rho),asin(4/9))
       >alpha0=acos(122/135).

The source proves this at the whole physical leaf and its transverse
endpoints; no abstract radial ray substitutes for the real unit.

All these actual open-interior arcs are disjoint. The three root arcs,
three full leaf arcs and three completion components therefore have
total angular length strictly greater than

    3delta0+6alpha0+4pi/9+phi.                         (9)

The next section proves that (9) itself exceeds 2pi, completing the
physical contradiction.

## 5. A complete strict angle-sum comparison

Let D=122/135 and set

    P=cos(3delta0)=4C^3-3C,
    U=sin(3delta0)=(4C^2-1)*sqrt(1-C^2),
    K=cos(3alpha0)=4D^3-3D,
    Q1=cos(6alpha0)=2K^2-1,
    V=sin(6alpha0)=2K*(4D^2-1)*sqrt(1-D^2),
    w=sin(phi)=sqrt(19)/10.

These explicit algebraic quantities satisfy

    -221/1000<P<-220/1000,
    -884/1000<Q1<-883/1000,
    973/1000<U<977/1000,
    467/1000<V<469/1000,
    435/1000<w<436/1000.                              (10)

For complete verification, the rational polynomials are

    P=-135740519821/615093750000,
    K=593042/2460375,
    Q1=-5350047513097/6053445140625.

The radical comparisons used for the remaining bounds are

    281/500<sqrt(1-C^2)<563/1000,
    107/250<sqrt(1-D^2)<429/1000,
    435/1000<sqrt(19)/10<436/1000,

with exact radicands

    1-C^2=57726719/182250000,
    1-D^2=3341/18225.

All displayed radical bounds follow by positive squaring. Multiplying
the first by 4C^2-1>0 gives the stated U bounds; multiplying the
second by 2K*(4D^2-1)>0 gives the stated V bounds. Thus (10)
is one continuous exact angle calculation, not a pose or angle grid.

Put T=3delta0+6alpha0+phi. The cosine addition formula gives

    cos(T)=(9/10)*(P*Q1-U*V)-w*(U*Q1+P*V).

Retaining all product signs in (10),

    cos(T)>
      (9/10)*(220/1000)*(883/1000)
      -(9/10)*(977/1000)*(469/1000)
      +(435/1000)*(973/1000)*(883/1000)
      +(435/1000)*(220/1000)*(467/1000)
      =36173673/200000000
      >7/40.                                         (11)

The last exact reserve is 1173673/200000000.

For the other angle, h(x)=4x^3-3x decreases strictly on (0,1/2).
Since cos(4pi/9) is in that interval and h(cos(4pi/9))=-1/2,

    -1/2-h(7/40)=57/16000>0

gives cos(4pi/9)<7/40.

The required branch is explicit. We have

    pi/6<delta0<pi/5,
    pi/8<alpha0<pi/6,
    pi/8<phi<pi/6.

For delta0, use C<sqrt(3)/2 and C>13/16>cos(pi/5), the
latter following from sqrt(5)<9/4. For alpha0 and phi, their
cosines lie between sqrt(3)/2 and cos(pi/8); the upper comparisons
follow from cos(pi/8)^2>(2+7/5)/4=17/20. Hence

    pi<11pi/8<T<53pi/30<2pi.

Cosine is strictly increasing on this entire branch. Combining (11)
with cos(4pi/9)=cos(14pi/9), we get T>14pi/9. Therefore

    3delta0+6alpha0+phi+4pi/9>2pi,

as required in (9). The nine disjoint actual open-interior arcs
cannot have this total length. This proves the complete theorem.

## 6. Retained scopes and the remaining broad-root alternative

Every radius endpoint in the original closed window is retained:
the high-S theorem handles d<=1 and all D assignments before this
physical theorem; the original upper endpoint still has epsilon<1/60.
The small-vertex bounds in (1) are weak and include equality. Every
strict reserve used later was proved from those weak premises.

No arbitrary root is given a true3 equation or an origin-containing
frame. Closed-origin avoidance and the full own-frame alternatives
were derived in Section 2 separately for each actual root. Every
original force, support, mean, circle coefficient and zero-stress
physical contact remains unchanged.

The whole high three-root physical domain still permits a root with
no actual vertex in D_(2epsilon). The accepted two-4epsilon-vertex
result does not remove that remaining alternative. A later proof
must handle the actual broad-root geometry or supply an independent
full-star contradiction. This manuscript gives no whole house/fan
flag or unrestricted three-genuine-root closure.

## 7. Exact operative inputs

| Source | SHA256 | Exact role |
| --- | --- | --- |
| THREE_NEAR_UNITS_COMPLETION_CENTER_COMPONENT_ARCS_AND_REAL_S_LEAF_BUDGET_2026_10_29.md | fdc1a41c0f405782b2b4f901d45a3c05a6aa56bc9529ea50a48e5a7f14faf9fa | Entire actual completion-center, component-length and real-leaf budget, including disconnected full intersections and all three extras |
| REVIEW_THREE_NEAR_COMPLETION_CENTER_COMPONENT_ARCS_AND_REAL_LEAF_BUDGET_ROOT_2026_10_29.md | 81638861aa5e78f6e8a6ffef5b34f3d790054425223ca48549f3dfd2b495276c | Existing independent full acceptance of the exact preceding source, as reported by root |
| THREE_GENUINE_LEAF_ROOTS_HIGH_S_REDUCTION.md | 41c6686127871c7c99ab69c84292f04c995a8530eb02cde0235cdacc181ae73f | Only the original full-window export: whole low/critical/D exit and actual high-S leaf geometry at arbitrary root degrees |

The small-corner chart, root arc and strict angle-sum calculation are
new proofs and require full independent review. The existing root
review of the component theorem does not supply their acceptance.

No original flag, metadata or ledger was edited. No actual square,
force, normal or mean was changed. No pose sampling, angle mesh,
packing certificate, Lean/Lake, CI/workflow, remote mutation or merge
was used.
