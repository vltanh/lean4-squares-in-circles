# Table-free exclusion of both three-share alternating C6 matchings

Date: October 25, 2026.

**Status: accepted analytic replacement after independent full source and
original-scope review; see REVIEW_C6_THREE_SHARE_TABLE_FREE_2026_10_25.md.** This replaces the 45-coefficient angular certificate in
`SIX_CYCLE_THREE_SHARED_MATCHING_EXCLUSION.md`. It introduces no contact
subdivision, gate ID, numerical premise, or new restriction on the original
positive forces. The existing physical derivation and reflection cover
remain unchanged. No Lean compilation or CI was run.

The only computations in the proof below are displayed identities and
comparisons of a fixed handful of rational numbers and square roots.
There is no polynomial coefficient list, Bernstein expansion, interval
subdivision, or external sign checker in the proof dependency.

## 1. The same original force-value identity

Retain the complete original all-unique, all-side-transmitter alternating
C6 and all three additional physical squares. The accepted strict-turn
and double-shared-channel results give

    pi/2 < theta_i <= 3pi/4,       sum theta_i=2pi,

and make three genuine shares one of the two cyclic perfect matchings.
For the incoming matching, the original means and support equations give
exactly

    R sum D_i = sum mu_i[2+sin(theta_i)-cos(theta_i)],       (1)
    D_i = sqrt(mu_(i-1)^2+mu_i^2
                         -2mu_(i-1)mu_i cos(theta_i)),
    mu_i>0.

Sections 1--2 of `SIX_CYCLE_THREE_SHARED_MATCHING_EXCLUSION.md` prove
(1) at the actual shared means, including their endpoint values. They
also carry the outgoing matching to the incoming one by a reflection
and reversal of cyclic labels, preserving every original force,
physical corner, mean, transmitter position and completion square.

Here is a stronger, entirely analytic replacement for its scalar lemma.
Put K=79/40. On the whole closed enlargement

    pi/2 <= theta_i <= 3pi/4,       sum theta_i=2pi,

every positive force triple satisfies

    K sum D_i - sum mu_i[2+sin(theta_i)-cos(theta_i)]
                         > (sum mu_i)/2500.                (2)

Consequently (1) implies R<K and contradicts the original radius floor.
No use of transmitter positions or completion capacity is made.

## 2. Eliminate all force ratios while retaining exact half angles

Normalize sum mu_i=1 for this homogeneous inequality, and put

    alpha_i=pi-theta_i,       pi/4<=alpha_i<=pi/2,
    sum alpha_i=pi,          s_i=cos(alpha_i/2),
    c_*=3/40,               xi_i=mu_i-1/3.

For positive a,b and 0<=s<=1, the elementary square-root chord inequality
is

    sqrt(s^2(a+b)^2+(1-s^2)(a-b)^2)
       >=s(a+b)+(1-s)(a-b)^2/(a+b).                       (3)

To prove it, divide by a+b and use concavity of sqrt on the chord
joining s^2 and 1. Throughout the closed alpha interval,

    1-s_i >= 1-cos(pi/8) > 3/40.

The final strict comparison follows by squaring positive quantities:
cos(pi/8)<37/40 is equivalent to 400sqrt(2)<569, and
569^2-2*400^2=3761>0. Since mu_(i-1)+mu_i<=1, (3) gives

    sum D_i >= sum mu_i(s_i+s_(i+1))
                         +3c_* sum xi_i^2.                (4)

Define the exact half-angle coefficients

    q_i=K[cos(alpha_i/2)+cos(alpha_(i+1)/2)]
                           -2-sin(alpha_i)-cos(alpha_i),
    qbar=(sum q_i)/3,
    V=sum(q_i-qbar)^2,
    B=(711/400)sum q_i-3V.                               (5)

Complete the square in the unrestricted xi_i:

    K sum D_i-sum mu_i[2+sin(alpha_i)+cos(alpha_i)]
      >= qbar+sum xi_i(q_i-qbar)+3Kc_*sum xi_i^2
      >= qbar-V/(12Kc_*)
       = B/(36Kc_*),                                    (6)

where 12Kc_*=711/400 and 36Kc_*=2133/400. Thus it suffices to prove

    B > 2859/1088000.                                   (7)

Unlike the previous certificate, (5) keeps the exact half angles.
Their extra margin permits the following elementary Taylor estimates.

## 3. Three-variable identities and the exact angle domain

Set

    delta_i=alpha_i-pi/3,       S=sum delta_i^2,
    r=sum delta_i^3,
    Pz=z-(sum z_i)/3,

where P is orthogonal projection onto the plane of zero-sum triples.
Then sum delta_i=0 and

    -pi/12<=delta_i<=pi/6,
    0<=S<=pi^2/24,
    sum delta_i^4=S^2/2,
    P(delta^3)=(S/2)delta,
    ||P(delta^2)||^2=S^2/6,
    |r|<=S sqrt(S/6).                                   (8)

Powers in (8) are coordinatewise. For the bound on S, put
x_i=delta_i+pi/12>=0. Their sum is pi/4, so
sum x_i^2<=(pi/4)^2; subtracting 3(pi/12)^2 gives the result.
The fourth-power identity follows by expanding (sum delta_i)^2=0.
The cubic identity follows because the three delta_i are roots of
X^3-(S/2)X-delta_0 delta_1 delta_2. The last inequality is Cauchy
applied to r=delta dot P(delta^2).

We use only the elementary exact bounds

    265/153 < sqrt(3) < 97/56,
    sqrt(2)<99/70,       pi<22/7.                        (9)

The square-root comparisons have respective squared integer reserves
2, 1 and 1. For completeness, the classical upper bound on pi follows
from the strictly positive integral

    integral_0^1 x^4(1-x)^4/(1+x^2) dx = 22/7-pi > 0.

In particular

    sqrt(S/6)<11/42,       S<121/294,
    max |delta_i|<11/21.                                (10)

## 4. A lower bound for the sum of the exact coefficients

Let

    F(alpha)=2K cos(alpha/2)-sin(alpha)-cos(alpha),
    q_eq=59sqrt(3)/40-5/2.

Then sum q_i=sum F(alpha_i)-6. At alpha=pi/3,

    F(pi/3)-2=q_eq,
    F''(pi/3)/2=1/4+sqrt(3)/320,
    F'''(pi/3)/6=239/1920-sqrt(3)/12 < 0.

On the entire closed angle interval,

    F''''(alpha)=(K/8)cos(alpha/2)-sin(alpha)-cos(alpha)
                                                     >=-sqrt(2).

Taylor's theorem through cubic order, summed over the three angles,
therefore gives

    sum q_i >= 3q_eq+(1/4+sqrt(3)/320)S
           +(239/1920-sqrt(3)/12)r-(sqrt(2)/48)S^2.

Apply (8)--(10), with the sign of the cubic coefficient retained. The
coefficient of S is strictly larger than

    1/4+(265/153)/320
       -[(97/56)/12-239/1920]*(11/42)
       -[(99/70)/48]*(121/294)
      =19/80+39169/67173120.

Thus the simple bound needed below is

    sum q_i >= 3q_eq+(19/80)S.                          (11)

This includes S=0, where the three angles are equal and the equality
in (11) is harmless.

## 5. A variance bound from one cubic Taylor expansion

Let C be the cyclic shift (Cz)_i=z_(i+1), and put

    A(alpha)=K cos(alpha/2)-sin(alpha)-cos(alpha),
    D(alpha)=K cos(alpha/2).

Thus q_i=A(alpha_i)+D(alpha_(i+1))-2. The Taylor coefficients at pi/3
through order three are

    a=-159/160+sqrt(3)/2,       b=-79/160,
    c=1/4+81sqrt(3)/640,       d=-79sqrt(3)/640,
    p=133/1280-sqrt(3)/12,     q=79/3840.               (12)

Here (a,b) are the first derivatives, (c,d) the second derivatives
divided by two, and (p,q) the third derivatives divided by six.
Write L_(u,v)=uI+vC. Because P commutes with C, (8) gives exactly

    P(q_0,q_1,q_2)
       =L_(a+(S/2)p,b+(S/2)q) delta
           +L_(c,d)P(delta^2)+P epsilon,              (13)

where epsilon is the sum of the actual fourth-order Taylor remainders.

### 5.1. The two fixed circulant norms

For every zero-sum triple z,

    z dot Cz=-||z||^2/2,
    ||L_(u,v)z||^2=(u^2+v^2-uv)||z||^2.              (14)

All constants in the following calculation are displayed explicitly:

    a^2+b^2-ab = 38161/25600-239sqrt(3)/320
                                                    <(111/250)^2,
    c^2+d^2-cd = 83203/409600+241sqrt(3)/2560
                                                    <(303/500)^2,
    L = 2ap+2bq-aq-bp
      = -124441/307200+335sqrt(3)/1536 < -1/40,
    Q = p^2+q^2-pq
      = 441121/14745600-719sqrt(3)/46080 < 1/300.

Each comparison follows directly by substituting the appropriate
upper or lower sqrt(3) bound in (9). Their positive rational reserves
are, in order,

    193303/2448000000,   1861287/1792000000,
    619/268800,         999943/2256076800.

For 0<=t=S/2<1/4, the first squared norm in (13) is

    (a+tp)^2+(b+tq)^2-(a+tp)(b+tq)
       =(a^2+b^2-ab)+tL+t^2Q
       <=a^2+b^2-ab,

because L+tQ<-1/40+1/1200<0. Hence the cubic correction does not
increase the norm of the linear term in (13).

### 5.2. The entire fourth-order remainder

On pi/4<=alpha<=pi/2,

    A''''(alpha)=(K/16)cos(alpha/2)-sin(alpha)-cos(alpha),
    D''''(alpha)=(K/16)cos(alpha/2).

The first expression is negative and has absolute value at most
sqrt(2); the second has absolute value at most K/16. Taylor's theorem,
the norm-one property of P, and the triangle inequality give

    ||P epsilon||
       <=(sqrt(2)+K/16)||delta^4||/24
       <=(sqrt(2)+K/16)(max |delta_i|)^3 sqrt(S)/24.

Using (9),

    sqrt(2)+K/16 < 99/70+79/640 < 77/50.

The last rational difference is 51/22400. For S>0, equations
(8), (10), and (13)--(14) consequently give

    sqrt(V/S)
       <111/250+(303/500)(11/42)+(77/1200)(11/21)^3
        =153/250-101/1587600
        <153/250.

Finally

    3/8-(153/250)^2=57/125000>0.

Thus, including the S=0 case separately,

    V <= (3/8)S.                                     (15)

The inequality is strict whenever S>0. No angle subdivision or
uncontrolled Taylor remainder is present.

## 6. Strict scalar gap and the complete physical conclusion

Insert (11) and (15) into (5):

    B >= (2133/400)q_eq
              +[(711/400)(19/80)-9/8]S.

The coefficient of S is negative. Using (9)--(10) with this sign,

    B > (2133/400)[(59/40)(265/153)-5/2]
              +[(711/400)(19/80)-9/8](121/294)
       =2859/1088000 > 0.

This proves (7). Equation (6) now gives the normalized force gap

    K sum D_i-sum mu_i[2+sin(alpha_i)+cos(alpha_i)]
       >953/1933920 >1/2500.

Rescaling the original positive magnitudes proves (2). Apply it to
the unchanged physical identity (1), and then use the already accepted
reflection/reversal for the other matching. Both complete three-share
families are excluded, including theta_i=3pi/4, every original
shared-mean endpoint, both radius endpoints, all positive force ratios,
all actual transmitter positions and all three additional squares.

This source replaces only the angular-certificate dependency of the
three-share theorem. The accepted double-shared-channel theorem is
still used to establish that the three shares form a perfect matching;
its separate 209-coefficient proof is not removed here. The one- and
two-share completion families and the strictly obtuse one-radial family
remain open. No existing gate is newly checked by this replacement.
