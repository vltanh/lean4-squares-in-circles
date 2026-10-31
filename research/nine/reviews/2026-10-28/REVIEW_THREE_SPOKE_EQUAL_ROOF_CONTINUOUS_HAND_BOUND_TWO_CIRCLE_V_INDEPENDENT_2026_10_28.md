# Independent full review of the continuous equal-roof scalar replacement

Date: October 28, 2026 UTC.

Reviewer: two_circle_v_review continuation, independently of the two
authors of the scalar proof. The reviewer did not contribute a discovery
argument, endpoint estimate, identity, or correction to the source before
its freeze.

**Verdict: PASS, without a source repair.** The complete original coupled
scalar domain implies the stronger strict inequality D0>17/8, and hence
the exact old export D0>21/10. This is a review of the entire proof, not
only the last polynomial or the difference from the old certificate.

## 1. Exact reviewed bytes and scope

The complete current source read and checked is

    THREE_SPOKE_EQUAL_ROOF_SEPARATION_CONTINUOUS_HAND_BOUND.md
    SHA256 495ffa7f6214724d9be9a02974e4729708d7eb9a057c94d8e11dbbe0f5733143.

The complete historical source was also read, for literal theorem and
coupling comparison:

    THREE_SPOKE_EQUAL_ROOF_SEPARATION_SCALAR.md
    SHA256 1297f7864dd3d629330f9741d7728fe894a3bf6c1beac4192fd1800da38cdeca.

The new theorem is self-contained real analysis and algebra. The old
Bernstein polynomial, its enlarged rectangles, row-floor table, and
checker are not inputs to the new proof. Its only use of the old file is
to identify precisely the scalar theorem whose export it replaces.

Both sources use exactly

    a>b>0, a^2+b^2=1,
    (a-b)/(a+b)<p<b/a, H=b+ap<1,
    t=1-H, Delta=b-a+p(a+b), J=a(1-p)+t Delta,
    theta=t Delta/J, v=t/(1-pH),
    rho0=(1-theta)(a-bp)-theta pH,
    D0=[rho0+1-pt+(1-pv)/sqrt(1+v^2)]/sqrt(1+p^2).

The change of name from rho to rho0 avoids confusion with a circle
radius; it changes no expression. There is no independent relaxation of
theta, v, H, an application mean, or any other parameter. No force,
geometric, mask, degree, or radius premise is added.

This scalar review does not by itself retire a geometric caller's
dependency, change a family flag, or claim an original-row closure.
Adoption still requires the separate exact caller join. It also does
not cover the distinct hub-owner scalar packet.

## 2. Original signs and exact decomposition

The two positive strict p bounds give 0<p<1; H is positive and less
than one. Thus t, Delta, J, and 1-pH are positive. The equality

    1-pH-t=H(1-p)>0

proves 0<v<1. All original square roots and denominators are valid.
The split at b=1/2 proves p<1/sqrt(3), including the meeting case:
b/a<=1/sqrt(3) below that value, and
(1-b)/a=sqrt((1-b)/(1+b))<=1/sqrt(3) above it.

With u=1+p^2, q=1-p, and T=a-bp, I checked

    T>0, Delta=H-T, H^2+T^2=u, T+pH=au.

The inequality p<b/a gives a^2u<a^2+b^2=1. The identity

    rho0+1-pt=q+(1-theta)au

therefore gives exactly

    D0=F-theta a sqrt(u),
    F=q/sqrt(u)+a sqrt(u)+(1-pv)/(sqrt(u)sqrt(1+v^2)).

No inequality or lost sign enters this decomposition. Consequently
theta<3/40 and F>11/5 imply D0>17/8 strictly, since
0<a sqrt(u)<1.

## 3. Entire theta bound

The existence of p between its two strict bounds gives
a^2-b^2<2ab. Both sides are positive, so squaring is valid and gives
ab>1/(2sqrt(2)). Hence L=a+b>13/10 and a>7/10.

For r=(L-1)/a, the printed identity

    r=1-sqrt((1-b)/(1+b))

gives r<2-sqrt(2)<3/5; a<1 gives r>L-1>3/10. Thus
L=1+ar>1+(7/10)r holds with the required strict sign.

I independently expanded a(1-p)=L-H and a Delta=LH-1.
Multiplying the positive denominator of theta shows that theta<3/40
is exactly the positivity of

    Q(H)=cL H^2-[c(L+1)+a]H+c+aL, c=37/3.

The negative discriminant identity is exact:

    [4cL(c+aL)-[c(L+1)+a]^2]/a^2
      =r[2c(2L+1)-c^2r]-1
      >74r-(5291/45)r^2-1.

The last concave quadratic has positive values 5309/500 and 134/125
at r=3/10 and r=3/5. This proves positivity on the entire closed
interval, not merely at sampled r. The leading coefficient cL is
positive, so Q is positive for every real H. This proves the whole
original-domain bound theta<3/40 with no omitted endpoint assumption.

## 4. Exhaustive closed fixed-p intervals

For psi=arctan(p), phi=arctan(b/a), and alpha=phi+psi,
the original domain is precisely

    max(pi/4,2psi)<alpha<min(pi/4+psi,pi/2-psi).

I checked each equivalence separately: Delta>0 gives alpha>pi/4;
p<b/a gives alpha>2psi; a>b gives alpha<pi/4+psi; and H<1 gives
alpha<pi/2-psi. All angles are in the increasing branch of sine.
Conversely alpha in this interval reconstructs phi=alpha-psi in
(0,pi/4) and all original strict inequalities.

Both endpoint switches occur at psi=pi/8. Thus the complete closed
fixed-p cover is exactly the printed pair:

| Closed p range | Lower H endpoint | Upper H endpoint |
| --- | --- | --- |
| [0,sqrt(2)-1] | sqrt(1+p^2)/sqrt(2), Delta=0 | (1+p)/sqrt(2), a=b |
| [sqrt(2)-1,1/sqrt(3)] | 2p/sqrt(1+p^2), p=b/a | 1, H=1 |

The two lower formulas agree at the switch; the two upper formulas
also agree there. At p=0 and p=1/sqrt(3), the appropriate interval
degenerates to one point, which is covered by the endpoint estimates.
Throughout these closed auxiliary intervals, H>=T>0, 0<H<=1,
T^2<=u/2, u<=4/3, q>0, and 0<=v<1. In particular, the extension
does not introduce a zero T, a zero K, or a vanishing denominator.

The variable t=1-H reverses the interval without changing its
endpoints or the exhaustiveness of the cover. The theta bound need
only hold on the original strict domain; it is not asserted on an
unrelated extension in this part of the proof.

## 5. Full concavity, including derivative signs

At fixed p, let

    K=sqrt((q+pt)^2+t^2), T=sqrt(p^2+2t-t^2).

I checked the exact rewrite

    F=[1+T-pt+q/K]/sqrt(u),

using 1-pH=q+pt and 1-pv=q/(q+pt). Direct differentiation gives

    T''=-u/T^3, K''=q^2/K^3,
    (q/K)''=q(2uK^2-3q^2)/K^5.

Thus the printed second derivative of the numerator is correct.
The negative term has magnitude at least sqrt(6)>12/5 by
T^2<=u/2 and u<=4/3.

For z=K/q>0, the other term is
(2uz^2-3)/(q^2z^5). Its global maximum in z occurs at
z^2=5/(2u), as its derivative has sign 15-6uz^2. The maximum is
2(2u/5)^(5/2)/q^2. The proof validly bounds this by a number less
than 12/5 using u<=4/3, q>21/50, and sqrt(8/15)<11/15.
The comparisons have the correct directions even if the original
second term is negative. I checked the integer reserves 23 and
260500 printed for these bounds.

Therefore F''<0 on each nondegenerate fixed-p interval. F is
continuous at both endpoints, so its value is at least the smaller
endpoint value. Strict endpoint bounds consequently suffice for a
strict bound everywhere; no interior parameter subdivision is used.

## 6. Both first-range endpoint curves

The common formula

    C=1/sqrt(1+W^2), W=(p+v)/(1-pv)=[1+p-uH]/q>=0

is valid on the complete closed cover because p,v>=0 and pv<1.
The tangent-addition angle lies in [0,pi/2), so there is no cosine
sign ambiguity.

On Delta=0, the first two terms are

    g=q/sqrt(u)+(1+p)/sqrt(2).

The printed derivative is negative because p^2<1/5 and u^3<2.
At the largest p, g=1+sqrt(1-1/sqrt(2))>3/2. The inequality
W<1 is equivalent to 2p<u^(3/2)/sqrt(2), whose positive squared
difference is 1-5p^2+3p^4+p^6. The previously established
p^2<1/5 makes it strictly positive, including p=0 and p=p_star.
Thus C>1/sqrt(2)>7/10 and F>11/5.

On a=b=1/sqrt(2), the derivative of
g=q/sqrt(u)+(1/sqrt(2))sqrt(u) is negative throughout the interval.
Its endpoint value sqrt(1+1/sqrt(2)) exceeds 653/500, with the
printed rational squared reserve 35509/24750000.

For the remaining term, W<1/2 is exactly the inequality K0<0
printed in Section 6. The first bound covers 0<=p<=1/10. The
second covers p>=1/10 using -2p^3<=-(1/5)p^2. These ranges meet
without a lost endpoint. The resulting quadratic has negative
leading coefficient and discriminant -607/4900, so it is strictly
negative on all real p. This proves C>2/sqrt(5)>447/500, with
the correct squared reserve 191/250000. Adding the two strict
bounds gives F>11/5 on the complete a=b curve.

## 7. The full H=1 curve

At H=1, t=v=0 and T=p. The exact simplification is

    F=(2+p)/sqrt(1+p^2).

The entire relevant p range lies within [2/5,3/5]. Both sides of
the target comparison are positive, so the squared difference is
equivalent to the desired strict bound. Its numerator
-21+100p-96p^2 is concave and has values 91/25 and 111/25 at
the endpoints of this larger interval. It is therefore strictly
positive on the whole interval, including both original endpoints.

## 8. The full p=b/a curve and complete polynomial check

At p=b/a, writing R_p=sqrt(1+p^2) gives
a=1/R_p, b=p/R_p, H=2p/R_p and

    F=1+q/R_p+C, w=W=(1+p-2pR_p)/q.

The proof establishes 0<w<1 with the correct strict signs: H<=1
gives the numerator at least pq>0, and R_p>1 gives it less than q.

The tangent to the convex function (1+z)^(-1/2) at z=1/2 is
(7-2z)/(3sqrt(6)). Consequently

    C>=(7-2w^2)/(3sqrt(6))>(20/147)(7-2w^2).

The second inequality is strict because sqrt(6)<49/20 and
7-2w^2>0. Substituting the desired upper bound for w^2 then
gives q/R_p+C>6/5 exactly; there is no rounding loss.

I independently expanded the identity in Section 8. In particular,
expanding the square in w gives

    100 R_p q^2[(147/40)q/R_p-91/100-w^2]
      =(735/2)q^3+400p(1+p)(1+p^2)
       -R_p[91q^2+100(1+p)^2+400p^2(1+p^2)]
      =A-R_p B,

with B=191+18p+591p^2+400p^4>0. Every multiplied factor is
positive. The concave square-root tangent and sqrt(5)>67/30
give the correct strict upper bound

    R_p<=(9/4+p^2)/sqrt(5)<(135+60p^2)/134.

Because B>0, this is the correct direction for a strict lower
bound on A-R_p B. I checked all seven coefficients of

    P=134A-(135+60p^2)B
      =23460-96565p+110090p^2+3275p^3-35860p^4-24000p^6,

including the zero fifth-degree coefficient. I also checked every
coefficient of its complete substitution p=3/5-z:

    468/5+(77512/25)z-(40643/5)z^2+186469z^3
      -165460z^4+86400z^5-24000z^6.

The entire original p interval is in [2/5,3/5], hence 0<=z<=1/5.
For each negative higher-power term, z^j<=z/5^(j-1) gives a
valid lower bound after multiplication by its negative coefficient.
Dropping the two nonnegative terms also gives a lower bound. The
remaining coefficient of z is exactly 717/5, so

    P(3/5-z)>=468/5+(717/5)z>0.

This includes z=0 and z=1/5. It is a single explicit whole-interval
estimate, not an unprinted coefficient packet or a numerical sign
test. It proves the required strict comparison for w^2 and hence
F>11/5 on the complete last endpoint curve.

## 9. Conclusion, arithmetic verification, and adoption limit

Every closed auxiliary interval has both endpoint values strictly
greater than 11/5, including the switch and both degenerate limiting
intervals. The full concavity proof therefore proves F>11/5 for
every original point. The exact decomposition, theta<3/40, and
a sqrt(u)<1 prove D0>17/8.

I independently checked the printed rational reserves and the full
degree-six/shifted identities by exact fraction arithmetic in addition
to the hand derivations above. This was verification of displayed
identities and rational comparisons; no sampled domain, coefficient
search, executable exclusion result, or numerical maximum is an
assumption of this review. No Lean/Lake, CI, remote write, commit,
normal reselection, source repair, or original-row mutation occurred.

The exact unchanged export follows from

    17/8-21/10=1/40>0.

Both radius comparisons are also correct:

    21/10-25/12=1/60,
    17/8-25/12=1/24.

The old scalar's 660+528=1188 coefficient obligations may therefore
be replaced in any caller that establishes precisely the full original
domain and literal coupling recorded in Section 1. The separate
caller review determines the actual dependency retirement. Other
scalar packets and the full original-family gates remain outside
this independent scalar verdict.
