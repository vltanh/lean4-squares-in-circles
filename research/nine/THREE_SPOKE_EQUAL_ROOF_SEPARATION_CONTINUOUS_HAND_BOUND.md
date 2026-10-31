# A continuous hand bound for the equal-roof separation scalar

Date: October 28, 2026.

Authors: W-continuation and root. W-continuation derived the uniform
theta bound, the global bound proving concavity, and the Delta=0 and
a=b endpoint estimates. Root supplied the exact F decomposition,
the second-derivative formula, and the p=b/a and H=1 endpoint estimates.
Both authors checked the combined argument. A separate independent
review is required before adopting the certificate replacement.

**Status: complete continuous scalar proof, frozen for independent
review.** The conclusion below holds on the entire original coupled
scalar domain. The proof has no numerical sampling, interval-leaf,
Bernstein-table, or executable-certificate premise. Exploratory
computations were used during discovery; none is an assumption or
inference in this proof. All estimates used here are printed below.

The exact original scalar theorem is recorded in
THREE_SPOKE_EQUAL_ROOF_SEPARATION_SCALAR.md, SHA256

    1297f7864dd3d629330f9741d7728fe894a3bf6c1beac4192fd1800da38cdeca.

That source's two tensor tables contain 660+528=1188 coefficients.
The present proof establishes a stronger conclusion for the same
literal scalar, with the same domain and coupling. It does not claim
positivity of the older auxiliary rational polynomial on enlarged
rectangles. A separate exact caller join determines which existing
uses can replace that older proof.

## 1. Whole original domain and stronger conclusion

Let a,b,p be real numbers satisfying

    a>b>0,       a^2+b^2=1,
    (a-b)/(a+b)<p<b/a,
    H=b+ap<1.

Define, without an independent relaxation of any variable,

    t=1-H,
    Delta=b-a+p(a+b),
    J=a(1-p)+t Delta,
    theta=t Delta/J,
    v=t/(1-pH),
    rho0=(1-theta)(a-bp)-theta pH,

    D0=[rho0+1-pt+(1-pv)/sqrt(1+v^2)]/sqrt(1+p^2).

**Theorem.** On this entire domain,

                         D0>17/8>21/10.                 (1)

In particular, the exact original export D0>21/10 is preserved.
No packing, force, degree, mask, mean, or circle-radius assumption is
added to the scalar theorem.

The domain gives 0<p<1, 0<H<1, t>0, Delta>0, J>0, and
0<theta<1. Moreover

    1-pH-t=H(1-p)>0,

so 0<v<1 and all displayed denominators are positive. In fact

                         0<p<1/sqrt(3).                  (2)

If b<=1/2, the upper bound p<b/a is at most 1/sqrt(3).
If b>=1/2, the bound H<1 gives

    p<(1-b)/a=sqrt((1-b)/(1+b))<=1/sqrt(3).

These two alternatives include b=1/2.

For the proof set

    u=1+p^2,       q=1-p,       T=a-bp.

Here T>0: p<b/a implies T>(a^2-b^2)/a>0. Direct expansion gives

    Delta=H-T,       H^2+T^2=u,       T+pH=au.             (3)

Also p<b/a implies

                         a sqrt(u)<1.                    (4)

Using t+H=1, the exact identity

    rho0+1-pt=q+(1-theta)au

rewrites the required scalar as

    D0=F-theta a sqrt(u),
    F=q/sqrt(u)+a sqrt(u)+(1-pv)/(sqrt(u)sqrt(1+v^2)).     (5)

We prove theta<3/40 and F>11/5. Equations (4)--(5) then give

    D0>11/5-3/40=17/8,
    17/8-21/10=1/40>0.

## 2. A uniform bound theta<3/40

Write

    L=a+b,       r=(L-1)/a,       c=37/3.

The two strict p bounds imply

    a(a-b)<b(a+b),
    a^2-b^2<2ab,
    ab>1/(2sqrt(2)).

For the last step, square the positive sides and use
(a^2-b^2)^2=1-4a^2b^2. Therefore

    L^2=1+2ab>1+1/sqrt(2)>17/10>(13/10)^2,
    L>13/10,       a>1/sqrt(2)>7/10.

Since a<1, we obtain r>L-1>3/10. For the other endpoint,

    r=1-(1-b)/a=1-sqrt((1-b)/(1+b))
      <2-sqrt(2)<3/5,

because b<1/sqrt(2) and the last expression is increasing in b.
Consequently

    3/10<r<3/5,       L=1+ar>1+(7/10)r.                 (6)

The two identities

    a(1-p)=L-H,       a Delta=LH-1

show that theta<3/40 is equivalent to

    c(1-H)(LH-1)<a(L-H).

It is thus enough to prove positivity of the quadratic

    Q(H)=cL H^2-[c(L+1)+a]H+c+aL.                       (7)

Its leading coefficient cL is positive. The negative of its
discriminant, divided by a^2, has the exact expression

    [4cL(c+aL)-[c(L+1)+a]^2]/a^2
       =r[2c(2L+1)-c^2 r]-1
       >74r-(5291/45)r^2-1.                             (8)

The strict inequality uses (6) and r>0. The last polynomial is
concave on the closed interval [3/10,3/5]; its two endpoint values are

    5309/500,       134/125.

Both are positive, so (8) is positive throughout. The quadratic
(7) has negative discriminant and positive leading coefficient,
and is strictly positive for every real H. This proves

                         theta<3/40.                    (9)

## 3. An exhaustive fixed-p interval

We will prove F>11/5 by concavity in t=1-H, retaining the exact
relation among a,b,p,H. The following closed intervals include every
original point and specify all endpoints used in the proof.

Let

    p_star=sqrt(2)-1,       psi=arctan(p),
    phi=arctan(b/a),       alpha=phi+psi.

The identities a=cos(phi), b=sin(phi) give

    H=sqrt(u)sin(alpha),       T=sqrt(u)cos(alpha).

The original inequalities are exactly the strict angle bounds

    max(pi/4,2psi)<alpha<min(pi/4+psi,pi/2-psi).          (10)

Indeed Delta>0 gives alpha>pi/4, p<b/a gives alpha>2psi,
a>b gives alpha<pi/4+psi, and H<1 gives alpha<pi/2-psi.
All these angles lie in (0,pi/2), where sine is increasing.
Conversely any alpha in (10), with fixed p, reconstructs the
original a,b by phi=alpha-psi. The endpoint switches both occur at
psi=pi/8, or p=p_star.

Taking the closed intervals in (10) therefore yields the complete
fixed-p cover

| Range of p | Lower H endpoint | Upper H endpoint |
| --- | --- | --- |
| 0<=p<=p_star | sqrt(u)/sqrt(2), where Delta=0 | (1+p)/sqrt(2), where a=b |
| p_star<=p<=1/sqrt(3) | 2p/sqrt(u), where p=b/a | 1, where H=1 |

The two endpoint formulas agree at each switch that concerns them.
At p=0 and p=1/sqrt(3), the corresponding H interval degenerates
to a point. These limiting cases are retained in the estimates.
Every interval lies in

    0<H<=1,       H>=T>0,       0<=p<=1/sqrt(3).

In particular T^2<=u/2, u<=4/3, and q>0. The variable t=1-H
ranges over the reverse closed interval, so an endpoint argument
in t has exactly the same four boundary types.

On these closed auxiliary intervals v>=0 and

    1-pH-t=Hq>0,

so v<1, pv<1, and every expression in F is still well defined.

## 4. Strict concavity on each whole interval

At fixed p set

    K=sqrt((q+pt)^2+t^2),
    T=sqrt(p^2+2t-t^2).

These are positive throughout each closed interval in Section 3.
Because 1-pH=q+pt and 1-pv=q/(q+pt), equation (5) gives

                         F=[1+T-pt+q/K]/sqrt(u).          (11)

The second derivative of the numerator, at fixed p, is

    -u/T^3 + q(2uK^2-3q^2)/K^5.                         (12)

For example, T''=-u/T^3 and K''=q^2/K^3; differentiating q/K
then gives exactly the second term in (12).

The negative term uniformly dominates the positive one. First,
T^2<=u/2 and u<=4/3 imply

    u/T^3>=2sqrt(2)/sqrt(u)>=sqrt(6)>12/5.               (13)

For the other term put z=K/q>0. It becomes

    (2uz^2-3)/(q^2 z^5).

For fixed u>0, the derivative of (2uz^2-3)/z^5 has the
sign of 15-6uz^2. Its global maximum on z>0 is attained at
z^2=5/(2u), with value 2(2u/5)^(5/2). Thus

    q(2uK^2-3q^2)/K^5
       <=2(2u/5)^(5/2)/q^2
       <=2(8/15)^(5/2)/(21/50)^2
       <(1408/3375)/(441/2500)
       <12/5.                                           (14)

Here q>=1-1/sqrt(3)>21/50, since 1/sqrt(3)<29/50.
The latter positive comparison follows from 3*29^2>50^2,
whose integer reserve is 23. The middle strict bound in (14)
uses sqrt(8/15)<11/15. The last comparison has positive integer
cross-product reserve

    12*1488375-5*3520000=260500.

Equations (12)--(14) show F''<0 on the full interior of every
nondegenerate closed interval, with continuous endpoint values.
Therefore F is concave, and its value at any point is at least the
minimum of its two endpoint values. It remains to prove F>11/5
on the four complete endpoint curves.

For convenience on every endpoint write

    C=(1-pv)/(sqrt(u)sqrt(1+v^2)).

Since p,v>=0 and pv<1, the angle arctan(p)+arctan(v) is in
[0,pi/2), so

    C=1/sqrt(1+W^2),
    W=(p+v)/(1-pv)=[1+p-uH]/q>=0.                      (15)

This records the signs needed in all cosine comparisons below.

## 5. The Delta=0 endpoint

Here 0<=p<=p_star and H=T=sqrt(u)/sqrt(2). The first two
terms in F are

    g(p)=q/sqrt(u)+(1+p)/sqrt(2),
    g'(p)=-(1+p)/u^(3/2)+1/sqrt(2)<0.                   (16)

For the sign, p^2<=p_star^2=3-2sqrt(2)<1/5, since
sqrt(2)>7/5. Hence u^3<(6/5)^3<2, and 1+p>=1 proves (16).
It follows that

    g(p)>=g(p_star)=1+sqrt(1-1/sqrt(2))>3/2,            (17)

using 1/sqrt(2)<3/4.

In (15) the tangent is

    W=[1+p-u^(3/2)/sqrt(2)]/q.

It satisfies W<1: this is equivalent to
2p<u^(3/2)/sqrt(2), and the positive squared difference is

    u^3-8p^2=1-5p^2+3p^4+p^6>0.

Together with W>=0 from (15), this gives

    C>1/sqrt(2)>7/10.

Adding (17) proves F>3/2+7/10=11/5 on this whole endpoint.

## 6. The a=b endpoint

Here a=b=sigma=1/sqrt(2), H=sigma(1+p), and
0<=p<=p_star. The first two terms in F are

    g(p)=q/sqrt(u)+sigma sqrt(u),
    g'(p)=[-1-p+sigma p u]/u^(3/2)<0,

because sigma u<=2sqrt(2)-2<1. Consequently

    g(p)>=g(p_star)=sqrt(1+sigma)>653/500.               (18)

For the last strict comparison, sigma>70/99 and

    1+70/99-(653/500)^2=35509/24750000>0.

The tangent in (15) is positive and has the form

    W=(1+p)(1-sigma u)/q.

The inequality W<1/2 is equivalent, after multiplying positive
denominators, to

    K0=(sqrt(2)-2)+(3sqrt(2)-2)p-2p^2-2p^3<0.           (19)

Use sqrt(2)<99/70. If 0<=p<=1/10, dropping the negative
higher powers gives

    K0<-41/70+(157/70)p<=-253/700<0.

If p>=1/10, then -2p^3<=-(1/5)p^2, so

    K0<-41/70+(157/70)p-(11/5)p^2<0.

The last quadratic is strictly negative for all real p: its leading
coefficient is negative and its discriminant is -607/4900. This
proves (19) throughout the endpoint, with no missing meeting value.
Therefore

    C>2/sqrt(5)>447/500,
    4/5-(447/500)^2=191/250000>0.

Together with (18), this gives F>(653+447)/500=11/5.

## 7. The H=1 endpoint

Here p_star<=p<=1/sqrt(3), t=v=0, T=p, and

                         F=(2+p)/sqrt(1+p^2).            (20)

The whole interval is contained in [2/5,3/5]: sqrt(2)>7/5
and 1/sqrt(3)<3/5. Both sides of the desired comparison are
positive. Its squared difference is

    (2+p)^2-(121/25)(1+p^2)
       =[-21+100p-96p^2]/25.                             (21)

The numerator is concave. At p=2/5 and p=3/5 its values are,
respectively, 91/25 and 111/25. Thus (21) is positive on
the whole enlarged interval, and F>11/5 follows from (20).

## 8. The p=b/a endpoint

Here p_star<=p<=1/sqrt(3), and set R_p=sqrt(1+p^2).
The subscript distinguishes this scalar radical from any packing
radius; no packing radius occurs in this theorem. We have

    a=1/R_p,       b=p/R_p,       H=2p/R_p,
    F=1+q/R_p+C.

The tangent in (15) is

    w=W=(1+p-2pR_p)/q,       0<w<1.                    (22)

For its lower bound, H<=1 gives

    1+p-uH>=1+p-u=pq>0.

Its upper bound follows from R_p>1, since
1+p-2pR_p<1-p=q.

The function (1+z)^(-1/2) is convex on z>=0. Its tangent
at z=1/2 therefore gives

    C=1/sqrt(1+w^2)>=(7-2w^2)/(3sqrt(6))
                      >(20/147)(7-2w^2).                (23)

The second strict inequality uses sqrt(6)<49/20 and
7-2w^2>0. The radical comparison has squared reserve 1/400.
It is enough to prove

    w^2<(147/40)q/R_p-91/100,                            (24)

because inserting (24) into (23) gives q/R_p+C>6/5.

We prove (24) by one displayed polynomial identity and a single
monomial estimate over the whole interval [2/5,3/5]. Define

    A=(735/2)q^3+400p(1+p)(1+p^2),
    B=191+18p+591p^2+400p^4>0.

Direct expansion using R_p^2=1+p^2 gives the exact identity

    100 R_p q^2[(147/40)q/R_p-91/100-w^2]
       =A-R_p B.                                        (25)

All factors outside the brackets on the left are positive.
The tangent bound for the concave function sqrt(1+y), at y=1/4,
and then sqrt(5)>67/30 imply

    R_p<=(9/4+p^2)/sqrt(5)<(135+60p^2)/134.              (26)

Here 5-(67/30)^2=11/900>0. Because B>0, (26) gives

    134(A-R_p B)>134A-(135+60p^2)B=P(p),

    P(p)=23460-96565p+110090p^2+3275p^3
                    -35860p^4-24000p^6.                 (27)

Set z=3/5-p. For 2/5<=p<=3/5 we have 0<=z<=1/5.
The complete shifted polynomial is

    P(3/5-z)=468/5+(77512/25)z-(40643/5)z^2
              +186469z^3-165460z^4+86400z^5-24000z^6.
                                                               (28)

For every j>=1 on this interval, z^j<=z/5^(j-1).
Apply this to each negative higher-power term and discard only the
nonnegative cubic and fifth-power terms. The resulting bound is

    P(3/5-z)
       >=468/5+[77512/25-40643/25-165460/125-24000/3125]z
        =468/5+(717/5)z
        >0.                                               (29)

This estimate includes z=0 and z=1/5. It is a direct
whole-interval bound; no table of coefficients on subintervals or
finite sign-check packet is needed.

Equations (25)--(29) prove (24). Equations (23)--(24) then yield

    q/R_p+C>6/5,
    F=1+q/R_p+C>11/5.

This covers the last endpoint, including both of its limiting values.

## 9. Conclusion and precise replacement scope

Sections 5--8 prove F>11/5 at both endpoints of every closed
interval in Section 3, including the switching and degenerate
values. Concavity from Section 4 gives F>11/5 everywhere on
these intervals. Every original scalar point lies in one of them.
Combining this fact with theta<3/40, a sqrt(u)<1, and the exact
decomposition (5) proves (1).

The proof preserves the original theta and v, both derived from
the same a,b,p. It does not allow an arbitrary application mean or
an unrelated return parameter. Geometric callers still have to
derive the full stated domain from their original equations.

The unchanged export D0>21/10 has exactly the same use as in
the original source. Its old radius reserve was

    21/10-25/12=1/60>0;

the stronger bound here additionally gives

    17/8-25/12=1/24>0.

No caller needs this stronger reserve to remain valid. The theorem
does not alter any retained component, original force, unit count,
degree, mask, endpoint ownership, or full-moment equation. Its
adoption and the retirement of the old 1188-coefficient proof require
the separate original-caller join and independent reviews. Other
three-spoke scalar packets, including the distinct hub-owner return
bounds, are outside this theorem's replacement claim.
