# Uniform positive hub and normalization bounds for the entire A-only side feature

Date: 2026-10-30. Input: PR #11 `71d385e75adc1f5183d35a92dbe18c208dc32f2a`.

**Status: complete new exact necessary bounds, not a whole-feature exclusion.**
The physical roof circle corner and the original hub moment give

    u > 1/12,
    s-c > 1/625,
    a=tan(alpha/2) > 41487/100000.

Consequently the bounded force normalization in the three-variable reduction
has denominators uniformly separated from zero:

    nu > 1/1875,
    |Fv| > 1/2250,
    |Bn| > 1/625,
    |Cn| > 5/18.

These bounds hold over the entire surviving original A-only side feature,
including its radial endpoint alternatives. In the both-unique endpoint
alternative one also has sigma>1/sqrt(2)>7/10. They justify exact interval
contraction and remove the alpha=pi/4 normalization boundary; they do not
require beta to stay away from pi/4.

The `u>1/12` comparison was suggested by the D02 interval contributor; its
complete scalar proof is given below. The strict original-angle gap and the
explicit denominator bounds are derived here from that comparison.

## 1. Exact original entry and previously established whole-feature bounds

Keep all nine actual squares and the original six positive stars

    A:{V,D,B}, D:{A,V,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C}.

A,D are unloaded true3, N is unloaded true2, and V is loaded true2 with its
unique actual physical circle corner. The true endpoint loads, owners,
complete side means and physical masks are unchanged. This source does not
apply the unloaded-N equations to D02.L1345.

Use the literal A-only scalar chart and common positive force scale from
[D02_A_ONLY_BOTH_UNIQUE_THREE_VARIABLE_REDUCTION_2026_10_30.md](D02_A_ONLY_BOTH_UNIQUE_THREE_VARIABLE_REDUCTION_2026_10_30.md):

    c=cos(alpha), s=sin(alpha), C=cos(beta), S=sin(beta),
    H=sin(alpha+beta), k=-cos(alpha+beta), p=H-k,
    delta=s-c>0,
    0<u,t,omega<1,
    u=1-omega*S/H, t=1-omega*s/H,
    mu=u*t, nu=delta*p,
    M=mu/nu>0,
    M*(1-omega)=S-C,
    Fv=mu*East+nu*nD,
    |Fv|^2=mu^2+nu^2+2*mu*nu*C.

The full high-angle side exclusion
[TYPE_II_A_ONLY_ENTIRE_HIGH_ANGLE_SIDE_EXCLUSION_BY_ORIGINAL_SUPPORT_WIDTH_2026_10_29.md](TYPE_II_A_ONLY_ENTIRE_HIGH_ANGLE_SIDE_EXCLUSION_BY_ORIGINAL_SUPPORT_WIDTH_2026_10_29.md)
already gives, for all endpoint physical masks,

    pi/4<alpha,beta<5*pi/12,
    pi/2<alpha+beta<2*pi/3,
    0<k<1/2, H>sqrt(3)/2,
    p>(sqrt(3)-1)/2>1/3.

The full hub-moment bound
[FULL_A_ONLY_HUB_MOMENTS_FORCE_STRICT_CONTACT_SUM_BOUND_2026_10_29.md](FULL_A_ONLY_HUB_MOMENTS_FORCE_STRICT_CONTACT_SUM_BOUND_2026_10_29.md)
also supplies

    omega>H/(s+S),
    u<s/(s+S), t<S/(s+S), u+t<1,
    u,t<2-sqrt(2)<3/5.

These are complete existing inputs, not newly counted original gates.

## 2. The actual roof corner bounds the force ratio

Write Q=1105/256. The original physical roof corner is Z=R*Fv/|Fv|.
Its North coordinate exceeds 1/2. At R^2<=Q this gives the necessary bound

    |Fv|^2 <= 4*Q*(nu*S)^2.

Divide only by nu^2>0 and use S^2+C^2=1:

    (M+C)^2+S^2 <= 4*Q*S^2,
    M+C <= sqrt(4*Q-1)*S.

Put K=65/16. The exact squared reserve is

    K^2-(4*Q-1)=61/256>0.

Thus M<K*S-C, and its right-hand side is positive. Since S-C>0, the unchanged
V moment gives

    1-omega=(S-C)/M > (S-C)/(K*S-C),
    omega < (K-1)*S/(K*S-C),
    u > 1-(K-1)*S^2/[H*(K*S-C)].                 (1)

No small hub factor or matrix determinant has been divided by.

## 3. One exact scalar comparison proves u>1/12

Let r=C/S, so 0<r<1 and S=1/sqrt(1+r^2). It suffices to prove

    (K-r)^2*(1+r^2) > 21609/1452.                 (2)

Indeed H>sqrt(3)/2 and K-1=49/16 then imply

    (K-1)/[H*(K-r)*sqrt(1+r^2)] < 11/12,

because the square of 12*(K-1)/[(11*sqrt(3)/2)] is exactly 21609/1452.
Substitution in (1) gives u>1/12.

For 0<=r<=1/2, expand the left side of (2). Since r^3<=r^2/2 and r^4>=0,

    (K-r)^2*(1+r^2)
      >= K^2-2*K*r+(K^2+1-K)*r^2
      >= K^2-K^2/(K^2+1-K)
       =13456625/880896.

The second inequality is completion of the square with positive coefficient
K^2+1-K=3441/256. Its exact reserve above (2) is

    13456625/880896-21609/1452
      =41978153/106588416>0.

For 1/2<=r<=1, differentiate (K-r)*sqrt(1+r^2). The derivative has the sign of

    -1+K*r-2*r^2.

This concave quadratic is positive throughout the interval because its two
endpoint values are 17/32 and 17/16. The function is therefore increasing,
and positive squaring gives

    (K-r)^2*(1+r^2) >= (K-1/2)^2*(5/4)=16245/1024.

The exact reserve above (2) is 121677/123904>0. This proves (2) on its entire
closed comparison interval, with the join r=1/2 retained, and hence

    u>1/12.                                       (3)

## 4. A uniform positive gap from alpha=pi/4

The identity s^2+c^2=1 gives s+c<=sqrt(2), while S>1/sqrt(2). Hence

    s-S < s-1/sqrt(2) <= (s-c)/2=delta/2.

Use the unchanged relation

    t=u-[(s-S)/S]*(1-u).

If s-S<0, then t>u. If s-S>=0, use 0<1-u<1 and S>7/10. Both cases yield

    t>u-(5/7)*delta.                              (4)

Suppose delta<=1/625. By (3),(4),

    t>1/12-1/875=863/10500,
    mu=u*t>863/126000.                            (5)

On the other hand |Fv|>mu because nu,C,mu>0. The roof-corner inequality gives

    mu<2*sqrt(Q)*nu*S < (25/6)*delta.

Here p,S<1 and the exact squared comparison is

    (25/6)^2-4*Q=55/576>0.

The supposition delta<=1/625 therefore gives mu<1/150=840/126000, contradicting
(5) with reserve 23/126000. Consequently

    s-c>1/625.                                    (6)

For the half-angle a=tan(alpha/2),

    s-c=(a^2+2*a-1)/(1+a^2).

This is strictly increasing for 0<a<1, since its derivative has numerator
2*(1+2*a-a^2)>0. At a0=41487/100000 its value is

    18571169/11721171169 < 1/625,

with exact gap 114190544/7325731980625. Thus (6) yields the rational strict entry

    a>41487/100000.                               (7)

## 5. Uniform bounds for every normalization used by the three-variable system

The existing high-angle exclusion gives p>1/3 and H>5/6. Combining with (6),

    nu=delta*p>1/1875,
    Fv.y=mu*s+nu*H>1/2250,
    |Fv|>1/2250.

The unchanged vector definitions give

    Bn.x=u*c+delta>delta>1/625,
    |Bn|>1/625,
    Cn.y=p*H>5/18,
    |Cn|>5/18.

For both physically unique endpoints, the earlier full strict cone has
pi/2<angle(b,cvec)<3*pi/4, so

    sigma=sin(angle(b,cvec))>1/sqrt(2)>7/10.

These conclusions retain the original absolute circle origin, all force and
torque equations, the actual six-square graph, N and every completing square.

## 6. Exact computational use and remaining obligation

An outward interval enclosure for an original solution may safely be intersected
with these necessary closed comparison ranges:

    a in [41487/100000,1],
    u in [1/12,3/5], t in [0,3/5], omega in [0,1],
    H in [5/6,1], p in [1/3,1],
    |Bn| in [1/625,+infinity), |Cn| in [5/18,+infinity),
    |Fv| in [1/2250,+infinity), sigma in [7/10,1].

Strict original inequalities permit these larger closed ranges without excluding
a real original solution. Intersections may tighten enclosures; they are not
assignments of new physical values. The both-unique unit-direction equation also
gives 0<rB,rC<1 and hence the usual safe closed ranges for rB,rC,xB,xC.

The full interval/certificate cover of every original E1=E2=E3 solution by the
physical capacity domains remains necessary. This lemma alone closes neither
the entire both-unique feature nor either original D02 load row. No original
fine or coarse flag changes.
