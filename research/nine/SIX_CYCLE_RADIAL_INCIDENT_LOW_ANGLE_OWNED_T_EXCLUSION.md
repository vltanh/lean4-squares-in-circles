# Low incident-radial angle: no owned T interface above a right turn

**Status: complete continuous-domain hand core exclusion and exact coefficient proof; root and separate independent full source, geometry, domain-map and all-coefficient audits passed.**

Use the actual incident-radial component B-W-C-U_C-T-U_B-B. B has its physical two-corner mask; C,T each have one physical circle corner. W is the only diagonal transmitter. The C other-port normal is nonaxis. Write its true normal as (−cosβ,−sinβ) and B's as (cosα,−sinα), with

0<α<π/4, π/4<β<π/2, π/2<α+β≤3π/4. (1)

Retain every original pair force, circle weight and side mean.

**Theorem.** Neither T interface can have a T-owned side-axis normal. Thus every remaining case in (1) uses two strict T vertices, with neither normal owned by T. No completion unit has been discarded; this is an exact core exit for the owned-normal alternatives only.

## 1. The unchanged shared-side normal form

The complete unique T feature cover puts its two applications on one inner side, with at least one a vertex. If T owns one normal, reflect and relabel the diagonal endpoints so the owned interface is the right endpoint C_*. Let the two displayed side-channel angles be θ,ψ, respectively. The left application is the vertex opposite T's unique circle corner. The right application has its original mean on that same side; it may be at the other side endpoint.

Put a=cosθ, b=sinθ, u=cosψ, v=sinψ, C=cos(θ+ψ), S=sin(θ+ψ), and

ell=(√2−a−u)/v, 0<ell≤1. (2)

In the reflected orthonormal frame e=(v,−u), f=(−u,−v), write T's circle corner as (A,B_0). Its actual applications are P=(A−1,B_0−1), Q=(A−1+ell,B_0−1). The two endpoint circle corners are exactly z_L=(A−p,B_0−q), z_R=(A−r,B_0−s), where

p=1+u+v+S, q=1+v−u−C, r=1+u−v−ell, s=2+u+v. (3)

These are the same actual-position identities as C6_SHARED_T_SIDE_ARC_CERTIFICATES.md; their derivation uses no unique mask or radial concurrence at the diagonal endpoints.

Set D=ps−qr. The equal physical circle radii give

A=[s(p²+q²)−q(r²+s²)]/(2D),
B_0=[p(r²+s²)−r(p²+q²)]/(2D). (4)

The true torque equation at UNIQUE T, with the original shared mean, is exactly

F=S[A−(1−ell)B_0]+ell C A=0. (5)

The factor S has not been omitted. All domains below have D>0 and S>0, proved explicitly. The physical upper circle height of the displayed left endpoint is

b_L=−u(A−p)−v(B_0−q). (6)

If that endpoint is the original radial B, then b_L=1/2 as physical geometry, regardless of its original force-weight split.

## 2. T owning the original C normal

Here θ=α, ψ=β. Its common inner side slopes downward from P to Q, so

e_C−1/2+sinα−sinβ=−ell cosβ<0.

The incident endpoint theorem gives e_C>5/4, hence sinα<1/4. Therefore

0<α<2 arctan(2/15), 0<δ:=π/2−β<α. (7)

The upper comparison follows since sin(2 arctan(2/15))=60/229>1/4.

Map the full physical domain into ONE closed rectangle:

t=(2/15)X, w=tY, α=2 arctan t, δ=2 arctan w, 0≤X,Y≤1. (8)

Thus cosα=(1−t²)/(1+t²), sinα=2t/(1+t²), u=sinδ=2w/(1+w²), v=cosδ=(1−w²)/(1+w²).

Set G=b_L−1/2. The exact whole-rectangle certificate below proves F+(3/10)G>0. (9)

But (5) and the original physical radial half-mask give F=G=0. This contradiction excludes the entire owned-C alternative.

For denominator positivity on the entire rectangle: u<1/3, v>2/3, cosα>0, and cosα+u<4/3<√2, so ell>0. Also S=cos(α−δ)>0, C≤0. In (3), p>2, s≥3, 0<q<3, r<1. If r≤0 then D>0 immediately; if r>0 then D>6−3>0. The endpoint ell=1, if physically present, has not been removed.

## 3. T owning the original B normal

Reflect and exchange the endpoints, so now θ=β, ψ=α. The original low-angle B is the displayed right endpoint. Since ell≤1 and θ>π/2−ψ,

√2≤cosθ+cosψ+sinψ<cosψ+2sinψ.

Thus sinψ>1/5; otherwise the right side is at most 7/5<√2. Consequently

1/10<tan(ψ/2)<√2−1, 0<δ:=π/2−θ<ψ. (10)

The lower tangent comparison uses sin(2 arctan(1/10))=20/101<1/5.

Use the ONE rectangle

w=1/10+(√2−1−1/10)X, t=wY, ψ=2 arctan w, δ=2 arctan t, 0≤X,Y≤1. (11)

Here cosθ=sinδ=2t/(1+t²), sinθ=cosδ=(1−t²)/(1+t²), u=cosψ=(1−w²)/(1+w²), v=sinψ=2w/(1+w²).

The certificate proves F≥0 on the rectangle and F>0 at every physical point in (10). This contradicts the original torque (5).

For all poles, v>0, S=cos(ψ−δ)>0, C≤0. Also ell≥0 because cosθ≤sinψ and u+v≤√2. In (3), p>2, s≥3, 0<q<2, r<2. Thus D>0, considering r≤0 and r>0 separately. The physical domain has X<1; the only zero-certificate loci are the two rectangle corners X=1,Y=0 or1, so none is physical.

## 4. Complete exact cleared polynomial definitions

The following definitions apply to both rectangles, with the respective t,w and sine numerators above. Write

D_a=1+t², D_b=1+w²,
a=C_a/D_a, b=S_a/D_a, u=U/D_b, v=V/D_b,
Z=D_a D_b,
S_n=C_a V+S_a U,
C_n=C_a U−S_a V,
E_n=√2 Z−C_a D_b−U D_a,
L=ZV,

P=[Z+(U+V)D_a+S_n]V,
Q=[Z+(V−U)D_a−C_n]V,
R=[Z+(U−V)D_a]V−E_n D_b,
T=[2Z+(U+V)D_a]V. (12)

Thus p=P/L, q=Q/L, r=R/L, s=T/L. Put

D_n=PT−QR, H_1=P²+Q², H_2=R²+T²,
A_n=T H_1−Q H_2, B_n=P H_2−R H_1. (13)

Then A=A_n/(2D_n L), B_0=B_n/(2D_n L). Define

F_n=S_n D_a V(A_n−B_n)+S_n E_n B_n+E_n C_n A_n,
G_n=−U A_n−V B_n+2D_n(UP+VQ)−D_n L D_b. (14)

Direct clearing gives

F=F_n/(2D_n L D_a² D_b V),
G=G_n/(2D_n L D_b). (15)

Every denominator is positive by Sections 2–3.

For the owned-C rectangle set

P_C=[F_n+(3/10)D_a² V G_n]/(D_a D_b² V);

for the owned-B rectangle set

P_B=F_n/(D_a D_b² V). (16)

The displayed divisions are exact polynomial identities over Q(√2), checked coefficient by coefficient; the divisors are positive everywhere. Natural bidegrees are respectively (18,10) and (18,8).

## 5. Every coefficient and every endpoint

Use the ordinary exact tensor Bernstein formula on the ONE unit rectangle,

β_{ij}(P;n,m)=Σ_{k≤i,l≤j}[X^kY^l]P · binom(i,k)/binom(n,k) · binom(j,l)/binom(m,l). (17)

The corresponding nonnegative basis sums to one.

For P_C, all 209 coefficients are strictly greater than 1/100. Their exact minimum is

(−186758080223278771192+132177556897286438927√2)/6021527541503906250 >1/100.

Thus P_C>0 on the entire closed rectangle.

For P_B, all 171 coefficients are nonnegative. Exactly two vanish, at (i,j)=(18,0),(18,8). Each of the other 169 coefficients is strictly greater than 1/4. Their exact minimum is

(−34888235658288752413+24881068186017980765√2)/10¹⁸ >1/4.

When X<1, the Bernstein row i=0 already has a positive term at every Y in [0,1], so P_B>0. At X=1 it is positive for 0<Y<1 as well. The only zeros are the two identified boundary corners, neither physical in (10).

The complete exact coefficient JSON and standalone JS generator accompany this manuscript. The generator recomputes (12)–(17) with BigInt rational pairs for Q(√2), verifies both circle identities

P A_n+Q B_n=D_n H_1,
R A_n+T B_n=D_n H_2,

checks every positive-factor division in (16), every coefficient, exact zero set and strict positive floor, and the full inverse Bernstein-to-power identity. Mixed Q(√2) signs are decided by exact integer-square comparison. The generator was executed in memory; no floating sign, sampled-angle box, subdivision, Lean compilation or CI is a premise.

Equations (15)–(17) prove (9) and the strict torque contradiction in Section 3. All original endpoint means, including ell=1 when allowed, were retained throughout.

These exact exits leave the strict-vertex/no-owner T family at turns above 90 degrees and the full lower-turn T family as separate physical domains. They do not themselves assert a completion capacity for those remaining families.
