# Double-shared C6: a universal torque slope and a 49-sign circle comparison

Date: October 25, 2026.

**Status: accepted after independent full source, physical-domain and exact
arithmetic review. See REVIEW_C6_DOUBLE_SHARED_SLOPE_REDUCTION_2026_10_25.md.** This
replaces the 209-coefficient sign proof in Section 5 of
`SIX_CYCLE_DOUBLE_SHARED_CHANNEL_EXCLUSION.md` by an elementary
whole-domain torque bound and one degree-(6,6) polynomial with 49 exact
positive Bernstein coefficients. It uses no angle subdivision and no
new physical assumption. The small remaining circle comparison is
still exact-arithmetic-assisted; it is not claimed to be table-free.

## Current table-free replacement

`SIX_CYCLE_DOUBLE_SHARED_CIRCLE_SLOPE_TABLE_FREE.md` now replaces
Sections 3--4 below with a short positive decomposition, independently
accepted in `REVIEW_C6_DOUBLE_SHARED_TABLE_FREE_2026_10_25.md`.
Section 2 remains the active analytic torque proof. The49-sign packet
is preserved below as an historical alternative; it is no longer a
required dependency. The complete double-shared scalar is table-free.

## 1. The unchanged original physical equations

Retain the complete double-shared-channel setup and original derivation
in Sections 1--4 of `SIX_CYCLE_DOUBLE_SHARED_CHANNEL_EXCLUSION.md`.
In particular the third loaded square has the original side chord

    ell=(1-cos(alpha)-cos(beta))/sin(beta),
    0<ell<sqrt(2)-1,
    pi/4<=alpha,beta<pi/2,
    pi/2<Sigma=alpha+beta<=3pi/4.

Its original unique circle corner in the unchanged (e,f) frame is
z_T=(A,B), with A,B>1/2. Put

    u=cos(beta), v=sin(beta), S=sin(Sigma), C=cos(Sigma),
    p=1+u+v+S,           q=1+v-u-C,
    r=1+u-v-ell,         s=2+u+v,
    Delta=p*s-q*r >=4+sqrt(2)>0.

The unchanged two-circle equations give

    A=[s(p^2+q^2)-q(r^2+s^2)]/(2Delta),
    B=[p(r^2+s^2)-r(p^2+q^2)]/(2Delta).             (1)

The genuine positive degree-two force and origin-torque equations require

    F=S[A-(1-ell)B]+ell*C*A=0.                      (2)

All original forces, original means, their allowed endpoints, full
transmitter intervals, circle masks, and all three additional squares
remain present. In particular ell>0 is the accepted distinctness of
the two actual applications, not an additional generic-position choice.

We prove the two whole-domain inequalities

    (S+ell*C)/(S*(1-ell)) < 15/14 < B/A.             (3)

Since A,S,1-ell are positive, (3) makes F strictly negative and
contradicts (2).

## 2. The torque side of (3) is elementary throughout the whole domain

Put

    sigma=1/sqrt(2),       k=sqrt(2)-1,
    w=S+C.

The original angular interval gives w>=0. For a fixed sum Sigma,
concavity of cosine on [pi/4,pi/2] shows that the minimum of
cos(alpha)+cos(beta) occurs at one of the two endpoint pairs:

    cos(alpha)+cos(beta)
       >=sigma+cos(Sigma-pi/4)=sigma+w/sqrt(2).

The actual ell>0 implies cos(alpha)+cos(beta)<1. Consequently

    0<=w<k,
    ell <=sqrt(2)[1-cos(alpha)-cos(beta)]<=k-w.       (4)

Here sin(beta)>=sigma, and the numerator of ell is positive; hence
the direction of the first comparison is preserved.

Because S-C=sqrt(2-w^2),

    S=[w+sqrt(2-w^2)]/2 >=sigma+(2/5)w.             (5)

For a direct verification, sqrt(2-w^2)>=sqrt(2)-w/5 follows by
squaring positive quantities: the difference of their squares is
(2w/25)(5sqrt(2)-13w)>=0. The latter follows from w<k and
13k<5sqrt(2), itself equivalent to 8sqrt(2)<13.

The left side of (3) is

    1+ell*w/[S(1-ell)].

The extra term increases with ell. By (4)--(5), it is at most

    w(k-w)/[(sigma+(2/5)w)(1-k+w)] < 1/14.          (6)

To prove the strict comparison, its positive-denominator difference is
the quadratic

    (72/5)w^2+[74/5-(139/10)sqrt(2)]w+k.

Its leading coefficient is positive and its discriminant is

    [33153-23452sqrt(2)]/50 < 0,

since 2*23452^2-33153^2=871199>0. The quadratic is therefore strictly
positive for every real w. This proves the first half of (3), including
w=0, without a polynomial sign certificate or an angular partition.

## 3. A simple independent rectangle covers the physical circle comparison

Let chi=3pi/4-Sigma. Then 0<=chi<pi/4 and

    sin(chi)=w/sqrt(2)<1-1/sqrt(2)<120/409.

The last strict comparison follows from
1/sqrt(2)>289/409, whose squared integer reserve is
409^2-2*289^2=239>0. Since

    sin(2atan(3/20))=120/409,

and both angles lie in [0,pi/4], the whole original domain is covered by

    Sigma=3pi/4-2atan((3/20)x),
    beta=pi/4+2atan(k*y),
    0<=x,y<=1.                                    (7)

The physical domain actually has x<1 and beta<pi/2, but the closed
rectangle is used. It may contain additional unphysical pairs of
alpha=Sigma-beta; this only enlarges the polynomial comparison. The
original physical Delta>0 from (1) is retained at the final implication.

## 4. One complete 49-coefficient proof of the second half of (3)

All following polynomials lie in Q(sqrt(2))[x,y]. Define

    a=(3/20)x,       b=k*y,
    Ds=1+a^2,        Dw=1+b^2,
    Sn=(1-a^2+2a)/sqrt(2),
    Cn=(-1+a^2+2a)/sqrt(2),
    U=(1-b^2-2b)/sqrt(2),
    V=(1-b^2+2b)/sqrt(2).

Thus S=Sn/Ds, C=Cn/Ds, u=U/Dw, v=V/Dw. Also put

    En=Ds*Dw-Cn*U-Sn*V-Ds*U,
    base=Ds*Dw*V,
    P=base+Ds*V*(U+V)+V*Dw*Sn,
    Q=base+Ds*V*(V-U)-V*Dw*Cn,
    RR=base+Ds*V*(U-V)-Dw*En,
    SS=2base+Ds*V*(U+V),
    T=P^2+Q^2,       Z=RR^2+SS^2,
    An=SS*T-Q*Z,     Bn=P*Z-RR*T.

These definitions give the exact substitutions

    ell=En/(Ds*V),
    p=P/base, q=Q/base, r=RR/base, s=SS/base.

The numerator 14Bn-15An is exactly divisible by Dw^2*V. Define the
quotient G by the complete polynomial identity

    Dw^2*V*G=14Bn-15An.                            (8)

After the original two-circle equations (1), its global normalization is

    G=2Delta*Ds^3*Dw*V^2*(14B-15A).                (9)

Every multiplier is positive on the actual domain: Delta>0, Ds>0,
Dw>0, and V=Dw*sin(beta)>0. The exact polynomial G has degree (6,6).

For its complete tensor Bernstein expansion on [0,1]^2,

    G=sum_(i,j=0)^6 b_ij*binom(6,i)*binom(6,j)
                     x^i(1-x)^(6-i)y^j(1-y)^(6-j),

**all 49 coefficients b_ij are strictly greater than 7.** The companion
`SIX_CYCLE_DOUBLE_SHARED_SLOPE_CHECK.py` reconstructs all defining
polynomials in exact Q(sqrt(2)) arithmetic, the complete division
identity (8), all 49 coefficients, every strict comparison, and the
entire inverse Bernstein expansion. No stored sign list is an input.
Optional `--json PATH` writes all ordinary and Bernstein coefficients.

The nonnegative Bernstein basis sums to one on the entire closed
rectangle. Hence G>7>0 there. By (9), 14B-15A>0 at every original
physical point. Since A>0, this is precisely the second half of (3).

## 5. Complete physical join and the remaining certificate

The torque-slope argument and circle-slope certificate prove F<0
throughout the entire original double-shared-channel family. The
reflection already used in the original source covers either choice
of the third loaded square's shared interface. No actual mean, channel
position, positive force, circle corner, boundary case, or completion
square is changed.

The accepted theorem's original Sections 1--4 are retained; this source
replaces only its last 209-sign torque certificate. The new residual
certificate has 49 signs, 160 fewer (about 76.6%), with one polynomial
on one rectangle. The analytic torque inequality covers its whole
domain at once. A completely table-free circle-slope proof remains
desirable and is not claimed here.

Together with `SIX_CYCLE_THREE_SHARED_MATCHING_TABLE_FREE.md`, this
reduces the two former C6 certificates from 209+45=254 signs to 49.
It does not settle the remaining one-/two-share completion families,
the strictly obtuse one-radial family, or any original equality packing.
No new gate or geometric closure count is introduced by the replacement.

