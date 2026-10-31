# Full independent review: both Type III D owners at small radial ratio

Date: October 29, 2026 UTC. Reviewer: roofs continuation.

**Decision: ACCEPT the complete stated theorem at the frozen source
below.** This is a full independent noncontributor review of the current
source, including both original owner charts, the full physical shared
mean, the exact original V2/A3/D3 reduction, the actual-point argument,
all continuous scalar intervals and both literal D02 transfers.

The accepted conclusion is exactly the exclusion of p<=1/2 for each
of the genuine sole-D and physical shared-D Type III owner rows. The
complement p>1/2 is not excluded by this source. Neither whole D02
load family nor the global common-selector obligation is closed here.

## 1. Exact source, independence and full reading

Reviewed source:

    UNIQUE_CIRCLE_TYPE_III_BOTH_D_OWNERS_FULL_MEAN_SMALL_RADIAL_RATIO_EXCLUSION_2026_10_29.md
    SHA256 a4dbb88633fff667457ecab23ac1320c588bdb2fe0ddda46b2d8217ea13812c7

I read that source in its entirety and independently reconstructed
its displayed identities and continuous comparisons. I also read the
two operative sources in full:

| Source | SHA256 | Scope checked |
| --- | --- | --- |
| UNIQUE_CIRCLE_TWO_STRICT_ROOF_PORTS_PERPENDICULAR_INTERFACE_EXCLUSION_AND_COMPLETE_SAME_AXIS_DOMAIN_2026_10_29.md | f8cce87f5bbc22ba898db4029676dd84f1fb1c448212a809ee6809cffc5056eb | Exact genuine and shared D-owner rows, full V2 equations, force/moment identities, original means, Type III domain and literal D02 roles |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual contact applications, complete aggregated shared means, full force/torque balance, physical-mask distinction and strict vertex/vertex construction |

I did not supply the fixed projection, its scalar bounds or any endpoint
calculation used in the reviewed source. My separate roof work supplied
no mathematical step of this small-ratio D-owner argument. This report
is an independent review, not a contributor confirmation. The frozen
source was not edited during the review.

## 2. Original physical entry and the two distinct owner charts

The reviewed source keeps A,D unloaded true3 with stars {V,D,B}
and {V,A,C}, and V loaded true2 with star {A,D}. The actual V has
one physical circle corner Z=(a,b), a,b>1/2, and original roof
applications P1=(a-1,b), P0=(a-1,b-1). A physical two-corner mask
with one zero coefficient does not satisfy this entry.

The actual frames are

    h=(c,-s), e=(s,c),
    nD=(C,S)=K*h+H*e,
    tD=(-S,C)=-H*h+K*e,
    H=c*S+s*C, K=c*C-s*S.

All c,s,C,S are strictly positive. The unchanged interface direction
from A into D is -nD throughout this source. There is no interchange
of the original upper and lower V ports.

For the genuine sole-D row, I checked the input chart directly:

    K<0,
    W=P1-r*e=P0+(s/H)*tD,
    r=S/H, 0<t<1-s/H, H>s, H>S,
    F_B=rho*nD-mu*h,
    Q_B=P1-h+(1-r)*e,
    F_C=-(nu+rho)*nD,
    Q_C=P0-nD+z_D*tD,
    z_D=rho*(s/H)/(nu+rho),
    mu*(1-r)=rho*(H+K)>0.

These are exactly the full original A and D force/torque equations
from the cited input. In particular Q_B is the genuine A vertex
forced by the strict signs of the two components of F_B; Q_C has
the original D-side application fixed by torque. No exterior force
has been deleted to create a smaller star.

For the shared-D row, I separately checked

    K=0, H=1, C=s, S=c,
    r=c, 0<t<1-s,
    W=P1-z*h-c*e=P0+(s+z)*tD,
    0<=z<=1-t-s,
    F_B=rho*nD-mu*h,
    Q_B=P1-h+(1-c)*e,
    F_C=-(nu+rho)*nD,
    Q_C=P0-nD+z_D*tD,
    z_D=rho*(s+z)/(nu+rho),
    rho*(1-z)=mu*(1-c).

Both original closed overlap endpoints are retained. The essential
s+z numerator is present; the genuine sole-D numerator s/H has
not been substituted into this different physical feature. The proof
ultimately needs only B, but it accurately retains the complete C
application and full D torque in its entry.

The genuine angular interval pi/2<alpha+beta<2*pi/3 and beta>pi/4
matches the direct source. Its use below is only to derive the stated
necessary bound on k. The shared row is handled separately at k=0.

## 3. Reconstruction of the common scalar chart

I expanded the unchanged full V equations

    mu*h+nu*nD=kappa*Z,
    mu*det(P1,h)+nu*det(P0,nD)=0.

Because P1=P0+North and det(P0,Z)=a-b, torque gives
mu*c=kappa*(a-b). Combining with the two force coordinates gives

    mu*c=kappa*(a-b)>0,
    nu*C=kappa*b>0,
    nu*(S-C)=mu*s.

Thus a>b and beta>pi/4 follow from the original equations. They
are not a new symmetry assumption.

For genuine k=-K/H>0, or shared k=0, put

    J=sqrt(1+k^2), H=1/J, K=-k/J,
    u=c+k*s=S/H,
    p=(mu/nu)*J-k,
    x=p+1, v=1+k, T=sqrt(x^2+v^2).

The h,e components of the full force equation give Z=(p*Y,Y),
Y=R/sqrt(1+p^2)>0. Independently, substituting
C=(s-k*c)/J and S=(c+k*s)/J into the last torque consequence
gives p=(1+k)*c/s-1. Therefore c=x/T and s=v/T exactly.

The genuine force positivity only gives p>-k; it does not force p
positive. The source correctly retains every negative p. The genuine
angle bound gives k<1/sqrt(3)<3/5. Consequently p>-k>-3/5,
so x>0 in every genuine comparison. In the shared row p=mu/nu>0.

The original relative-side-interior condition r=u<1 gives
k<(1-c)/s=s/(1+c). Squaring only positive quantities in
(x+k*v)^2<x^2+v^2, canceling and dividing by positive v, gives

    (2*p+1)*k+k^2+k^3<1.

Every sign in that derivation is valid. For p>=2/5, the left side
increases in k>=0. Its value at p=2/5,k=9/20 is 8829/8000>1.
Hence actual k<9/20 in that entire subdomain. The same inequalities
used subsequently are valid at the distinct shared endpoint k=0.

## 4. Exact exterior normal and the actual point of B

For the genuine row, expanding the full vector F_B in h,e gives

    F_B=(rho/J)*(-lambda*h+e),
    lambda=mu*J/rho+k.

The full A torque mu*(1-u)=rho*(1-k)/J then gives

    lambda=(1-k)/(1-u)+k=(1-k*u)/(1-u)>1.

The strict inequality uses 0<u<1 and k<1, both already established.
No division by a quantity with an unproved sign occurs.

For the shared row, lambda=mu/rho=(1-z)/(1-c). The full allowed
mean interval gives 1-z>=t+s>s>1-c, so lambda>1 at every mean,
including both overlap endpoints. This is a valid uniform estimate
on the original mean, not a rechoice of that mean.

The actual point lemma is complete. If a unit has minimum support
at Q in an inward unit-normal direction f, express both in its own
orthonormal axes. A positive component of f starts at the lower own
coordinate endpoint and stays in the unit interval after addition;
a negative component starts at the upper endpoint and also stays in
that interval. A zero component preserves the full side coordinate.
Thus Q+f belongs to the same unchanged unit for strict vertices,
owned sides, original side means and both endpoints.

Applying the lemma at the actual Q_B yields

    X_B=(p*Y-c-1-lambda/sqrt(1+lambda^2),
         Y-s+1-u+1/sqrt(1+lambda^2)) in B.

I independently expanded its projection on the fixed unit direction
(-4,3)/5:

    5*P_B=7+c-3*(1+k)*s
       +(4*lambda+3)/sqrt(1+lambda^2)
       +R*(3-4*p)/sqrt(1+p^2).

The normal contribution exceeds four for every lambda>1, because
the positive-side squared difference is 24*lambda-7>0. This is
where the full original force and mean dependence is uniformly bounded;
none of it was removed before the actual-point formula was obtained.

Accordingly the reviewed source's scalar lower bound is correct:

    5*(P_B-R)>F_R(p,k),
    F_R=11+G(p,k)+R*q(p)-5*R,
    G=(x-3*v^2)/sqrt(x^2+v^2),
    q=(3-4*p)/sqrt(1+p^2).

No degree, circle-load, mask or own-frame assumption at B was used.

## 5. Every negative p is covered without a positive-ratio shortcut

For actual p<0, c>0, s<1 and k<3/5 give G>-24/5. Also q>3:
3-4*p is positive, and its square minus 9*(1+p^2) is
-24*p+7*p^2>0. Thus

    F_R>31/5-2*R
       >31/5-2*(1039/500)=511/250>0.

This proof includes every genuine p approaching -k from above.
It does not set mu=0 at that force boundary. The case p=0 is
handled by the next closed interval, so no endpoint is lost.

## 6. Complete scalar monotonicity on both nonnegative intervals

The auxiliary rectangle 0<=p<=1/2, 0<=k<=3/5 is explicitly a
domain for comparison of a scalar formula. Its points are not asserted
to preserve the physical feature, force ratios or original means.
That distinction makes the enlarged corner estimates legitimate.

Direct differentiation gives

    G_p=v^2*(1+3*x)/(x^2+v^2)^(3/2),
    G_k=-v*(x+6*x^2+3*v^2)/(x^2+v^2)^(3/2)<0.

On the whole rectangle, x is in [1,3/2], v>=1 and T>=sqrt(2).
Since x>0, v^2<T^2. Therefore G_p<11/(2*sqrt(2))<4.
The exact comparison 121<128 proves the final strict bound.

The other derivative is

    q'=-(4+3*p)/(1+p^2)^(3/2)<-8/3.

The numerator is at least four, and the denominator is strictly
less than 3/2 even at p=1/2, by 125/64<9/4. Consequently

    (F_R)_p<4-(79/40)*(8/3)=-19/15<0,
    (F_R)_k<0.

These are strict whole-rectangle derivatives, not checks at finitely
many angles. The fixed actual R is retained while differentiating.

For 0<=p<=2/5, actual k<3/5 and these derivatives give

    F_R(p,k)>F_R(2/5,3/5)
      =11-157/(5*sqrt(113))+R*(7/sqrt(29)-5).

The exact positive-side square comparisons give
157/(5*sqrt(113))<3 and 7/sqrt(29)>9/7. Hence

    F_R>8-(26/7)*R>493/1750>0.

Both p=0 and p=2/5 are included. Strictness at the k comparison
holds because the actual upper k endpoint is excluded; alternatively
the final rational reserve is itself strict.

For 2/5<=p<=1/2, the stronger actual bound k<9/20 gives

    F_R(p,k)>F_R(1/2,9/20)
      =11-1923/(20*sqrt(1741))+R*(2/sqrt(5)-5).

The comparisons 1923/(20*sqrt(1741))<7/3 and 2/sqrt(5)>8/9
then give

    F_R>26/3-(37/9)*R>557/4500>0.

Again both closed p endpoints are covered. The overlap at p=2/5
is harmless, and p=1/2 has a strict positive reserve. The separate
physical shared row k=0 is included by the same formula; no genuine
feature is falsely extended to its nongenuine k=0 limit.

## 7. Independent exact arithmetic audit

I recomputed the following values using exact integer and rational
arithmetic, independently of the source's printed results:

| Comparison | Recomputed value |
| --- | --- |
| (1039/500)^2-1105/256 | 6711/4000000 |
| (9/5)*(9/20)+(9/20)^2+(9/20)^3 | 8829/8000 |
| 31/5-2*(1039/500) | 511/250 |
| 128-121 | 7 |
| 9/4-125/64 | 19/64 |
| 4-(79/40)*(8/3) | -19/15 |
| 225*113-157^2 | 776 |
| 49^2-81*29 | 52 |
| 8-(26/7)*(1039/500) | 493/1750 |
| 140^2*1741-5769^2 | 842239 |
| 4*81-64*5 | 4 |
| 26/3-(37/9)*(1039/500) | 557/4500 |

All match the manuscript. The displayed derivative identities,
positive-factor transformations and exact corner substitutions were
reconstructed separately in Sections 3--6 of this report. The rational
checks corroborate those continuous arguments; they are not a numerical
pose search or a replacement for a complete interval proof.

## 8. Containment contradiction and literal D02 transfer

The negative, low nonnegative and upper nonnegative intervals exhaust
all p<=1/2. Their strict positivity yields P_B>R for the actual
point X_B in B. Since (-4,3)/5 is a unit vector and B is contained
in the same D_R, this is a valid direct containment contradiction.

For each literal D02 caller the retained labels are

    A=0, V=1, D=2, C=3, N_original=4, B=5,
    rim A--V--D--C--N_original--B--A, chord AD.

A,D remain unloaded true3; V,B,C remain loaded true2. The actual
N remains unloaded true2 in L135 and loaded true2 in L1345. No
equation at N is used or changed. All three other actual squares
and all original physical circle corners, including zero individual
coefficients, remain present. The local theorem has not assumed a
different boundary mask or smaller degree at B or C.

The exact Type III owned-normal entry continues to require its
separate previously stated compatible-selection domain. This theorem
does not choose a new normal after stress extraction or resolve the
global common-selector obligation. Its genuine and shared conclusions
are distinct physical features; their remaining p>1/2 domains are
explicitly left open by this source.

## 9. Final review decision and verification boundary

The complete source at a4dbb886 is mathematically accepted for its
stated scope. I found no omitted mean endpoint, wrong owner transfer,
force deletion, sign error, missing continuous interval, unsupported
symmetry or literal-degree mismatch. No correction is requested.

This review supplies independent acceptance of both original D-owner
small-ratio exclusions. It gives no additional closure credit to the
complementary ratios, Types I/II, the physical-two roof, a whole D02
load family, the sharp nine-unit theorem, equality classification or
Lean. No source edit, metadata mutation, Lean/Lake build, CI run,
numerical pose search, packing certificate, remote write or merge was
performed.
