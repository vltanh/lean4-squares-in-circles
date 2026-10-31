# Root reconstruction: the entire Type II perpendicular-owner unloaded bridge proof

Date: October 29, 2026 UTC. Reviewer: root continuation.

**Decision: the complete current proof reconstructs correctly.** The
frozen source is

    TYPE_II_PERPENDICULAR_HUB_OWNER_WHOLE_UNLOADED_BRIDGE_EXCLUSION_BY_CONTINUOUS_OBLIQUE_GAP_2026_10_29.md
    SHA256 1de9fe2c3ab7d71d13c9dc96a8a036d05200e9e0447704bbae641e974a0dd03a.

I read all 548 lines, independently reconstructed both full continuous
projection cases, both scalar monotonicity reductions, the complete
quartic bound and the exact degree-six positivity identities. The
eight direct pins, six polynomial identities, fourteen positive basis
coefficients and eight rational reserves were recomputed exactly.

Root had earlier suggested recording the full original coupling
tK(1-omega)=p*s*(S-C) and exploring a different cone-determinant
comparison. The new side proof does not use that suggested comparison
or require the coupling beyond its retained original setting. To keep
provenance conservative, this report is a full reconstruction with those
earlier suggestions disclosed; the separate capacity current-source
review is the independent adoption gate.

## 1. Full actual domain and both exact support projections

The accepted complete Type II entry retains A,D unloaded true3,
V loaded true2 with one physical circle corner, all original V/A/D
equations, and the derived original A-side mean z=sH/C in(0,1).
The actual angular domain has0<alpha<pi/4<beta<theta<pi/2,
theta=alpha+beta, H=sin(theta),K=cos(theta).

In the actual frame(-tD,nD),

    p=1-H+omega*S, t=1+K-omega*C, p,t in(0,1),
    q=t/p, r=1-z,
    Delta=(-E,V0), E=1+H+rK, V0=p-K+rH,
    b=(-H,-K), f_C=(t,-p)/sqrt(p^2+t^2).

These are the unchanged supports and original exterior force directions.
The complete D moment gives q=rho/nu. No independent ratio is selected.

Define J0=H-Kz,D0=K+Hz. Since z<H(H-K),
completing K^2-KH shows J0>H(1-H^2/4)>=3H/4>1/2.
The entire horizontal unit-support gap is therefore

    1+J0-1/sqrt(1+q^2)>1

for every q>=2, including equality at the joining ratio.

For q<=2 the single unit direction(-4,1)/sqrt(17) has the
correct strict support signs. Its exact sine tails are H+4K and
(4p-t)/sqrt(p^2+t^2), after scaling by sqrt(17). Direct
subtraction gives the whole-unit gap at least P/sqrt(17), where

    P=4+4J0+p-D0+(q-4)/sqrt(1+q^2).

I checked these formulas from the original supports, with the full z
retained. The remaining task is the uniform strict P>25/6>sqrt(17).

## 2. Full slider monotonicity, with every ratio interval covered

At fixed actual angles, increase only the scalar omega to1.
The entire comparison preserves0<p,t<1, with p increasing,
t decreasing and q decreasing. This is an enlarged scalar comparison;
it does not purport to preserve the force-coupled packing.

Writing k=C/S, the exact P derivative is negative precisely when

    (k+q)(1+4q)>p(1+q^2)^(3/2).

For0<q<1/2, the original t>1-C and p<1 give q>2/7.
Also t=q*p<1/2 forces C>1/2 and k>1/2. Thus the left side
exceeds165/98>3/2 while the right side is below(5/4)^(3/2)<3/2.

For1/2<=q<=1, positive squaring reduces the required stronger
comparison to

    R(q)=-1-2q^2+8q^3+13q^4-q^6.

Here R(1/2)=19/64 and R'(q)>=15q>0 throughout the full
interval. For q>=1, p=t/q<1/q makes the right side less
than3q^2, while the left side exceeds4q^2. These three complete
intervals cover the entire original-to-one comparison path, including
both joins and q=2. Therefore actual P is strictly above its omega=1
scalar value.

## 3. Full angle monotonicity after the slider comparison

Hold the actual theta fixed and compare beta down to pi/4. On the
entire interval pi/4<=beta<theta<pi/2,

    p=1-H+S, t=1+K-C,
    z=H(H-K*S/C), z'=-HK/C^2<0.

Hence J0 increases, D0 decreases and p increases as beta increases.
The exact q derivative has positive numerator

    S*p-C*t=1+S-C-cos(theta-beta)>0.

Moreover p-t=C+S-H-K>0 throughout, because cosine plus sine
strictly decreases above pi/4. Thus0<q<1 and the oblique tail
keeps its sign. Each term of P increases with beta. Actual P is
therefore strictly above P at the single scalar boundary
omega=1,beta=pi/4. No actual angle, normal or mean is altered.

## 4. Complete one-variable and quartic bounds

With sigma=1/sqrt(2),x=H-K,y=H+K=sqrt(2-x^2), the exact
comparison coordinates are

    J0=(y+x^3)/2, D0=y(1+x^2)/2,
    p0=1+sigma-(y+x)/2, t0=1-sigma+(y-x)/2.

Their ratio is strictly between sqrt(2)-1 and1 in the actual
open domain. The full closed comparison lies in[2/5,1].

I expanded the positive-square comparison for

    (q-4)/sqrt(1+q^2)>2q-25/6.

Its polynomial is144q^4-600q^3+733q^2-312q+49. At
h=q-1/2 it is41/4+43h+49h^2-312h^3+144h^4.
For h in[-1/10,0], the lower bound is119/20>0. For
h in[0,1/2], it is bounded below by the concave quadratic
41/4+43h-107h^2, whose two endpoint values are41/4 and5.
This proves the entire interval, including every join and outer end.

It now suffices to prove4J0+p0-D0+2q0>13/3.

## 5. Exact rational comparison and whole polynomial positivity

I reconstructed the exact expression

    Hfun=1+sigma+y(1-x^2/2)-x/2+2x^3
         +2(2-2sigma+y-x)/(2+2sigma-y-x).

At fixed x,sigma it increases with y, since both its linear
coefficient and the complete quotient derivative are positive.
The endpoint chord of sqrt(2-x^2), then sqrt(2)>7/5, give

    y>=ybar=7/5-(2/5)x^2.

All intermediate denominators stay positive. With y=ybar, increasing
sigma to17/24 decreases Hfun: its derivative is
1-4(4-2x)/(2+2sigma-ybar-x)^2<0. The denominator is
at most29/12 and the numerator factor is at least8, with
8>(29/12)^2. This verifies the entire comparison, not only its
rational endpoint. The ratio numerator also remains positive.

At the rational comparison the exact identity is

    D(x)[Hfun-13/3]=P6(x),
    D(x)=121/60-x+(2/5)x^2>=61/60>0,

    P6=1197/800-(107/60)x-(361/120)x^2
       +(74/15)x^3-(611/300)x^4+(3/5)x^5+(2/25)x^6.

Root recomputed P6 from A(x)D(x)+2N(x), then independently
expanded both substitutions x=v/2 and x=(1+v)/2 in the printed
nonnegative degree-six basis. All fourteen coefficients agree
exactly and are strictly positive; the smallest is47/9000.
The basis sums to one on the entire closed interval. Thus this is
a complete polynomial identity proof on[0,1], with both half
intervals and every endpoint covered.

Dividing by positive D proves the required Hfun>13/3. The tail
bound then gives P>25/6, and the final squared reserve is13/36.
This completes the whole continuous oblique gap proof.

## 6. Exact original join and honest load boundary

For every original q, one of the two whole-unit projections has
gap greater than one. The applications of an actual unloaded side
N2 are one unit apart, so no side transmission remains. The complete
earlier ae0ecc51 theorem excludes every diagonal N on this identical
row, including all original mean and tangent-tie cases under the
unchanged initial endpoint-owner convention.

The earlier full owner cover removed both strict A returns and all
shared AD cases before obtaining this surviving A-side row. Thus
the join excludes the entire D-owned perpendicular Type II owner
in L135, with the actual rim and chord unchanged. All original
A3,D3,V2,B2,C2,N2 stars and all nine physical units remain.

The gap above one is not a bound above every physical unit width.
Loaded N in L1345 consequently remains open; no unloaded equation
is assigned to it. Other Type II rows and original D02 parents remain.
The global common-selector compatibility remains conditional.

All exact polynomial checks are algebraic identities on full intervals,
not numerical poses or angle sampling. No mean, mask, force, normal,
degree or original flag was changed. No build, CI, packing certificate
or merge was used.
