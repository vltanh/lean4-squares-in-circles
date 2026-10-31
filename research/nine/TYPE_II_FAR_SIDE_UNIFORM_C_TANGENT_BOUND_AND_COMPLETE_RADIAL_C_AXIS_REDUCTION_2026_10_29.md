# A uniform C tangent bound and the complete radial-C axis reduction

Date: October 29, 2026 UTC. Author: root continuation.

**Status: complete proposed whole-domain hand inequality and physical
mask reduction, frozen for separate independent review.** Throughout the
entire remaining original Type II far-return side row,

    Q_C.d0<1/2.

Consequently the entire radial-C alternative supplied by the complete
mask cover is aligned with the original -n axis. Every nonzero tilt in
that common-side radial-C alternative, including its side-normal
endpoint, is excluded at once. The remaining exact alternatives are B
radial along f or C radial along -n, possibly both. Neither whole far
side nor either of those remaining alternatives is excluded here.

The proof uses one continuous stronger cap, rational radical bounds
and an explicit polynomial identity. Positivity of the expanded
polynomial is reduced to a small sextic by coefficient grouping and
two elementary derivative arguments. No parameter samples, angle mesh,
packing feasibility computation or numerical witness enters the proof.

## 1. Whole unchanged original entry

Use the entire original far-side chart, full scalar comparison and
physical-mask cover from the complete sources pinned in Section9.
All nine actual unit squares, the unchanged circle origin and radius,
their disjoint open interiors, every original positive force, complete
true star, selected normal, actual application or full shared mean,
physical circle corner and individual zero coefficient remain.

The literal core is A--V--D--C--N--B--A with chord AD. A,D are
unloaded true3; V,B,C are loaded true2; N is the original unloaded
true2 side transmitter of D02.L135. The earlier complete diagonal,
parallel-endpoint and coincident-C exits retain their full scopes.
Every original V/A/D moment and all unused endpoint equations remain.
The same original conditional common-selection premise is retained.

Write the scalar abbreviations

    e=ell, J=sqrt(1+e^2), A=1+e, B=1-e,
    d=B/J, L=A/J,
    0<e<1/2, H^2+k^2=1, H,k>0,
    q=A*k/H-1>0, v=k+eH<1,
    z=Z.n/Z.d0=(L-H*J^2)/d,
    T=q+e, u=z-e,
    delta_D=T*v/(T+u).

The original C tangent is exactly

    Q_C.d0=R/sqrt(1+z^2)-B/J-delta_D.             (1)

The complete preceding scalar source proves

    w(e)=8/15+(4/7)e,
    z>w(e),
    d/dz [R/sqrt(1+z^2)-B/J-delta_D]<-1/7        (2)

on the entire comparison interval w(e)<=z<=z_actual, at each fixed
actual e,R. It verifies every branch and positive denominator on that
interval, including q>0, u>3/10, v<1 and the original side inequality
k<1/sqrt(1+q^2). It makes no physical realization claim for comparison
points. Those verified hypotheses are used at their exact scope below.

The original radius has the sharper rational upper bound

    R<=sqrt(1105)/16<133/64,
    (133/64)^2-1105/256=9/4096>0.                 (3)

## 2. One stronger cap, from the same entire interval

Define on 0<=e<=1/2

    W(e)=w(e)+(2/15)e(1/2-e)
        =8/15+(67/105)e-(2/15)e^2.               (4)

The preceding scalar proof used

    Phi(e)=L-1/60-(25/12)g(w(e)),
    g(s)=s/sqrt(1+s^2),

and proved positive endpoint values Phi(0)=1/340 and
Phi(1/2)>29/27100. Its exact second derivative obeys the stronger
estimate

    Phi''<=-1+64/(49*sqrt(5))<-219/539,          (5)

using sqrt(5)>11/5. Subtracting (219/1078)e(1/2-e) leaves a
strictly concave function with the same positive endpoints. Therefore

    Phi(e)>(219/1078)e(1/2-e)                    (6)

throughout the closed interval, with strict positivity at the endpoints
supplied by their same original values.

For s>=1/2,

    (25/12)g'(s)<=10/(3*sqrt(5))<50/33.

Since W>=w>=8/15>1/2, the mean-value inequality and (4) give

    (25/12)(g(W)-g(w))
       <=(20/99)e(1/2-e).

The exact coefficient reserve is

    219/1078-20/99=1/882>0.

Combining this with (6) and the unchanged positive endpoint chord
proves

    L-1/60>(25/12)g(W)

on the whole closed interval. The actual physical cap is
R*g(z)>L-1/60, and R<25/12. Strict monotonicity of g therefore
gives the stronger original-domain bound

    z>W(e).                                      (7)

Because W>=w, the full connecting interval [W,z_actual] is already
contained in the verified interval of (2). No new branch assertion or
packing realization is needed. Equations (1)--(3),(7) imply

    Q_C.d0
      < (133/64)/sqrt(1+W^2)-B/J-delta_D(e,W).   (8)

The remaining proof bounds this explicit comparison uniformly on the
larger closed interval 0<=e<=1/2. The equality endpoints are arithmetic
comparison values, not additional original configurations.

## 3. Exact radical variables at W and their whole-interval range

Put

    P=49+94e+81e^2-14e^3,
    K=sqrt(11025J^6-P^2),
    H=P/(105J^3), k=K/(105J^3).

Here P=105(A-BW)>0 on [0,1/2]. The exact radicand is

    K^2=8624-9212e+16301e^2-13856e^3
             +29146e^4+2268e^5+10829e^6.       (9)

We prove the simple strict range

    84<K<93.                                    (10)

For the lower bound let P_1=49+101e+60e^2, the corresponding
linear-cap numerator. Since

    P_1-P=7e(1-e)(1-2e)>=0,

and both are positive, K^2>=11025J^6-P_1^2. The latter polynomial
minus84^2 has the exact decomposition

    11025e^6
    +e^2*(29475e^2-12120e+1246)
    +(15748e^2-9898e+1568).                      (11)

Both displayed quadratics are strictly positive for every real e.
Their positive leading coefficients and negative discriminants are
verified by the exact reserves

    4*29475*1246-12120^2=9000>0,
    4*15748*1568-9898^2=801052>0.

Thus K^2>84^2, including both comparison endpoints.

For the upper bound differentiate (9) twice:

    (K^2)''=2*(162435e^4+22680e^3
                         +174876e^2-41568e+16301).

The quadratic 174876e^2-41568e+2500 is positive for all real e,
since 4*174876*2500-41568^2=20861376>0. Hence (K^2)''>0
throughout [0,1/2]. A convex function is bounded above by the maximum
of its endpoint values there. Those exact values are

    K^2(0)=8624<8649=93^2,
    K^2(1/2)=539069/64<93^2,
    93^2-539069/64=14467/64>0.

This proves (10) by a single continuous range argument.

The chord identity (K-84)(K-93)<0 now gives

    K>K_0:=(K^2+7812)/177>84.                    (12)

K_0 is one explicit polynomial in e. It is a scalar bound on the
same radical, not a new square position or selected force ratio.

## 4. Rational lower bounds for both subtracted terms

First put x=e^2 in [0,1/4]. Positive squaring of the identities

    (1+x+x^2/8)^2-(1+x)(1+x/2)^2=x^4/64,

    (1+5x/4)^2-(1-x/4)^2(1+x)^3
       =x^3*(5+5x-x^2)/16

proves

    1/J>=r_1:=4(2+e^2)/(8+8e^2+e^4),
    1/J^3>=r_3:=(4-e^2)/(4+5e^2).               (13)

Every square root and denominator used here is positive. The right
side of the second squared difference is nonnegative throughout the
whole comparison interval. No truncated asymptotic estimate is used.

At W the exact original mean is

    delta_D(e,W)
      =[(A*K-B*P)(K+eP)]
        /[J^3*(105*A*K+(105W-105)P)].            (14)

For fixed e,P,J,W, this expression is increasing with K on its
positive branch. Indeed T=A*K/P-B and v=(K+eP)/(105J^3)
both increase strictly, u=W-e>0 is fixed, and T*v/(T+u)
increases in either positive variable T or v.

That branch remains positive at K_0. For a direct check, define

    F=A*K_0-B*P,
    E=105*A*K_0+(105W-105)P.

Their exact polynomial expressions are

    177F=7763-741e+9390e^2+19260e^3+12812e^4
                         +31414e^5+13097e^6+10829e^7,

    59E=433601+174783e+345052e^2+368598e^3+412902e^4
                         +1111054e^5+458395e^6+379015e^7.

All coefficients of E are positive. For F, its only negative term
is absorbed by 7763-741e>=14785/2>0. Also K_0+eP>0.
Thus (12)--(14) give the valid entire-interval lower comparison

    delta_D(e,W)>=r_3*N/E,
    N=F*(K_0+eP).                               (15)

In particular every multiplication by a denominator and every monotone
radical substitution in (15) has its positive branch verified.

## 5. A rational upper bound for the remaining radial term

The stronger cap W is increasing on [0,1/2], since
W'=67/105-(4/15)e>0. Therefore W>=8/15. Define

    t=(225W^2-64)/289>=0.

The exact 8-15-17 identity gives

    1/sqrt(1+W^2)=(15/17)/sqrt(1+t).

For every t>=0, the positive squared difference

    (4+t)^2(1+t)-(4+3t)^2=t^3>=0

proves

    1/sqrt(1+W^2)
        <=(15/17)*(4+t)/(4+3t).                 (16)

This estimate is exact at e=0 and is valid on the whole interval
without selecting any further comparison point.

Set the following entirely rational function:

    S=1/2+B*r_1+r_3*N/E,
    U=(133/64)*(15/17)*(4+t)/(4+3t).

It suffices to prove S-U>0. Equations (13),(15),(16) then give

    1/2+B/J+delta_D(e,W)
       >=S>U>=(133/64)/sqrt(1+W^2).             (17)

## 6. One exact polynomial identity and a simple positive lower bound

Define two explicitly positive polynomials

    V=56644+22512e+8763e^2-5628e^3+588e^4,
    E_7=433601+174783e+345052e^2+368598e^3+412902e^4
                         +1111054e^5+458395e^6+379015e^7.

E_7 has positive coefficients. For V, use
8763e^2-5628e^3>=5949e^2 on [0,1/2]. Thus the denominator

    D=577728*(5e^2+4)*(e^4+8e^2+8)*V*E_7

is strictly positive. Substitution of the explicit formulas in
Sections3--5 and multiplication give the exact identity

    D*(S-U)=P_23(e)=sum_{i=0}^{23} c_i*e^i,      (18)

with these integer coefficients. The identity can be checked solely
by polynomial multiplication; the table contains no sampled value.

| i | c_i | i | c_i |
| --- | --- | --- | --- |
| 0 | 100133775467544448 | 12 | 1295588626585632410 |
| 1 | -287008044436081024 | 13 | 1293030065352094410 |
| 2 | 99401880785174464 | 14 | 171092113568789345 |
| 3 | -357249180649380544 | 15 | 23752838382338297 |
| 4 | 461092316650579912 | 16 | -165723454398030816 |
| 5 | 1034340552883931544 | 17 | -108925070986454284 |
| 6 | 1265369684932574592 | 18 | -41379499821646784 |
| 7 | 2576927830257173264 | 19 | -15327917854503296 |
| 8 | 1563161303489641891 | 20 | 1659974811733056 |
| 9 | 3256447306601442625 | 21 | -820674431027136 |
| 10 | 1792273633667593716 | 22 | 611612816016384 |
| 11 | 3029661970360040766 | 23 | -75021013826304 |

Here is a short continuous positivity proof which does not require a
table of interval signs or a polynomial root computation. Put

    Q(e)=100-288e+99e^2-358e^3+461e^4+1034e^5+1265e^6.

For i=0,...,6, the displayed c_i is strictly greater than 10^15
times the corresponding coefficient of Q. Every c_i for 7<=i<=13
is positive. For the remaining tail, write

    B_9(e)=sum_{j=0}^{9} c_{14+j}e^j.

Drop its positive nonconstant terms and bound every negative term
using e<=1/2. Direct integer comparisons in the table give

    B_9(e)/10^15
      >171-166/4-109/8-42/16-16/32-1/128-1/512
       =57723/512>0.

Consequently

    P_23(e)>10^15*Q(e)                           (19)

throughout [0,1/2]. The high-degree tail has been eliminated by one
positive reserve; all that remains is the elementary sextic Q.

For 0<=e<=1/3, bound the positive terms of Q' at the upper
endpoint and drop its negative quadratic term:

    Q'(e)<=-288+198/3+1844/27+5170/81+7590/243
           =-4750/81<0.

Thus Q(e)>=Q(1/3)=9785/729>0 on that whole interval.

For 1/3<=e<=1/2,

    Q'''(e)=-2148+11064e+62040e^2+151800e^3>0.

Hence Q''(e)>=Q''(1/3)=11980/9>1300. Apply the resulting
quadratic lower support at the fixed arithmetic center2/5:

    Q(e)>=Q(2/5)+Q'(2/5)(e-2/5)+650(e-2/5)^2.

The exact center values are

    Q(2/5)=3312/625>5,
    Q'(2/5)=-32844/625, |Q'(2/5)|<53.

Completing the square therefore gives, on the entire second interval,

    Q(e)>5-53^2/2600=10191/2600>0.

Both closed intervals include their join1/3. This is a derivative
proof of one whole scalar inequality, not an orientation partition or
sampled pose test. Equations (18),(19) prove S-U>0 everywhere on
the original closed comparison interval.

## 7. The whole original tangent inequality

Equation (17) proves

    (133/64)/sqrt(1+W^2)-B/J-delta_D(e,W)<1/2

for all 0<=e<=1/2. Combining it with the complete actual-data
comparison (8) yields the promised strict result

    Q_C.d0<1/2                                   (20)

throughout the entire remaining original far-side domain. All full
original moments, means and physical masks were retained in reaching
the exact function (1). The polynomial argument bounds that same
function; it asserts no comparison packing and changes no force.

## 8. The entire common-side radial-C alternative is aligned with n

The complete far-side support lemma gives one actual common C side
with outward own normal and tangent

    m=-sin(phi)d0+cos(phi)n,
    r=cos(phi)d0+sin(phi)n,
    0<=phi<=theta<pi/2,

where theta is the actual angle from n to d_N. If C is physically
radial along the inward normal of that side, its entire actual position
is

    C=[-A_R,1-A_R]m+[-1/2,1/2]r,
    A_R=sqrt(R^2-1/4), h=A_R-1>1/2.

If phi>0, the unchanged maximum-n support is the unique actual
inner-side endpoint

    Q_C=-h*m+r/2.

Its tangent projection is

    Q_C.d0=h*sin(phi)+(1/2)cos(phi)
       >(1/2)(sin(phi)+cos(phi))>1/2,

because 0<phi<pi/2 and h>1/2 throughout the original radius
window. This contradicts (20), including phi=theta when that value
is positive. Therefore this entire common-side radial-C feature forces

    phi=0,
    C=[-A_R,1-A_R]n+[-1/2,1/2]d0.               (21)

No interior condition at the original C port was used before this
conclusion. In this exact boundary position,

    Q_C.n=1-A_R, P.n=2-A_R,
    U=-d0/2-h*n.

The last point is the actual strict maximum-d_N vertex, since the
already proved strict cone gives d_N.d0<0 and d_N.n>0. The full
C2 moment equation, with original magnitudes p_C,gamma>0, then gives

    p_C*(Q_C.d0)
       =gamma*((d_N.n)/2-h*(d_N.d0))>0.

Thus (20) further gives 0<Q_C.d0<1/2, with the original full
mean retained. The earlier far physical-mask alternative and (21)
now leave exactly

    B physically radial along f,
    OR C physically radial along -n,

possibly both. The complete nonzero tilt feature of this common-side
radial-C alternative is excluded. When B is already radial, the mask
cover alone does not classify every possible physical two-corner C;
no such additional classification is asserted by this argument.
The aligned C feature and the B radial feature remain, subject to all
their untouched original force, moment, side, circle and completion
constraints. Neither whole far-side row, Type II, D02, loaded-N case,
global sharp bound nor equality classification is closed here.

## 9. Complete sources, provenance and independent-review boundary

| Complete source | SHA256 | Exact use |
| --- | --- | --- |
| TYPE_II_FAR_SIDE_LINEAR_CAP_AND_STRICT_C_TANGENT_MONOTONIC_REDUCTION_2026_10_29.md | 90950427e5f69369fd9bd6a6295552355b2abf33954aa989cacb094ac98a7ffe | Entire original scalar entry, exact tangent and D mean, linear-cap endpoint values, full comparison interval and strict derivative |
| TYPE_II_FAR_SIDE_COMPLETE_PHYSICAL_RADIAL_ENDPOINT_MASK_ALTERNATIVE_2026_10_29.md | b002cbf7521c44b67c9bac13e048aac9961ea04ab1717f78c312e2eb0c36708c | Entire actual common-C-side lemma and exhaustive far physical-mask cover, including original side ties and zero weights |
| TYPE_II_FAR_RETURN_SIDE_CHANNEL_EXCLUDES_BOTH_PARALLEL_LOADED_ENDPOINTS_2026_10_29.md | e573ec4e567bb3e255ddbc9348b24dd4780651beebd1f3ea713e949930929b68 | Complete original far-side force, moment, point, radius and full-mean conventions |

All three complete direct sources were read. Root contributed to the
earlier linear cap and far-side cap construction, as their independent
gates record. Far-vertex suggested the stronger quadratic cap (4) and
the initial radical-chord approach. Root supplied the sharpened radical
range, rational lower and upper bounds, exact identity and complete
continuous positivity argument, and the full strict tangent join. The
radial-C consequence was reconstructed from the unchanged actual side.
These contributions require a separate noncontributor full current-source
review before adoption of this new result.

Exact rational polynomial arithmetic was used to expand and verify
(9),(11),(13),(18) and the displayed reserves. Every positivity argument
is printed above as an elementary inequality on the whole stated
interval. No numerical approximation, sampled parameter, orientation
mesh, polynomial-root search, packing certificate, new normal or mean,
shortened positive star, changed physical mask, omitted square,
Lean/Lake invocation, CI/workflow dispatch or merge was used.
