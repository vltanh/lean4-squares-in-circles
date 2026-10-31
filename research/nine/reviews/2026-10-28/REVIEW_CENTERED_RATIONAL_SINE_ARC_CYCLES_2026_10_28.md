# Full independent review of the centered rational-sine arc theorem

Date: October 28, 2026 UTC. Reviewer: cycles continuation.

## 1. Exact target and disposition

I read the entire current source

    ALL_UNITS_CENTER_RADIUS_FOUR_FIFTHS_CENTERED_RATIONAL_SINE_ARC.md

at SHA256

    1c6389ca1d16472451b118f5b0c220589d52f9006416f1f6faf4854af63df262

including every center regime, the complete closed angular interval, the high-center denominator identity, both continuous polynomial comparisons and the two corollaries.

**Disposition: PASS, without repair.**

The proved theorem is exactly this: every actual closed unit square contained in D_sqrt(1105/256), with actual center radius at least 4/5, contains in its open interior the entire closed arc of radius 43/40 and halfwidth arcsin(13/40) centered on its own center direction. The center threshold and both arc endpoints are included. There is no containing-radius lower bound and no boundary-contact or stress premise.

The target is self-contained. Its earlier centered36 predecessor is motivation, not an operative dependency; I did not import its review as a substitute for checking this new proof.

## 2. Authorship and independence boundary

Root supplied the mathematical derivation of this wider arc, including its chosen exact lower cosine bound, the cleared polynomial and both positivity intervals.

During separate channel research I requested a stronger centered arc after finding an exact obstruction to an endpoint-only merged-interval claim. That request is discovery context. I did not derive or supply any part of the target's mathematical proof. The audit below is a separate full check of the frozen current bytes.

My separate whole-extra proximity manuscript uses the older reviewed centered36 theorem, not this new strengthening. There is therefore no circular use of the target or a presupposed pocket conclusion in this review.

## 3. Entire actual-coordinate and closed-arc reduction

The source chooses only signs and order of the original own orthonormal axes, giving c=r(C,S) with C>=S>=0 and C^2+S^2=1. This does not move the actual square.

I independently derived the farthest-corner expression

    r^2+r(C+S)+1/2<=1105/256.

The two own-coordinate displacements of an actual arc point are exactly the displayed pair in source equation (2). Changing the sign or order of axes preserves the complete symmetric deviation interval, so no orientation or sign of delta is omitted.

With

    rho=43/40,
    sin(alpha)=13/40,
    cos(alpha)=sqrt(1431)/40,

the constants are correctly

    A=43sqrt(1431)/1600,
    B=559/1600,
    A0=8133/8000.

The strict squared reserve A^2-A0^2=1143/32000000 is positive, and both quantities are positive. The deduction A>A0 is legitimate. Also A0-4/5=1733/8000>0 and 1/2-B=241/1600>0.

The full pointwise bounds

    A<=rho cos(delta)<=rho,
    |rho sin(delta)|<=B

hold for every -alpha<=delta<=alpha, including the closed endpoints. The acute-angle inequality cos(alpha)+sin(alpha)>1 gives A+B>rho and rho-A<B. These inequalities are used with their correct directions in all three center regimes.

The comparison to the older36-degree width is also exact: sqrt(5)<23/10 gives sin(pi/10)<13/40. The squared reserve is29/100. The stated decimal width is descriptive only and plays no role.

## 4. Complete low and middle center ranges

For 4/5<=r<=A, rho cos(delta)-r is nonnegative and at most11/40. Cauchy's inequality applied to each displacement in the actual unit own frame gives a squared upper bound

    (11/40)^2+B^2
       =1/4-133919/2560000<1/4.

This covers r=4/5, r=A and every angle deviation. Both original own-axis endpoints C=1,S=0 and C=S remain.

For A<=r<=A+B, I checked the absolute-value comparison even when r exceeds rho. The distance from r to either endpoint A or rho of the admissible first coordinate interval is at mostB. If r>rho, r-rho<=r-A<=B; if r<=rho, rho-r<=rho-A<B. Therefore the absolute first-coordinate displacement is at mostB over the entire interval.

The squared Cauchy bound2B^2 is strictly below one quarter by7519/1280000. Hence this middle range also includes both center endpoints and every point of the closed arc. There is no gap or equality loss between the ranges.

## 5. Complete high-center reduction and sign prerequisites

If r>=A+B, then r>rho. The two coordinate upper bounds are

    (r-A)C+BS,
    (r-A)S+BC.

Their difference is (C-S)(r-A-B)>=0, so the first controls both. This retains the equality r=A+B and the diagonal own-axis endpoint C=S.

If that larger expression reached one half, division by the strictly positive C would give

    r>=A+(1/2-BS)/C
      >A0+(1/2-BS)/C=r0.

The strict step comes from A>A0. The numerator1/2-BS is positive because B<1/2 and S<=1. Thus r0>0, and the farthest-corner expression is strictly increasing between r0 and the actual r. The contradiction can correctly be reduced to the positivity of its excess at r0. No squaring of an unsigned quantity occurs.

For t=tan(theta/2), the actual full interval is

    0<=t<=sqrt(2)-1<5/12<1.

The exact stronger bound t^2<11/64 follows from sqrt(2)>181/128, whose squared reserve is7/16384. The comparison sqrt(2)<17/12 has reserve1/144. Both are valid at the closed actual endpoint theta=pi/4.

I independently recovered

    r0=(12133-5590t-4133t^2)/(8000(1-t^2)).

Its denominator is strictly positive, including both actual orientation endpoints.

## 6. Full exact polynomial identity and continuous positivity proof

Let

    N=12133-5590t-4133t^2,
    D=1-t^2, U=1+t^2, V=1+2t-t^2.

Multiplication of the displayed farthest-corner excess by64000000 D^2 U gives exactly

    N^2 U+8000 N D V-244250000 D^2 U.

I expanded this independently with integer/rational polynomial arithmetic. Its coefficient list is exactly

    [23689,
     13761060,
     5784411,
     -260256000,
     444920411,
     67614940,
     -260232311].

In particular the constant244250000 correctly equals64000000*(Q-1/2), so no denominator or constant term has been dropped.

The negative t^6 term is bounded using t^2<11/64. The resulting t^4 coefficient is exactly

    444920411-260232311*(11/64)=25612350883/64.

Thus source inequality(12) has the correct direction and is sufficient at t=0 as written. For t>0 it is strict, but the argument does not need that additional strictness.

For

    q(t)=13761060+5784411t-260256000t^2
                       +(25612350883/64)t^3,

the derivative is an upward quadratic. Its signs q'(0)>0 and q'(3/8)<0 imply exactly one derivative root within(0,3/8), with the other root beyond3/8. Therefore q increases and then decreases on this whole interval; its minimum is at an endpoint. I checked both endpoint values, and both are positive.

On[3/8,5/12], q' is convex and negative at both endpoints. It is at most its linear interpolant, hence negative throughout. Thus q(t)>=q(5/12), while t^4>=(3/8)^4. This is a complete continuous comparison, not a numerical orientation check.

All exact values in these steps agree:

| Quantity | Recomputed exact value |
| --- | --- |
| q'(0) | 5784411 |
| q'(3/8) | -84280010703/4096 |
| q'(5/12) | -8176877333/3072 |
| q(3/8) | 14275082289/32768 |
| q(5/12) | -6962533225/110592 |
| q(5/12)+67614940*(3/8)^4 | 140911340555/110592 |

The last reserve is strictly positive. Thus P(t)>=23689>0 on every actual orientation. The cleared prefactor64000000(1-t^2)^2(1+t^2) is positive. This proves the strict excess at r0, contradicts actual containment and excludes either coordinate displacement reaching one half.

Consequently the high-center proof establishes strict interior membership over the entire closed deviation interval, and joins the two previous ranges without any missing endpoint.

## 7. Clearance, separation and exact exported scope

For dist(O,K)=d0>=3/10, the actual nearest point p exists and is nonzero. The supporting direction p/d0 gives n.z>=d0 for every z in K. The actual support halfwidth of a unit square in any unit direction is at least one half. Hence

    |c|>=n.c>=d0+1/2>=4/5.

This checks the full closed clearance threshold. The geometric supporting direction is used only to bound the unchanged square; it is not substituted for a selected stress normal.

For two distinct squares with disjoint open interiors, their two closed centered arcs are disjoint because every arc point is interior to its own square. A minor center gap at most2alpha would make the arcs overlap, including their common endpoint when equality holds. The strict center-separation corollary follows with the correct equality treatment.

No connectedness assertion for the square's whole circle intersection is imported or needed. There is no pocket winding conclusion, extra-unit allocation, transmitter-proximity conclusion or original graph closure in the theorem. A caller must supply those separately. The physical-boundary and proved-clearance remarks in the source are legitimate checks of its geometric center hypothesis only.

## 8. Verification record and conclusion

The complete target was read at the pinned current bytes. Every new regime, direction inequality, denominator, coefficient, derivative sign, comparison endpoint and strict reserve was independently checked. Exact fraction/polynomial arithmetic corroborated the printed identities; it did not replace the continuous proof.

There is no requested source repair. This is a full independent PASS for the exact arbitrary-orientation theorem, its closed center/arc/clearance thresholds and its strict two-unit separation corollary.

No pose enumeration, mesh, optimizer, finite geometric certificate, altered force, actual contact, application mean or corner mask, Lean compilation, CI, remote action or shared-ledger edit was used in this review.

