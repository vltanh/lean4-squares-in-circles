# Independent full review: the uniform far C tangent and common-side radial axis

Date: October 29, 2026 UTC. Reviewer: Type II A-owner continuation.

**Verdict: PASS at the exact whole-scalar and common-side-radial scope
stated below.** I read the entire revised source and all three complete
direct inputs, reconstructed the original-domain joins, checked every
positive branch and complete comparison interval, and independently
regenerated the full degree-23 polynomial identity with exact rational
arithmetic. Every displayed coefficient and numerical reserve agrees.

The reviewer did not contribute to the stronger cap, radical estimates,
polynomial construction, positivity argument, tangent monotonicity or
physical radial-C consequence. I requested one scope clarification in
the initial version; it has been applied in the reviewed revision and
is recorded explicitly in Section10 below.

## 1. Exact source revision and all complete direct inputs

Reviewed current source:

    TYPE_II_FAR_SIDE_UNIFORM_C_TANGENT_BOUND_AND_COMPLETE_RADIAL_C_AXIS_REDUCTION_2026_10_29.md
    SHA256 ed6a592db738a3fa31c87244415efc668180fbff9397b4511052e8fb3e3269c2

The initial version read during this review had SHA256
2bde5cc104203cbb2792d005e9eab5863392b6bdf66b3da94e40887bfd8c3e4a.
Only the overly broad radial-C wording was narrowed; the entire current
source was reread after that correction. This report endorses the
complete current bytes, not just a selected calculation.

All three complete direct inputs were read:

| Complete source | SHA256 | Exact scope checked |
| --- | --- | --- |
| TYPE_II_FAR_SIDE_LINEAR_CAP_AND_STRICT_C_TANGENT_MONOTONIC_REDUCTION_2026_10_29.md | 90950427e5f69369fd9bd6a6295552355b2abf33954aa989cacb094ac98a7ffe | Entire original scalar chart and D mean, e<1/2, linear cap, all comparison branches and strict tangent derivative |
| TYPE_II_FAR_SIDE_COMPLETE_PHYSICAL_RADIAL_ENDPOINT_MASK_ALTERNATIVE_2026_10_29.md | b002cbf7521c44b67c9bac13e048aac9961ea04ab1717f78c312e2eb0c36708c | Actual common-C-side lemma, the whole B-radial or common-side-C-radial alternative, every side mean and physical coefficient endpoint |
| TYPE_II_FAR_RETURN_SIDE_CHANNEL_EXCLUDES_BOTH_PARALLEL_LOADED_ENDPOINTS_2026_10_29.md | e573ec4e567bb3e255ddbc9348b24dd4780651beebd1f3ea713e949930929b68 | Entire original far-side load and force chart, true degrees, original points, full means and closed radius window |

The operative full far-diagonal, loaded two-application, open-side-cone
and closed-side-cone inputs underlying those sources were also available
from complete reads. The current review does not change their accepted
scopes or replace their own independent gates.

## 2. The whole original scalar function and the connecting interval

The unchanged original C application has exactly

    Q_C.d0=R/sqrt(1+z^2)-(1-e)/sqrt(1+e^2)-delta_D,
    delta_D=T*v/(T+u), T=q+e, u=z-e.

The full original ratio gives this exact delta_D; it is not a freely
selected contact mean. The complete old scalar source proves 0<e<1/2,
0<z<1, z>w(e) and u>3/10. I checked its preservation of q>0,
k<a, H,k>0, v<1 and every positive denominator along the entire
comparison interval from w(e) to the original actual slope.

In particular its derivative bound is a statement about this same
explicit original-data function at fixed e,R. Its lower estimate on
the derivative of delta_D uses the exact square (3T-11u)^2, and the
remaining radial derivative gives the strict bound less than -1/7.
No circle cap or physical packing is assumed at a varied comparison
slope. These facts justify the later use of the entire subinterval
starting at W(e), once z>W(e) is established.

The new upper radius 133/64 is valid at the entire original closed
upper endpoint, since its squared reserve is exactly 9/4096>0.

## 3. The stronger cap preserves both comparison endpoints

I independently rederived the curvature margin from the preceding
linear-cap proof:

    Phi''<=-1+64/(49*sqrt(5))<-219/539.

Subtracting (219/1078)e(1/2-e) therefore leaves a strictly concave
function with the same two strictly positive endpoint values. Its
positive chord proves the claimed strict lower bound on Phi, including
the endpoints where the subtracted quadratic vanishes.

For s>=1/2 the exact derivative bound is
(25/12)g'(s)<=10/(3sqrt(5))<50/33. Multiplying by the full increment
W-w=(2/15)e(1/2-e) gives the printed coefficient 20/99. I checked
the positive reserve

    219/1078-20/99=1/882.

Thus the strengthened comparison remains strictly below the actual
physical cap on the entire closed interval. With R<25/12 and strict
monotonicity of g, it yields the actual original inequality z>W.

Since W>=w, every comparison value between W and z_actual lies
in the already verified old interval. The strict tangent derivative
therefore gives exactly the upper comparison in the new equation(8).
No new force ratio, mean, normal, circle center or physical realization
is introduced.

## 4. Both radical range bounds are continuous and exact

At the strengthened W I checked

    P=105((1+e)-(1-e)W)
      =49+94e+81e^2-14e^3,
    K^2=11025(1+e^2)^3-P^2.

The complete expansion agrees with every term in equation(9).
P and the old P_1 are positive on [0,1/2], and
P_1-P=7e(1-e)(1-2e)>=0, giving the correct direction for the
lower radicand comparison.

I recomputed the exact decomposition of the latter polynomial minus
84^2. Both displayed quadratics are positive for all real arguments:
their positive leading coefficients and discriminant reserves are
9,000 and 801,052. Thus K>84 holds strictly, including both outer
comparison endpoints.

For the upper bound, the printed second derivative is exact. The
quadratic used inside it has positive leading coefficient and positive
discriminant reserve 20,861,376. Thus the radicand is strictly convex
throughout the whole interval. Its endpoint values are exactly 8624
and 539069/64, both below 93^2. Convexity gives the entire bound
K<93, not merely an endpoint check on an arbitrary polynomial.

The strict chord identity then gives

    84<K_0=(K^2+7812)/177<K.

This is a lower bound for the same positive radical. Its use does not
assert the existence of any square or force at K_0.

## 5. Every denominator and monotone radical substitution is valid

The two exact squared-difference identities in equation(13) yield the
stated lower bounds r_1<=1/J and r_3<=1/J^3. All their denominator
polynomials and both sides before squaring are positive on e^2 in
[0,1/4]. I checked their algebra directly; no Taylor remainder or
uncontrolled asymptotic approximation is used.

At fixed e,P,J,W, the original mean formula is increasing in K
on its positive branch: both T=A*K/P-B and v=(K+eP)/(105J^3)
increase, u=W-e is fixed positive, and T*v/(T+u) increases in
either positive variable. It is legitimate to use this scalar monotonicity
without maintaining H^2+k^2=1 at an intermediate K: only this explicit
function is compared, and the original physical configuration is kept.

The positive branch at K_0 is checked rather than presumed. I
independently regenerated the full polynomials for 177F and 59E.
The single negative coefficient of F is dominated by the printed
positive constant reserve throughout e<=1/2; E has entirely positive
coefficients. K_0+eP>0 as well. Thus the lower comparison
delta_D(e,W)>=r_3*N/E has exactly the required sign and domain.

For the remaining radial term, W is increasing and W>=8/15.
Hence t=(225W^2-64)/289>=0. The exact positive squared-difference
identity t^3 proves the stated rational upper bound on 1/sqrt(1+W^2).
Both denominators 4+t and 4+3t are positive. It follows that

    1/2+B/J+delta_D(e,W)>=S,
    U>=(133/64)/sqrt(1+W^2),

with precisely the directions required for the later S>U proof.

## 6. Independent exact regeneration of the entire degree-23 identity

I reconstructed the rational functions from their printed definitions,
using exact polynomial operations over rational numbers:

    W, P, K^2, K_0, F, E, N,
    r_1, r_3, t, S, U,
    D=577728*(5e^2+4)*(e^4+8e^2+8)*V*E_7.

Multiplication and exact polynomial division give zero remainder in
D*(S-U). Its resulting polynomial has degree23, and all24 coefficients
agree exactly with the displayed integer table. This checks the full
identity, including the negative high-degree coefficients, without
evaluating any parameter or packing sample.

I also checked positivity of every factor in D. The only negative
coefficient of V is absorbed by
8763e^2-5628e^3>=5949e^2. E_7 and the other factors are positive
throughout the whole closed interval. Thus the polynomial sign is
equivalent to the rational-function sign as used in the source.

## 7. The entire polynomial positivity argument is valid

For degrees0 through6, each actual coefficient is strictly greater
than 10^15 times the corresponding coefficient of Q, including the
two negative comparisons. All degrees7 through13 are positive.

For the degree14 tail, I checked every term used in the lower bound.
The positive nonconstant terms are dropped only in the safe direction;
the six negative terms are bounded using their whole-interval powers
of1/2. The exact remaining reserve is 57723/512>0. Consequently
P_23>10^15 Q throughout [0,1/2], including e=0 where the strict
low-degree constant reserve still applies.

On [0,1/3], the derivative of Q has exactly one negative nonconstant
term. Dropping it and bounding only the positive terms gives the
printed uniform bound -4750/81<0. The endpoint value is
Q(1/3)=9785/729>0, proving positivity on the entire first interval.

On [1/3,1/2], Q''' is strictly positive; its first two terms already
have positive sum at1/3 and every later term is nonnegative. Hence
Q''>=11980/9>1300 throughout that whole interval. The quadratic
lower support at2/5 is therefore valid on both sides of2/5. Its
exact values are

    Q(2/5)=3312/625>5,
    Q'(2/5)=-32844/625,
    |Q'(2/5)|<53.

Completing the square leaves the positive reserve 10191/2600.
Both intervals contain their joining value. This is a full derivative
and convexity proof of positivity, not a collection of sampled sign
checks. It proves S>U at every comparison parameter.

## 8. Whole actual tangent bound and all original joins

The rational inequalities and positive polynomial give exactly

    (133/64)/sqrt(1+W^2)-B/J-delta_D(e,W)<1/2.

The entire original-data monotonic comparison then proves
Q_C.d0<1/2 for every original far-side parameter, full D mean,
positive force ratio, physical endpoint mask and original radius in
the closed window. No original physical term was enlarged or selected
independently. The proof uses both the actual cap and full V/A/D
identities at precisely their retained original scopes.

## 9. Complete common-side radial-C consequence

The imported actual-side lemma supplies the unchanged common C side,
whose outward axis m lies on the closed arc from n to d_N. In the
radial-C alternative supplied by the full mask cover, C is physically
radial along the inward normal -m of that side, with the entire two-
corner square and all individual circle coefficients retained.

For any nonzero tilt 0<phi<=theta<pi/2, n has strict positive
components in both outward m and tangent r. Its original support
Q_C is therefore the unique inner-side endpoint -h*m+r/2.
Because h=sqrt(R^2-1/4)-1>1/2 throughout the original window,

    Q_C.d0=h*sin(phi)+(1/2)cos(phi)>1/2.

This contradicts the whole actual tangent bound. The argument covers
phi=theta whenever it is positive and introduces no interior premise
for an original side mean. Thus this entire common-side radial-C
alternative forces phi=0 and the exact original -n radial position.

In that aligned position the strict signs of the original d_N select
U=-d0/2-h*n. The full original C torque has the claimed exact sign:

    p_C*(Q_C.d0)
       =gamma*((d_N.n)/2-h*(d_N.d0))>0.

Combining it with the proven upper bound gives 0<Q_C.d0<1/2 and
the displayed equality P.n=2-sqrt(R^2-1/4). Every original D mean
and physical two-corner coefficient is still present.

## 10. The applied scope correction and final adoption boundary

The initial wording said that every physical radial C in the entire
far row was aligned with -n. The operative mask cover guarantees a
radial C along the common-side inward axis when B is not already
radial; its alternative alone does not classify every possible two-
corner C when B is radial. The new scalar theorem needs only that
common-side radial-C feature for its final disjunction.

The author narrowed the introduction and Section8 accordingly and
added an explicit note preserving the B-radial case's unclassified C
masks. The final complete conclusion is exactly

    B physically radial along f,
    OR C physically radial along -n,

with overlap permitted. The entire nonzero tilt of the common-side
radial-C alternative is excluded. Neither remaining radial alternative,
the whole far-side row, Type II, D02, loaded N, the global sharp bound
nor equality classification is declared closed. No further correction
is needed at the final reviewed hash.

This full review used complete source reads, exact rational polynomial
identities, continuous inequalities and the unchanged physical support
geometry. It used no numerical pose search, angle mesh, packing
certificate, sampled feasibility check, new normal or mean, shortened
star, omitted unit, Lean/Lake build, CI, branch write or merge.
