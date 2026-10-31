# Root review: complete mixed-01 exclusion and exhaustive two-share assembly

Date: October 26, 2026.

**Result: PASS for the full mixed-01 physical orbit and the complete
three-orbit two-share cover.** The root independently read the complete
saved scalar monotonicities, Cauchy/endpoints source, mixed-01 assembly,
and full two-share assembly. The boundary derivative manuscript was
written by the root and independently reviewed in full by the C6
reviewer; that independent review is a required dependency of this
acceptance, not a self-review substitute.

Sources:

- SIX_CYCLE_MIXED_01_CLOSURE_REDUCTION.md, with its earlier root review.
- SIX_CYCLE_MIXED_01_GAP_MONOTONICITIES.md and its two independent reviews.
- SIX_CYCLE_MIXED_01_CAUCHY_AND_ENDPOINTS.md.
- SIX_CYCLE_MIXED_01_BOUNDARY_MONOTONICITY.md and its independent review.
- SIX_CYCLE_MIXED_01_COMPLETE_EXCLUSION.md.
- SIX_CYCLE_TWO_SHARE_COMPLETE_EXCLUSION.md.

The acceptance is for a hand proof with unchanged original physical
scope. It does not claim Lean verification or close the coarse
all-side C6 gate, whose remaining one-share completion still needs a
proof.

## 1. Cauchy covers the entire unbounded third-force range

The two actual force norms involving \(q>0\) are the norms of
\((q+a,s)\) and \((q+pc_2,ps_2)\). Their triangle inequality and
Cauchy with \((w/2,v/2)\), whose norm is exactly \(K=79/40\),
give the displayed lower bound without choosing a value of \(q\).
The nonshared support upper bound is the valid triangle inequality
\[
 \sqrt{p^2+2q^2+2pqh_2}\le p+\sqrt2q.
\]
Its \(q\)-coefficient agrees exactly with the definition of \(w\).
All eliminated terms cancel with the correct signs. Thus the gap
bound applies pointwise to every original positive \(q\).

The strict force bound \(p>1+1/\sqrt2\) and both original closure
projections were independently accepted in the earlier root review.
Their use here does not alter a physical force or application mean.

## 2. All partial-derivative domains are valid

I independently checked the derivatives with respect to both angles
and to \(p\), including the dependence of \(w,v\) on the first
angle and the third angle's dependence on the first two.

For the first-angle derivative, the exact ratio bound reduces to
\[
 1+(5/2-4\sqrt2)A+2\sqrt2A^2>0.
\]
The stated negative discriminant proves this on the whole required
interval; the case of a nonpositive numerator was handled before
division. The auxiliary positive factors are indeed positive.

For the force derivative, the consequence \(c_2>7/15\) is valid:
the endpoint minimum of the two sine sum with each angle at most
\(\pi/4\) gives the stated bound on \(s_2-c_2\). The function
used for \(U_2\) is concave in each of its two arguments separately,
so checking its four rectangle endpoints supplies a lower bound
over that entire enlargement. The exact lower bound \(U_2>13/10\),
together with the force contribution \(>17/10\), proves
\(\partial_pG>0\).

For the second-angle derivative, the original strict inequality
\(h_1>(1+r)s_0-rc_0\) implies \(c_0>3/10\) with the displayed
squared reserve. It gives \(w>11/3\), \(v<3/2\), and
\(ws_2-vc_2>3/2\). The two force ranges meet at \(9/4\) without
a gap. Their exact quadratic and Cauchy estimates prove
\(\partial_{\theta_1}G<0\) over the entire required domain.

The final assembly only needs the force and second-angle
monotonicities. It correctly does not infer a directional tradeoff
inequality from coordinate derivatives.

## 3. Both fixed endpoints were independently reconstructed

Using exact rational arithmetic from the displayed radical bounds,
I independently checked all interval directions, positive
denominators, positive-term lower bounds and negative-term upper
bounds in both endpoint computations. Every displayed squared or
linear reserve agrees exactly. The resulting strict lower values are
\[
 G(P,5/9,4/9)>
             \frac{11451047}{450000000}>\frac1{40},
\]
\[
 G(9/4,r,1-r)>
             \frac{32451}{1000000}>\frac1{40}.
\]
These are fixed radical comparisons. Neither numerical minimization
nor interpolation between evaluated points is used.

## 4. The actual domain reaches the endpoints with the correct direction

For every actual \(a>3/10\), the path increasing \(b\) to \(1-a\)
stays within the individual angle upper bounds, since
\(1-a<7/10<r\). It preserves the lower angle-sum condition.
Its final squared-sine sum is less than one, so the sum of its
arcsines is strictly below \(\pi/2\); hence the third angle stays
within its allowed interval. The same holds along the whole path.

Every boundary point \(3/10\le a\le r,\ b=1-a\) also has
angle sum at least \(\pi/3\), by convexity of arcsine. Thus the
independently reviewed boundary monotonicity is applied on its exact
stated interval, with no hidden extension.

For \(p\ge9/4\), decreasing \(p\), then increasing \(b\), then
increasing \(a\) along the boundary all decrease or preserve \(G\),
ending at the second fixed endpoint. For \(P<p<9/4\), the full
first closure projection gives
\[
 a\le1-\frac1p-b\left(1-\frac{h_1}{p}\right)<\frac59,
\]
since \(h_1\le\sqrt2<P<p\). The comparison now ends at the first
fixed endpoint after decreasing \(p\) to \(P\).
Equality \(p=9/4\) belongs to the first range; no force boundary is
omitted. The strict \(p>P\) input is a proved original implication.

## 5. Original physical conclusion and complete contact-type cover

Restoring the original force scale gives the uniform strict gap
\[
 \frac{79}{40}\sum_iD_i-N>\frac{\mu_0}{40}>0.
\]
The actual virial identity \(N=R\sum_iD_i\) then contradicts
\(R\ge79/40\). Every original actual shared mean, including its
endpoint case, entered the closure reduction before the scalar
relaxations. All six cycle bodies, three additional physical squares,
circle masks, zero circle weights, and original degrees remain.

The separate two-share assembly correctly joins exactly three
symmetry orbits. For constant corner bits, cyclic symmetry places
the two shares at 0 and 1. For canonical mixed bits 110, the
placements are 01 and 02; placement 12 is excluded by the accepted
double-shared-transmitter theorem. The reflection-plus-reversal map
carries actual physical data and complements the bits.

The constant orbit has its reviewed six rational matrix proof.
Mixed 02 is exhaustively split into \(q\ge p\) and \(q<p\), with
equality retained in the former and complete independent review of
the join. Mixed 01 now has the full proof above. The entire
two-share family is therefore excluded over its original scope.

This excludes a whole contact family, not a new artificial gate.
The surviving one-share completion, the strictly obtuse one-radial
family, other coarse cells, the unrestricted bound, equality
classification, and the older prerequisite audit remain separate.
No Lean compilation, CI, or workflow dispatch was performed.
