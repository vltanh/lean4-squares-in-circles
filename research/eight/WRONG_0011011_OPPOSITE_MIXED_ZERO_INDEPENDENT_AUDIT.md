# Independent audit: every opposite-sign mixed zero-quarter case of 0011011

**Result: PASS.**

This review covers
\`proof_integration/WRONG_0011011_OPPOSITE_MIXED_ZERO_HAND_PROOF.md\`
and its 149-comparison arithmetic checker. It is an independent review
of the continuous proof and its complete case cover, followed by an
independent exact reconstruction of its single polynomial.

The exact file hashes and reconstructed coefficients are recorded in
\`wrong_0011011_opposite_mixed_zero_independent_polynomial_audit.json\`.
The independent reconstruction script is
\`audit_wrong_0011011_opposite_mixed_zero_polynomial.py\`.

## 1. Scope and exact role data

I checked the three normalized families directly against the rational
role table:

- \(J\): core \(C_0^+=.00125+1.03981b\), outer \(O_1^-=J(B)\).
- \(P\): core \(C_1^+=.19555+.63132b\), outer \(O_2^-=O_0^+=P(B)\).
- \(L\): core \(C_4^+=.04970+.94831b\), outer \(O_5^-=O_4^+=L(B)\).

The reflection identity sends edge \(i\) to \(1-i\pmod7\), interchanges
the radial order, and preserves the opposite sign pair \((+,-)\).
All 30 coefficients of these six labels match the JSON exactly.

The source core negative-primary axis is impossible throughout
\(|\phi|\le.7\). The target primary axis becomes the separately treated
outer-source primary case under reflected reversal. Both transverse
axes are treated with both angle signs for all three rows. This
restores all \(3\cdot4\cdot2=24\) stated signed kind/axis cases.

This audit accepts the previously established structural sign
restriction and four-axis reduction as the stated upstream hypotheses.
It does not enlarge the result to other quarter classes or to
outer/outer pairs.

## 2. Continuous geometry and monotonicity

I independently rederived the four displayed SAT projections using
own-frame centers \((a,-\sigma b)\). Their signs, the width \(W\), and
the role-reflection identities are consistent.

The primary-axis exclusions are valid for both angle signs. The
successive bounds \(\phi>.45\), \(B>.34\), and \(B>1/2\) when
\(\phi\le.55\) give the six displayed direct cost bounds without
assuming any contact or feasible minimizing state.

The two negative-angle caps follow by maximizing the relevant
projection at the appropriate outer/core diagonal. The derivative
signs make these true whole-domain maxima. Both cap expressions are
strictly decreasing in the angle and yield \(x<.32\) and
\(x<.44152\), respectively.

I rederived the general formulas for \(F',F'',F'''\). The signs for
\(J,P,L\), including monotonicity of \(P'''\) through the slight
analytic extension to outer coordinate .9, are correct. The global
aligned scalar lower bounds follow from the stated concavity or
strong-convexity arguments.

The positive and negative source-transverse bounds, including the
\(P\)-row transverse-sum constants 1.09 and 1.295, follow with the
correct inequality directions. The full-circle norm argument for
the \(J,L\) positive source cases and the direct small-coordinate
\(J\) estimate are valid. The positive target-transverse estimates
also preserve their directions and cover both \(P\) subranges.

## 3. Negative target-transverse contact

Because each outer label strictly increases, lowering the target
coordinate to the exact first feasible value lowers the cost.
The displayed contact coordinate decreases strictly along both
parts of the core boundary. Feasible core coordinates form a terminal
interval; its possible corner endpoints are exactly the side join,
the diagonal, and the first feasible point with outer coordinate
\(B=d\).

The \(J\) side derivative is positive. Its \(B=d\) continuation is
increasing by the displayed completed square. On the corner,
\(J''<0\), \(J'>0\), and \(B_{bb}<0\) give strict concavity. All three
endpoint types are covered, with the split at .41 using a valid
increasing lower bound for the core coordinate. The diagonal curve is
strictly concave with both endpoints bounded.

The \(P\) contact cost decreases with the core coordinate on both side
and corner. Its minimum is therefore the core diagonal. I rederived
\[
 H'''/w=P'''w^2+3P''w'-P'
\]
and checked all sign choices in the three fixed curvature intervals.
They show \(H''\) decreases while remaining positive, and \(H'\)
increases while remaining negative. Evaluation at the slightly
extended endpoint .44152 therefore gives a valid lower bound for
every physical endpoint; the extended outer radical remains positive.

## 4. The new \(L\)-corner inequality

Using \(v=B+1/2\), \(U=Q-v^2\), and
\[
 N=(2B+1/2)v-Q,
\]
the derivatives take the independently checked form
\[
 L'=j-hB+kN/\sqrt U,\qquad
 L''=-h+k(2vU+BQ)/U^{3/2}.
\]
Consequently
\[
 \{\lambda(B-1/2)L'-L''\}U^{3/2}
 =\mathcal A U^{3/2}+\mathcal B
\]
with exactly the author's two polynomials. The polynomial
\(\mathcal A\) is positive by endpoint concavity. The reconstructed
degree-ten polynomial
\(\mathcal A^2U^3-\mathcal B^2\) has all eleven displayed positive
coefficient lower bounds. Thus the squared inequality gives the
claimed strict unsquared inequality; no sign assumption on
\(\mathcal B\) is needed.

The contact estimate
\(B\le1/2+(13/12)\sin x\) and Cauchy's inequality
\[
 \kappa/(\cos x+t\sin x)^2\ge12
\]
then give strict core-coordinate concavity when \(B>1/2\).
When \(B\le1/2\), the already established \(L''<0\) gives the same
conclusion directly. The side, first-feasible endpoint, and diagonal
alternatives are all covered.

For the final diagonal, I checked the derivative bound before .3
and the uniform lower curvature
\(1.69(.96)-1.165(.4)>1.1\) thereafter. The single point .3832 and
completed square prove the whole interval bound \(>.89777\).
The slight analytic extension to .44152 is harmless and explicitly
covered.

## 5. Exact arithmetic and artifact binding

A fresh copy of the author checker was executed in
\`/tmp/opposite_zero_audit_f57a7198\`.
All **149 strict comparisons passed**, and its complete JSON was
byte-identical to the saved author record.

The independent script rebuilds the polynomial from the derivative
identity. It then substitutes \(B=.5+.4t\) and solves the defining
Bernstein basis by triangular elimination. This is separate from
the author's direct basis-conversion sum. It verifies the full
polynomial identity, all **11 printed integer coefficient floors**,
and all **30 exact role coefficients**. These checks passed.

The continuous proof has no uncovered contact endpoint, sign case,
or axis branch within its stated scope. Every terminal inequality is
strictly above \(\gamma=.89765\).
