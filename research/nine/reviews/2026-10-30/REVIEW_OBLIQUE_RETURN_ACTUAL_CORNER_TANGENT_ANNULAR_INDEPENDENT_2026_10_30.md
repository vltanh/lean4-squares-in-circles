# Independent review of the oblique-return actual-corner tangent proof

**Date:** October 30, 2026 UTC. **Reviewer:** annular-capacity agent.

**Verdict: PASS at the complete stated scope. No source repair is required.**

## 1. Frozen object and independent reconstruction

I read the entire source
`OBLIQUE_ALIGNED_ENDPOINT_RETURN_SECTION_BOUND_BY_ACTUAL_UPPER_CORNER_TANGENT_2026_10_30.md`
and reconstructed its contact cover, section-existence argument, both
active-edge calculations, tangent identity and literal caller.
The reviewed source is 15,777 bytes with SHA256

`a43df2c0bdf368d43c5858829e9a5594b8ac202fcfcf5b59e10d9282f8572bea`.

The source was not edited. I independently developed a different squared
inequality proof for the same below-floor section problem before reading
this manuscript. This review checks the author's distinct tangent argument
in full; agreement of its conclusion with that other proof is not used as
evidence for an unchecked step.

The theorem retains the original strict upper-left common normal at the
original endpoint corner. Its core is geometric and uses physical boundary
contact at both squares, not positive circle load or a restricted force
star. The above-side condition on C is present in the scope and is used
explicitly in the section-existence estimate.

## 2. Exhaustive original contact types

The aligned endpoint's farthest corner has squared norm
`(x+1)^2+(1-h)^2=q`, including the radial case `h=1/2`.
The reflected own-coordinate inner-face parameters obey
`kappa-ell0=x+h>163/120>1`. The source fully reproves the face
lemma: a shared supporting side supplies an actual neighbor vertex in the
endpoint face interval, and every one of the neighbor's four corner norms
is then strictly below q. This handles all original side endpoints and
does not use an all-owned graph selection.

At the actual contact corner p, C cannot contain p in its open interior.
If p is a vertex of C, its right-angle tangent cone cannot enter B's open
southeast interior cone. Parameterizing its two inward edge directions
therefore leaves exactly the above-floor or left-halfplane alternatives.
The left-halfplane alternative is forbidden by the face lemma. A remaining
axis-aligned above-floor vertex cone would be northeast or northwest:
the former does not minimize the original strict upper-left normal, while
the latter lies in the forbidden left halfplane. Thus this branch is
genuinely tilted, as claimed.

If p is in the relative interior of a C side, its actual inward normal is
uniquely the original n. The chart

    C=p+[0,1]n+[-r,1-r]v, 0<r<1

is exact and retains the original side parameter. Its bottom vertex is
strictly below h, so it is precisely the remaining below-floor branch.
No new normal is substituted into an old force or torque equation.

## 3. Section existence before its endpoints are used

The square contains p below the line at `rho=5/4`. If its top were no
higher than that line, the exact chart would imply

    beta+(1-r)*alpha<=k, k=rho-h in [3/4,7/8].

This gives the stated complete upper bound on its rightward reach:

    (1-r)*beta<=k^2/(4sqrt(1-k^2))
                <=49/(32sqrt(15))<2/5.

Each comparison is valid on the closed beta interval; the final radical
comparison has the stated positive square reserve. The full horizontal
range is then inside `(-1/2,17/12)`. The given whole-square positive
height hypothesis and the supposed upper bound place its vertical range
in `(0,5/4]`. Thus all actual corner norms squared are below `257/72`.

The original endpoint itself forces
`q>15061/3600`, whose excess over `257/72` is `737/1200`.
The return square would have no circle contact, a contradiction. The line
therefore crosses strictly between C's horizontal supporting lines, so its
section is nondegenerate and no later endpoint is fictitious.

## 4. Both active section-edge alternatives

In the actual side chart, eliminating the side coordinate at height rho
gives `X=x+(beta/alpha)k-u/alpha`. This is strictly decreasing in u.
The largest allowed u is exactly `min(1,(k+alpha*r)/beta)`.
The already proved section existence supplies the remaining interval
constraints. Thus the two formulas in Section 5 cover every possible
left endpoint, including their common equality boundary.

For the opposite-n-face case, the elementary squared identity

    (1-beta*k)^2-alpha^2(1-k^2)=(beta-k)^2

has positive unsquared quantities and gives
`ell<=x-sqrt(1-k^2)`. The source's G(h) is strictly increasing:
its derivative comparison is equivalent to `Q*k^2>(h+1)^2`,
which follows uniformly from `Q>4`, `k>=3/4`, and `h+1<=3/2`.
The exact lower endpoint radical bounds give the strict margin `1/48`.
No active-angle subinterval is assumed in this branch.

## 5. Tangent contradiction for the bottom-v-edge case

Under the contrary inequality `ell>=f(h)`, the comparison parameter
`r0=beta*d-alpha*k` satisfies `r0>=r>0`. Its positivity yields
`alpha/beta<d/k<4/5`, and hence `beta>3/4` over the complete
original parameter range. This is a proved consequence of the assumed
bad section value, not an added small-angle hypothesis.

The actual upper corner is Z. The comparison point Z0 is displaced from
Z only along the displayed own axis, with
`z0.Z>=z0.Z0` because `z0.v>0` and `r0>=r`. The source keeps Z
as the actual contained point; Z0 is solely an algebraic comparison.

I independently expanded the identity for `(z0.Z0-Q)/alpha`. Starting
with the substitution for r0, the coefficient independent of alpha is

    (B0-A0)+(9*A0/4-B0*K)*beta,

and the alpha coefficient is

    A0*K+9*B0/4-Q-(A0+B0)/(1+beta).

The identity uses only `alpha^2+beta^2=1` and `A0^2+B0^2=Q`;
all signs and the factor `1+beta` are correct.

For the first term, its beta coefficient is at least `67/320>0`.
Using the proved lower bound on beta and handling the resulting negative
B0 coefficient with B0's upper bound gives the strict lower bound
`281/1280`. There is no reversed inequality at that negative coefficient.

For the bracket, J(B0) is concave because its circle-root coefficient is
positive. Its minimum is therefore bounded below by its endpoint values.
Those endpoint estimates are respectively greater than `11929/6400` and
equal to `7333/3840`, both above `37/20`, with the stated reserves.
The exact coupled relation `A0^2+B0^2=Q` gives `A0+B0<3`, and
`beta>3/4` then bounds the subtracted quotient by `12/7`.
The bracket is strictly greater than `19/140`.

Both terms in the tangent identity are positive. Hence `z0.Z0>Q` and
then `z0.Z>Q`. This contradicts Cauchy's inequality for the unchanged
actual corner Z in `D_q subset D_Q` and the reference vector of norm
`sqrt(Q)`. The whole slider interval and both active-edge boundary values
have therefore been covered continuously.

## 6. Full conclusion and literal endpoint application

The below-floor side-interior branch has the strict actual section bound.
The other physical branch is wholly above h and is necessarily tilted
because the original common normal is strictly oblique. A separate
strict profile theorem for such above-floor tilted units therefore joins
without a missing contact type. The local source itself correctly leaves
that additional profile theorem separate.

In the long-endpoint caller, the complete preceding alignment theorem
supplies its full true-degree hypotheses. The original return normal has
positive y component while the other original force is horizontal. Full
endpoint equilibrium forces a negative total circle y resultant, so the
aligned endpoint center is nonpositive in height. Its zero-height radial
case keeps both physical circle corners and all original weights. The
coupled endpoint bound supplies `-1/8<=y_B<=0`, giving precisely
the stated h interval. The actual contact-locus and whole-return-side
theorems provide the original oblique point and C's positive-height
premise. Thus every geometric hypothesis is literal, and no old endpoint
force has been omitted.

This source closes all oblique local contact types for the required
section estimate. It does not itself assert a complete cycle or unrestricted
nine-square theorem, and it does not change any original certificate.

## 7. Verification boundary

All nine rational margins used in this independent review were recomputed
exactly. The full tangent identity was reconstructed algebraically, and all
continuous domains, strict comparisons, closed edge-transition cases and
physical-circle hypotheses were checked. No numerical pose search,
finite-angle sampling, stress optimization, source edit, ledger change,
Lean compilation, CI execution or publication was performed for this review.
