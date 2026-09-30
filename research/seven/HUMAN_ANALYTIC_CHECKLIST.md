# n=7 human-analytic proof checklist

## Scope

This is a research handoff for improving the existing seven-square proof to a
strong human-analytic standard.

This PR is deliberately isolated:

- [x] Change files only under `research/seven/**`.
- [x] Do not modify production Lean, public statements, general documentation,
      CI, or metadata.
- [x] Preserve the marker/contact/hexagon architecture unless a genuinely
      simpler mathematical argument replaces part of it.
- [ ] Deliver mathematical proofs and proposed Lean lemmas for a maintainer to
      integrate separately.

The goal is not fewer lines or fewer rational constants. The goal is that a
mathematically trained reader can see **why each substantive continuous
inequality is true** without having to trust or reverse-engineer an opaque
coefficient list.

## What is already good

The global proof is conceptual and should remain the backbone:

```text
admissible exterior states
  -> marker for every exterior square
  -> canonical pair
  -> four separating axes
  -> sign / active-label geometry
  -> marker separation >= pi/3
  -> six exterior markers form a regular hexagon
  -> equality gives neighbour contacts
  -> column packing classification
```

The audited n=7 path contains no `ExactCover`, generated stress-table
classification, interval-box mesh, `native_decide`, `Lean.ofReduceBool`,
or external numerical success premise.

The four axes, two transverse signs, active axial/side labels, capped-label
triangle, regular-hexagon combinatorics, and tiny `Fin n` enumerations are
legitimate mathematical case splits. They are not targets merely because they
are finite.

## What needs scrutiny

There are eight substantive uses of the Bernstein positivity criterion:

| ID | Production location | Mathematical role | Current certificate |
| --- | --- | --- | --- |
| A | `MarkerArc.arcCurvaturePolynomial_pos` | curvature of the marker-arc envelope | degree 8, 9 coefficients |
| B | `TargetBoundaryMonotonicity.ratio_derivative_lt_one` | monotonicity on the circular axial boundary | degree 5, 6 coefficients |
| C | `InwardAxialTarget.inward_turn_profile` | inward negative-turn profile | degree 5, 6 coefficients |
| D | `OppositeForward.opposite_axial_scalar` | opposite-forward axial scalar | degree 5, 6 coefficients |
| E1 | `ForwardNegativeTarget.axial_target_support`, small-turn branch | disk/tie-line support discriminant | degree 14, 15 coefficients |
| E2 | `ForwardNegativeTarget.axial_target_support`, large-turn branch | half-angle disk support bound | degree 7, 8 coefficients |
| E3 | `ForwardNegativeTarget.sideTarget_negative_pos`, small-turn branch | side-target disk support bound | degree 6, 7 coefficients |
| F | `InwardOppositeMinima.radialPolynomial_pos` | two-circle/radical discriminant | degree 11, 12 coefficients |

The existence of exact rational coefficients is **not itself a defect**. The
analytical n=6 work also uses many exact support weights, rational Taylor
bounds, endpoint constants and margins.

The concern is narrower:

> Does the proof explain the sign of the original geometric/analytic quantity,
> or does the coefficient vector become the only practical reason we know the
> sign?

For the strongest human-readable standard, an opaque Bernstein vector is not a
satisfactory final explanation even though Lean checks it exactly.

## Readability test for every substantive inequality

For every item A--F, produce a note that answers these questions in order.

- [ ] **Original quantity.** What geometric or analytic expression are we
      trying to bound before Taylor expansion or polynomialization?
- [ ] **Domain.** What is its exact continuous domain, and where does that domain
      come from geometrically?
- [ ] **Reduction.** Which exact inequalities reduce the original quantity to
      the auxiliary polynomial?
- [ ] **Reason for sign.** Is there a monotonicity, convexity/concavity,
      tangent/support, completed-square, factorization, or endpoint principle
      that explains the sign?
- [ ] **Constants.** For each non-obvious rational constant, state what it is
      doing: support slope, Taylor truncation, tangent coefficient, interval
      endpoint, or slack margin.
- [ ] **Equality/strictness.** Explain where equality could occur and why the
      theorem is strict when strictness is needed.
- [ ] **Lean skeleton.** Give the intended Lean lemma statement and the short
      chain of existing lemmas it should use.

A replacement is preferred when it makes the **reason for positivity visible**,
not merely when it reduces the coefficient count.

## Bernstein policy

Bernstein positivity is an exact theorem, not numerical sampling. It may still
appear as a final algebraic check, but only after the human argument has exposed
the structure.

For each of A--F:

- [ ] First attempt a direct whole-domain proof from the original quantity.
- [ ] Next attempt a low-complexity polynomial proof by monotonicity,
      convexity/concavity, factorization, or a sum/completed-square identity.
- [ ] If Bernstein remains, derive the polynomial explicitly from the preceding
      analytic inequalities.
- [ ] Explain why the chosen interval is natural.
- [ ] Explain how the Bernstein coefficients arise from the polynomial and
      interval, rather than presenting them as discovered data.
- [ ] If the vector is long or irregular, treat that as a sign to look one step
      earlier in the argument for a stronger geometric estimate.
- [ ] Do not accept “all coefficients are positive” as the sole human
      explanation for a central inequality.

The goal is not “zero Bernstein at all costs.” The goal is that Bernstein, if
retained, is bookkeeping at the end of a comprehensible proof rather than the
substantive proof itself.

## Rational constants and breakpoints

Do not classify a constant as problematic because it looks ugly.

A rational constant is acceptable when a reader can trace it to a visible
choice or inequality. The same applies to n=6.

Audit the hand-selected thresholds currently used in n=7, including
`1/6`, `1/3`, `2/3`, and `5/16`.

For every such threshold:

- [ ] Classify it as a geometric boundary, sign boundary, tangent/support
      switch, or convenience-only analytic split.
- [ ] Keep genuine geometric/sign boundaries.
- [ ] For a convenience-only split, attempt a whole-domain estimate.
- [ ] If it remains, derive why that threshold is a useful or natural point
      from an explicit inequality.
- [ ] Do not introduce a fine partition of a continuous interval.

The concern is unexplained regime engineering, not rational arithmetic.

## A — marker-arc curvature

Target:

- `SquaresInCircles/Seven/MarkerArc.lean`
- `arcCurvaturePolynomial_pos`

Current reduction:

[
P(x)=676(1-x^2)^3-9x^2(9-8x-4x^2)^3>0,
qquad 0le xle 3/4.
]

This controls the sign of the second derivative of the marker-arc envelope.

Tasks:

- [ ] Start from the two radical curvature terms in `arcEnvelopeSecond`,
      before cubing and expanding.
- [ ] Form a positive ratio if possible and study its logarithmic or ordinary
      derivative.
- [ ] Check whether the ratio is monotone on `[0,3/4]`, so one endpoint
      comparison suffices.
- [ ] If polynomialization is still cleaner, study `P`, `P'`, or a shifted
      polynomial for a short monotonicity/factorization proof.
- [ ] Document exactly why the curvature statement implies the marker-arc
      bound used later.

Preferred endpoint: a curvature/ratio argument a reader can reproduce without
nine unrelated coefficients.

## B — axial-boundary derivative ratio

Target:

- `SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean`
- `ratio_derivative_lt_one`

Current proof writes

[
1-mathrm{ratioD}(s)=
rac{N(X)}
 {5X(5X-4)^2(13-4X^2)}
]

and proves the quintic numerator (N(X)>0) by six Bernstein coefficients.

Tasks:

- [ ] Use `X^2+Y^2=13/4` before expanding.
- [ ] Separate the manifestly positive denominator from the real mathematical
      content.
- [ ] Determine the exact geometric `X` interval.
- [ ] Study (N') and (N'') on that interval.
- [ ] Try a tangent/chord lower bound or completed-square decomposition.
- [ ] If Bernstein remains, give a direct derivation of the quintic from the
      derivative-ratio geometry and explain why its positivity is plausible.

Preferred endpoint: the monotonicity of the boundary support should be the
main idea; the quintic should be secondary verification.

## C — inward axial turn profile

Target:

- `SquaresInCircles/Seven/InwardAxialTarget.lean`
- `inward_turn_profile`

Original inequality:

[
rac z{50}
le
sin z-rac45zcos z-rac34(1-cos z),
qquad 0le zleracpi2.
]

Current proof uses Taylor bounds plus a degree-5 Bernstein certificate.

Tasks:

- [ ] Analyze this displayed function directly.
- [ ] Compute its first two derivatives and determine whether monotonicity or
      convexity gives a one- or two-endpoint proof.
- [ ] Try to prove it from one coherent Taylor remainder estimate.
- [ ] Try a simple positive grouping of the existing quintic.
- [ ] Avoid a new arbitrary subinterval split.

This is a likely quick win because the original statement is already a clean
one-variable inequality.

## D — opposite-forward axial scalar

Target:

- `SquaresInCircles/Seven/OppositeForward.lean`
- `opposite_axial_scalar`

Original scalar:

[
1-rac{4pi}{15}+rac45z-(sqrt3-1)sin z
-rac12(1-cos z)>0,
qquad 0le zleracpi3.
]

Current proof uses elementary bounds on (pi,sqrt3), Taylor bounds, and a
degree-5 Bernstein certificate.

Tasks:

- [ ] Study the original scalar and its derivatives first.
- [ ] Determine whether its minimum is forced to an endpoint or a unique
      critical point.
- [ ] Try a global tangent/concavity lower bound.
- [ ] If the degree-5 polynomial remains, seek a short factorization or
      derivative proof.
- [ ] Keep the elementary rational bounds on (pi) and (sqrt3) explicit.

Again, the visible scalar should be the proof object, not its coefficient
vector.

## E — forward negative target

Target:

- `SquaresInCircles/Seven/ForwardNegativeTarget.lean`
- especially `axial_target_support` and `sideTarget_negative_pos`

This is the first major priority.

The current proof changes analytic method several times inside one geometric
sector:

- at `z <= 1/3`, the axial tie line is incorporated as a dual constraint and
  a degree-14 discriminant polynomial is certified;
- beyond `1/3`, a half-angle disk support estimate leads to a degree-7
  certificate;
- for a negative side-target turn, `z <= 1/6` invokes another degree-6
  certificate before the proof changes method again.

Tasks:

- [ ] Explain the geometric meaning of the dual variable
      `n=(3/40)(1-2 sin z)`.
- [ ] Derive the quantities `L`, `P`, and `U` conceptually rather than
      treating them as tuned expressions.
- [ ] Determine whether `z=1/3` is a genuine change in the optimal support
      argument or only where the chosen approximation ceases to work.
- [ ] Search for one support/tangent inequality valid on the full
      `[0,pi/2]` turn range.
- [ ] If one estimate cannot cover the whole interval, derive the switch point
      from equality of two mathematically natural bounds.
- [ ] For `sideTarget_negative_pos`, perform the same audit of `z=1/6`.
- [ ] Keep radicals and support functions unexpanded long enough to test
      monotonicity/curvature before introducing Taylor polynomials.
- [ ] Separate the geometric disk/tie-line optimization from the final
      one-variable trigonometric inequality.
- [ ] Track contact/equality cases independently of positive slack estimates.

Preferred endpoint: at most a small number of natural analytic regimes, each
with a visible support principle and a simple one-variable inequality. A long
Bernstein vector should not be what tells the reader why the sector works.

## F — inward opposite minima

Target:

- `SquaresInCircles/Seven/InwardOppositeMinima.lean`
- the two-circle/radical-envelope argument leading to
  `radialPolynomial_pos`

This is the second major priority.

The present argument reaches a degree-11 polynomial only after bounding a
radical envelope and taking a discriminant. That suggests the expansion may be
hiding the actual geometry.

Tasks:

- [ ] Reconstruct the inequality immediately before the discriminant.
- [ ] Draw/write the two-circle support picture in state coordinates.
- [ ] Search for a tangent-line comparison between the two radical envelopes.
- [ ] Search for a completed square before eliminating the radical.
- [ ] Parameterize the circular boundary by an angle and test whether the
      radical difference is monotone or convex in that parameter.
- [ ] Derive the critical-point equation before squaring; check whether it has
      at most one solution.
- [ ] Test a support-cone or radial-support argument analogous in spirit to the
      exceptional OWN/OWN corner in the n=6 analytical work.
- [ ] Only after these fail, return to `radialPolynomial`.
- [ ] If the polynomial remains, derive it line by line from the geometric
      inequality and look for a human sign proof stronger than a 12-entry
      Bernstein vector.

Preferred endpoint: the reader understands the two-circle comparison before
seeing any expanded polynomial.

## Preserve the all-gaps assembly

Targets:

- `SquaresInCircles/Seven/FixedGap.lean`
- `SquaresInCircles/Seven/AllGaps.lean`
- `SquaresInCircles/Seven/SmoothMinima.lean`

These modules encode good high-level mathematics.

- [ ] Preserve the four-axis fixed-gap structure.
- [ ] Preserve the convex reduction of capped labels to the capped triangle.
- [ ] Preserve the small-gap marker-arc contradiction.
- [ ] Preserve the leftmost-minimum argument for larger gaps.
- [ ] Ensure every simplified sector lemma has the same strictness/equality
      information needed by the contact classification.
- [ ] Do not replace this structure with a new continuous finite partition.

## Research artifacts to produce

All artifacts remain under `research/seven/**`.

For each completed item A--F:

- [ ] write a standalone mathematical note;
- [ ] state the production theorem being replaced;
- [ ] state the exact domain and hypotheses;
- [ ] give the human proof before the Lean skeleton;
- [ ] list any reusable existing Lean lemmas;
- [ ] give exact endpoint/factor margins where arithmetic closure is needed;
- [ ] record any exploratory computation separately from the proof;
- [ ] never use exploratory numerical success as a theorem premise.

Maintain a summary table:

| ID | Current method | Human explanation recovered? | Replacement found? | Integration note |
| --- | --- | --- | --- | --- |
| A | Bernstein degree 8 | [ ] | [ ] | |
| B | Bernstein degree 5 | [ ] | [ ] | |
| C | Bernstein degree 5 | [ ] | [ ] | |
| D | Bernstein degree 5 | [ ] | [ ] | |
| E1 | Bernstein degree 14 | [ ] | [ ] | |
| E2 | Bernstein degree 7 | [ ] | [ ] | |
| E3 | Bernstein degree 6 | [ ] | [ ] | |
| F | Bernstein degree 11 | [ ] | [ ] | |

## Priority

1. [ ] E — understand and simplify the forward-negative support regimes.
2. [ ] F — recover the geometry hidden by the degree-11 discriminant.
3. [ ] C and D — likely simple one-variable cleanups.
4. [ ] A and B — curvature/ratio proofs that may admit monotonicity arguments.
5. [ ] Re-audit all rational breakpoints after stronger inequalities are found.
6. [ ] Re-check the fixed-gap/all-gaps assembly.

Coefficient count alone does not determine priority. E and F rank first because
their current expansions obscure the preceding geometry.

## Definition of done

The research task is complete when:

- [ ] every Bernstein site A--F has a human-readable derivation from the
      original geometric/analytic quantity;
- [ ] every site for which Bernstein remains uses it only as transparent final
      algebraic verification, not as the primary reason for positivity;
- [ ] the large E and F certificates have either been replaced or accompanied
      by a convincing human proof that explains their sign before coefficient
      verification;
- [ ] every convenience-only interval split has been removed or given a
      mathematical derivation;
- [ ] no interval-box search, generated continuous cover, or external success
      result is introduced;
- [ ] equality/contact information is preserved;
- [ ] a maintainer can integrate the proposed lemmas without reverse-engineering
      the mathematics from the current Lean coefficient vectors.

## Audit status

This checklist is a plan, not a claim that the simplification has been carried
out.

The current n=7 proof is exact and formal at source level. The open question is
whether all of its hardest one-variable inequalities meet the stronger
human-readable standard above. Under that standard, the eight Bernstein sites
are genuine audit obligations until their mathematical explanations are
written down.
