# n=7 human-analytic simplification checklist

## Scope

This is a research/integration handoff checklist for simplifying the existing
seven-square proof to a stricter human-analytic style.

This branch is intentionally **research-only**:

- [x] Keep all changes in `research/six/**`.
- [x] Do not modify `SquaresInCircles/**`, root files, general documentation,
      CI, metadata, or public theorem statements in this PR.
- [x] Preserve the existing global n=7 proof architecture unless a local
      simplification clearly requires otherwise.
- [ ] Produce proof arguments and proposed Lean lemmas that a maintainer can
      incorporate into the production source separately.

The target is not "fewer Lean lines" by itself. The target is a proof whose
substantive inequalities can be followed and checked by a human without
reverse-engineering long numerical coefficient certificates.

## Current assessment

The core seven-square argument is already conceptual and should be preserved:

```text
admissible exterior states
  -> markers
  -> canonical pair
  -> four separating axes
  -> sign / active-label cases
  -> marker gap >= pi/3
  -> six exterior markers form a regular hexagon
  -> neighbour contacts
  -> column packing classification
```

The current proof does **not** use the old n=6-style `ExactCover`, generated
stress rows, interval-box search, `native_decide`, or an external numerical
success result.

The main human-readability issue is the analytic tail. Eight substantive
Bernstein-basis positivity calls currently carry 69 displayed rational
coefficients. Several sectors also switch estimates at hand-chosen rational
thresholds such as `1/6` and `1/3`.

The goal is to replace as much of that machinery as practical with visible
whole-interval monotonicity, convexity/concavity, tangent/support arguments,
completed squares, or short factorizations.

## Acceptance standard

A proposed replacement should satisfy the following.

- [ ] No external numerical oracle or script success is a theorem premise.
- [ ] No exhaustive mesh, interval-box subdivision, or generated table proves
      a continuous inequality.
- [ ] Geometric finite splits are allowed: the four separating axes, transverse
      signs, active labels, capped-label triangle, sign walls, and genuine
      label-boundary transitions are part of the mathematics.
- [ ] Continuous ranges should be handled by one whole-domain inequality,
      monotonicity/convexity/concavity, or a small number of mathematically
      explained regions.
- [ ] Exact Taylor inequalities are allowed when their remainder/sign is proved.
- [ ] Short explicit polynomial identities are allowed.
- [ ] Long unexplained vectors of rational coefficients should not be the
      primary mathematical explanation.
- [ ] If a rational breakpoint remains, document the structural reason for it
      (sign change, tangent switch, geometric transition, or a proved optimal
      analytic regime), rather than merely "this estimate works on this side".
- [ ] Every replacement note should state the exact production theorem it is
      intended to replace and the hypotheses it uses.

## Keep: conceptual finite structure

Do **not** spend effort removing the following merely because they are finite:

- [ ] Keep the four separating axes in the canonical pair.
- [ ] Keep the two transverse signs where the formulas genuinely differ.
- [ ] Keep active axial/side labels and the capped-label reduction.
- [ ] Keep the capped-label triangle / convex-combination argument.
- [ ] Keep the regular-hexagon finite combinatorics at equality.
- [ ] Keep tiny `Fin n` enumeration used only for index bookkeeping.

These are human mathematical case splits, not numerical classification.

## Workstream A — marker arc curvature

Production target:

- `SquaresInCircles/Seven/MarkerArc.lean`
- theorem `arcCurvaturePolynomial_pos`

Current mechanism:

- degree-8 polynomial;
- 9 positive Bernstein coefficients.

Checklist:

- [ ] Rewrite the curvature comparison before full polynomial expansion.
- [ ] Express the sign as a comparison of the two radical curvature terms.
- [ ] Try a monotone ratio after clearing only manifestly positive factors.
- [ ] Try a derivative-sign proof for that ratio on `[0, 3/4]`.
- [ ] If a polynomial remains, search for a short factorization or a low-degree
      monotonicity argument rather than a Bernstein vector.
- [ ] Record an exact endpoint margin sufficient for the marker-arc theorem.
- [ ] Write a proposed Lean proof skeleton using existing derivative/Taylor
      lemmas.

Desired outcome: eliminate this Bernstein call completely.

## Workstream B — axial-boundary derivative ratio

Production target:

- `SquaresInCircles/Seven/TargetBoundaryMonotonicity.lean`
- theorem `ratio_derivative_lt_one`

Current mechanism:

- positivity of a quintic in the radial coordinate;
- 6 Bernstein coefficients.

Checklist:

- [ ] Substitute the circle identity `X^2 + Y^2 = 13/4` as early as possible.
- [ ] Factor all positive denominator terms explicitly.
- [ ] Study the numerator directly on the actual `X` interval.
- [ ] Try monotonicity of the numerator.
- [ ] Try tangent/chord bounds at the geometric interval endpoints.
- [ ] Look for a completed-square decomposition after using the circle relation.
- [ ] Produce a short proof of `1 - ratioD > 0` that explains the geometry.

Desired outcome: replace the quintic Bernstein certificate by one derivative or
completed-square argument.

## Workstream C — inward axial turn profile

Production target:

- `SquaresInCircles/Seven/InwardAxialTarget.lean`
- theorem `inward_turn_profile`

Current mechanism:

- one quintic auxiliary polynomial;
- 6 Bernstein coefficients.

Checklist:

- [ ] Differentiate the target inequality before introducing the quintic.
- [ ] Test whether the difference is monotone or convex on `[0, pi/2]`.
- [ ] Try one Taylor lower bound with a manifestly signed remainder.
- [ ] Try grouping the current quintic into positive factors on the interval.
- [ ] Avoid introducing any new subinterval unless it corresponds to a sign
      change of an explicit derivative.

Desired outcome: a direct one-variable calculus/Taylor proof.

## Workstream D — opposite-forward axial scalar

Production target:

- `SquaresInCircles/Seven/OppositeForward.lean`
- theorem `opposite_axial_scalar`

Current mechanism:

- degree-5 auxiliary polynomial on a bounded interval;
- 6 Bernstein coefficients.

Checklist:

- [ ] Analyze the original trigonometric scalar directly.
- [ ] Compute first and second derivatives and locate possible extrema.
- [ ] Try a global tangent/concavity lower bound.
- [ ] Try an explicit positive factorization of the existing degree-5
      polynomial if calculus is not cleaner.
- [ ] Keep the existing elementary bounds on `sqrt 3` and `pi` explicit.

Desired outcome: remove this Bernstein call.

## Workstream E — forward negative target

Production target:

- `SquaresInCircles/Seven/ForwardNegativeTarget.lean`

Current mechanism:

- 3 Bernstein certificates with coefficient counts 15, 8, and 7;
- hand-chosen switches including `z <= 1/3` and `z <= 1/6`;
- a mix of Cauchy--Schwarz disk support and Taylor bounds.

This is a major simplification target.

Checklist:

- [ ] Identify the exact geometric quantity each of the three certificates is
      bounding before expansion.
- [ ] Re-derive the target support using one stronger disk/tangent estimate.
- [ ] Try to keep the radical/support expression intact long enough to prove a
      monotonicity or curvature statement.
- [ ] Investigate whether one affine or quadratic support majorant works over
      the full turn interval.
- [ ] Replace the `1/3` split if it is only an artifact of choosing different
      Taylor truncations.
- [ ] Replace the `1/6` split if it is only an artifact of the small-angle
      polynomial; if retained, prove why it is a natural tangent/sign switch.
- [ ] Try endpoint reduction from a whole-domain concavity statement.
- [ ] Separate source-state geometry from one-variable trigonometric analysis so
      the final human proof has a visible two-step structure.
- [ ] Document equality/contact behavior separately from strict positivity.

Desired outcome: reduce three coefficient certificates to at most one short
explicit algebraic lemma, ideally none.

## Workstream F — inward opposite minima

Production target:

- `SquaresInCircles/Seven/InwardOppositeMinima.lean`
- theorem `radialPolynomial_pos` and the radical-envelope argument that uses it.

Current mechanism:

- degree-11 `radialPolynomial`;
- 12 large rational Bernstein coefficients;
- polynomial is obtained from a discriminant after bounding a two-circle /
  radical envelope.

This is the hardest and highest-value target.

Checklist:

- [ ] Go one step earlier than `radialPolynomial`; do not begin by trying to
      beautify the degree-11 expansion.
- [ ] Write the two-circle/radical support comparison in geometric coordinates.
- [ ] Search for a tangent-line comparison between the two radical envelopes.
- [ ] Search for a completed-square inequality before taking the discriminant.
- [ ] Test whether the relevant radical difference is monotone or convex along
      the circular boundary parameter.
- [ ] Test whether the unique possible minimum can be characterized by the
      derivative equation and bounded directly.
- [ ] Try a support-cone argument analogous to the repaired exceptional OWN
      corner in the n=6 analytical proof.
- [ ] If a polynomial is unavoidable, derive it from a visible sum-of-squares or
      factored identity rather than a 12-entry coefficient vector.
- [ ] Record the exact equality/strictness conditions needed by the contact
      classification.

Desired outcome: replace the degree-11 Bernstein certificate by a geometric
support/curvature lemma.

## Workstream G — rational breakpoints audit

Current hand-selected thresholds include values such as:

- `1/6`;
- `1/3`;
- `2/3`;
- `5/16`.

Checklist for each occurrence:

- [ ] Classify it as one of:
      geometric boundary / derivative sign boundary / tangent switch /
      convenience-only analytic split.
- [ ] Keep geometric/sign boundaries.
- [ ] For convenience-only splits, attempt a whole-domain estimate.
- [ ] If a convenience split must remain, derive the threshold from an explicit
      inequality rather than presenting it as an unexplained magic constant.
- [ ] Record which splits disappear after Workstreams A--F.

## Workstream H — preserve the all-gaps argument

Production targets:

- `SquaresInCircles/Seven/AllGaps.lean`
- `SquaresInCircles/Seven/SmoothMinima.lean`

The current high-level argument is strong and should not be rewritten merely
for stylistic uniformity.

Checklist:

- [ ] Preserve the small-gap marker-arc contradiction.
- [ ] Preserve the leftmost-minimum argument for larger gaps.
- [ ] Confirm replacement sector lemmas still provide the same strict
      fixed-gap statements and equality cases.
- [ ] Avoid adding a new continuous partition in `AllGaps`.
- [ ] Keep equality classification at `pi/3` explicit.

## Workstream I — proposed handoff artifacts

All artifacts in this research PR should remain under `research/six/**`.

- [ ] Write one note per completed workstream with:
      exact target theorem, mathematical reformulation, proof, and proposed
      Lean skeleton.
- [ ] Maintain a table mapping old Bernstein calls to proposed replacements.
- [ ] Record which existing n=7 lemmas can be reused unchanged.
- [ ] Record any new generic lemma that would be worth adding to
      `Seven/Analysis.lean` by the integrator.
- [ ] Do not patch production Lean in this PR.
- [ ] Do not update global docs or metadata in this PR.
- [ ] Keep numerical experiments, if any, clearly marked exploratory and never
      use their success as a proof premise.
- [ ] When a proof is complete, include exact rational endpoint/factor margins
      so the integrator does not need to rediscover constants.

## Suggested order

Work in increasing difficulty:

1. [ ] Workstream C — inward axial turn profile.
2. [ ] Workstream D — opposite-forward axial scalar.
3. [ ] Workstream B — axial-boundary derivative ratio.
4. [ ] Workstream A — marker arc curvature.
5. [ ] Workstream E — forward negative target.
6. [ ] Workstream F — inward opposite minima.
7. [ ] Workstream G — remove convenience-only breakpoints made obsolete by the
       stronger lemmas.
8. [ ] Workstream H — re-check the fixed-gap/all-gaps assembly against the
       simplified sector lemmas.

The first four are plausible quick wins. E and especially F are the places
most likely to require genuinely new inequalities.

## Definition of done

This research task is complete when:

- [ ] each of the eight current substantive Bernstein calls has either:
      - a human-analytic replacement proof, or
      - a written justification for why a short explicit polynomial proof is
        still the cleanest option;
- [ ] no replacement relies on interval-box search, a generated table, or an
      external success result;
- [ ] convenience-only numerical subintervals have been removed or explained;
- [ ] the marker/contact/hexagon proof architecture is unchanged unless a
      documented simplification improves it;
- [ ] a maintainer can transfer the proposed lemmas into production Lean without
      having to reconstruct the mathematical idea from numerical coefficients.

## Audit baseline

The checklist is based on a source audit of the n=1--5 and n=7 case files and
their shared `Common/` dependencies. The audit found no `ExactCover`,
`FixedData`, `ProofTools.Certificate`, `native_decide`,
`Lean.ofReduceBool`, external script premise, or interval-box classifier on
the n=7 path.

The eight Bernstein uses identified above are exact in-kernel algebraic proofs,
not sampled numerical checks. This project is therefore a simplification of an
already analytical proof, not a conversion from an external/computer-assisted
proof to a formal proof.
