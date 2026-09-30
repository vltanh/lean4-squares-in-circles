# Seven-square human-proof handoff

## What has been delivered

All eight Bernstein positivity sites in the audited seven-square proof now
have written human-readable replacements. The replacements use geometric
support, first/second derivatives, a ratio majorant, or explicit factored
squares. None needs a Bernstein coefficient vector.

This is a completed mathematical research handoff, not a production-code
integration or a claim of new Lean kernel acceptance. The production proof
still contains its original Bernstein arguments until a maintainer chooses
to incorporate these notes.

PR: #8, branch `research/seven-human-analytic`.
Frozen production baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
All files changed by this work are under `research/seven/`.

## Reading order

Start with [E_FORWARD_TARGET_PROOF.md](E_FORWARD_TARGET_PROOF.md), the largest
conceptual simplification. It replaces all three forward-negative target
certificates and both old numerical branch cuts in those statements.

Then read [F_INWARD_OPPOSITE_PROOF.md](F_INWARD_OPPOSITE_PROOF.md), which
explains the two-circle comparison, its completed square, and why the remaining
degree-11 polynomial is decreasing rather than relying on twelve Bernstein
coefficients.

The smaller independent replacements are
[A_MARKER_CURVATURE_PROOF.md](A_MARKER_CURVATURE_PROOF.md),
[B_BOUNDARY_RATIO_PROOF.md](B_BOUNDARY_RATIO_PROOF.md),
[C_INWARD_TURN_PROOF.md](C_INWARD_TURN_PROOF.md), and
[D_OPPOSITE_FORWARD_PROOF.md](D_OPPOSITE_FORWARD_PROOF.md).

[G_BREAKPOINTS_AND_ASSEMBLY.md](G_BREAKPOINTS_AND_ASSEMBLY.md) audits the
remaining regime changes, gives additional simplifications, and maps the
replacement statements back into the existing global proof.
The tracked requirements are in
[HUMAN_ANALYTIC_CHECKLIST.md](HUMAN_ANALYTIC_CHECKLIST.md).

## Exact replacement map

| Production file under `SquaresInCircles/Seven/` | Replace / simplify | Human proof |
| --- | --- | --- |
| `MarkerArc.lean` | Body of `arcCurvaturePolynomial_pos` | Bound H/(1-x^2) by 9-6x, then maximize x^2(9-6x)^3 at its derived critical point 3/5. |
| `TargetBoundaryMonotonicity.lean` | The polynomial positivity block in `Boundary.ratio_derivative_lt_one` | Its quintic numerator is concave on [8/5,7/4]; both endpoints are positive. |
| `InwardAxialTarget.lean` | Body of `inward_turn_profile` | A square plus a factored Taylor error on [0,1], then a derivative-positive tail. |
| `OppositeForward.lean` | Body of `opposite_axial_scalar` | A fixed derivative vector has norm below 9/10; the total possible decrease cannot exhaust the initial reserve. |
| `ForwardNegativeTarget.lean` | Body of `axial_target_support` (two Bernstein calls) | A proved residual-force cone plus a tangent parabola on [0,pi/6]; concavity of half-angle disk support on [pi/6,pi/2]. |
| `ForwardNegativeTarget.lean` | Body of `sideTarget_negative_pos` (one Bernstein call) | Split by the actual support/tangent coefficient signs; the small remaining regime has a cubic squared-support margin. |
| `InwardOppositeMinima.lean` | Body of `radialPolynomial_pos` | The negative constant term of P' dominates all its positive terms on [0,1]; evaluate the decreasing P at 5/8. |

The old auxiliary polynomials need not be retained for C, D, or E. Their
production callers require the trigonometric/support statements, not those
particular polynomial witnesses. A, B, and F preserve the polynomial interface
where that is the least disruptive integration point.

## Principal positive reserves

These margins are consequences of the written proofs, not sampled minima.

| Item | Proved reserve |
| --- | --- |
| A | P(x) >= (518177/3125)(1-x^2)^3 on [0,3/4]. |
| B | N(X) >= 20113/256 on [8/5,7/4]. |
| C, 0<=z<=1 | F(z) >= z[(9/40)(z-5/6)^2+19/800]. |
| C, 1<=z<=pi/2 | F(z) >= 3z/100. |
| D | The original scalar is greater than 2/35 on [0,pi/3]. |
| E small axial | T(z) >= M(z) >= (z-1/5)^2/16+3/2000. |
| E large axial | The concave lower bound has endpoint reserves greater than 1/84 and 17/105. |
| E tangent-side regime | T(z) >= 13z/22500 > 0. |
| E small-side regime | The squared support margin is at least 119z/720 > 0. |
| F | P'(z) <= -253/547560 on [0,1], and P(5/8)>1/4000. |

Strictness domains matter. C vanishes at zero. E's side-target result and F's
completed-square conclusion still require z>0; they do not exclude the
original z=0 contacts. A, B, D and the axial-target E result retain strictness
on their closed domains.

## Additional breakpoint simplifications

G supplies three additional low-disruption proposals:

1. Replace `InwardSideTarget.targetH_zero_gt_one`'s label regimes by one
   increasing trigonometric profile. Its minimum is greater than 1196/1125.
2. Replace the separate opposite-side/axial cut at 1/3 by the actual crossing
   of its two affine clearance bounds,
   `z_star=pi/2-5/4+1/68`.
3. Replace the forward-positive cutoff 5/16 by 3/10, the exact zero of the
   already available coarse support reserve.

The retained 2/5 source-label split has an explicit 1/1050 marker-support
reserve. G explains why it is a convenient overlap point rather than a
geometric singularity. Label intersections, support sign changes and the
four-axis/sign combinatorics remain: removing meaningful geometric cases
would make the proof less clear, not more analytical.

## Why the global proof is preserved

The route remains

```text
admissible states and markers
  -> separating-axis support inequalities
  -> the same strict fixed-gap sector statements
  -> marker gap at least pi/3, equality only at the same contacts
  -> six exterior markers form a regular hexagon
  -> contact-cycle and central-square rigidity
  -> the unchanged three-parameter column family.
```

The construction and least-radius conclusion at `sqrt(13)/2` are unchanged.
The original `Packing`, `Congruent`, public theorem statements and equality
classification have not been edited. These are local proofs of the same
lemmas, not a new hypothesis added to the problem or a change to the model.

## Validation performed

A separate exact symbolic/rational calculation checked 52 identities and
margins in the notes, including:

- the curvature-ratio factorization, derivative and maximum in A;
- the circle derivative identity and translated second derivative in B;
- the Taylor-to-quintic and completed-square identities in C;
- the derivative-vector norm and final reserve in D;
- E's residual-force identities, cone squared-support identity, tangent
  parabola, half-angle curvature, and side squared-support margin;
- F's discriminant, completed square, derivative reserve and endpoint;
- the new monotone side profile and clearance-crossing bounds in G.

All 52 checks passed. They use exact expressions, not floating-point grids or
sampled minima. They are development cross-checks, not imported premises of
any theorem. The notes themselves contain the inequalities and calculus
arguments establishing the whole-domain conclusions.

The named calculus helpers were checked in the baseline `Seven/Analysis.lean`:
`monoOn_of_hasDeriv_nonneg`, `antiOn_of_hasDeriv_nonpos`, `curvature_tangent`,
`positive_of_second_nonpos`, and `trig_concave_gt`.

## Integration work deliberately left to the maintainer

The Lean blocks in these notes are explicitly labelled proposed statements or
implementation sketches. They are not drop-in compiled files; ellipses denote
the described implementation work, not completed Lean proof terms.

For each selected replacement, implement the helper bodies with the displayed
identities and the existing calculus lemmas, preserving the original theorem
statement. Compile before moving to the next production lemma. Do not prove a
replacement by importing or applying the old Bernstein-based result it is meant
to replace. Then run the existing case tests, public theorem checks, axiom audit
and an elaborated dependency review.

No production Lean integration, Lean build, Comparator, axiom audit, or
independent kernel replay was performed as part of this research handoff.
