# Seven-square human-proof handoff

PR #8 — `research/seven-human-analytic`.
Production baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
All repository changes are confined to `research/seven/`.

## Delivered

The eight Bernstein sites A–F and all identified second-pass numerical
hotspots J–N have written mathematical replacement arguments. The global
marker/separating-axis/contact/hexagon proof remains intact.

This is a completed research handoff for the identified humanization tasks,
**not a production integration or a newly kernel-checked Lean proof**. The
production source still uses its original arguments until a maintainer
implements and checks the proposed replacements.

The status checklist is [HUMAN_ANALYTIC_CHECKLIST.md](HUMAN_ANALYTIC_CHECKLIST.md).
The new dependency and arithmetic audit is
[SECOND_PASS_AUDIT.md](SECOND_PASS_AUDIT.md).

## Read the second pass first

1. [L_COARSE_TRANSITION_PROOF.md](L_COARSE_TRANSITION_PROOF.md) replaces
   five-decimal transition/radical enclosures with a monotone circle/line
   intersection argument. Its comparison point is derived from the diagonal
   angle domain the proof actually needs.
2. [J_TRANSITION_ENDPOINT_PROOF.md](J_TRANSITION_ENDPOINT_PROOF.md) replaces
   the interior anchor 18/25 by the geometric diagonal junction. Stronger
   curvature and a circle-correlated endpoint comparison give the uniform
   transition-profile reserve 1/32000. The other diagonal-value certificate
   follows by angle order, without a separate numerical evaluation.
3. [K_MARKER_ENVELOPE_PROOF.md](K_MARKER_ENVELOPE_PROOF.md) replaces the tangent
   at 1/8 and its six-digit brackets by uniform curvature and exact origin data.
4. [M_STATE_SEPARATION_PROOF.md](M_STATE_SEPARATION_PROOF.md) rewrites the
   tuned state inequalities as a disk projection and two corner-distance
   contradictions.
5. [N_INITIAL_RATIO_PROOF.md](N_INITIAL_RATIO_PROOF.md) compares the initial
   ratio directly with the smallest geometric angle pi/12; no decimal bound
   on sqrt(3) is needed.
6. [P_ELEMENTARY_PI_BOUNDS.md](P_ELEMENTARY_PI_BOUNDS.md) supplies a short
   arctangent-integral derivation of the elementary pi bounds used in L.

These arguments remove the audited chains of separately bracketed test-point
coordinates, radical values, reciprocals, and trigonometric values. They do
not claim that all rational arithmetic disappears.

## First-pass Bernstein replacements

[E_FORWARD_TARGET_PROOF.md](E_FORWARD_TARGET_PROOF.md) replaces all three
forward-negative target certificates. A proved residual-force cone plus a
tangent parabola handles small axial turns; half-angle concavity handles large
turns. The two meet at pi/6, where the nonnegative dual multiplier vanishes.
The side-target proof switches by the actual transition-tangent force sign.

[F_INWARD_OPPOSITE_PROOF.md](F_INWARD_OPPOSITE_PROOF.md) explains the two-circle
comparison and its completed square. The resulting degree-11 polynomial is
strictly decreasing and positive at 5/8, so the twelve-entry Bernstein vector
is unnecessary. The expanded polynomial and one exact endpoint computation
remain, with their mathematical roles explained.

The other independent replacements are
[A_MARKER_CURVATURE_PROOF.md](A_MARKER_CURVATURE_PROOF.md),
[B_BOUNDARY_RATIO_PROOF.md](B_BOUNDARY_RATIO_PROOF.md),
[C_INWARD_TURN_PROOF.md](C_INWARD_TURN_PROOF.md), and
[D_OPPOSITE_FORWARD_PROOF.md](D_OPPOSITE_FORWARD_PROOF.md).
K now supplies quantitative curvature directly, so A is optional for the
combined marker-envelope integration.

## Production integration map

| Production target | Replacement | Interface note |
| --- | --- | --- |
| `MarkerArc.arcCurvaturePolynomial_pos` | A, or use K's direct quantitative envelope curvature | No Bernstein vector needed. |
| `MarkerArc.arcEnvelope_bound` | K | Replace internal `5443/10000` by sufficient `353/648`; update its local caller too. |
| `MarkerArc.marker_vertical_endpoint` | K plus the unchanged state-to-envelope comparison | Same 801/1600 marker half-width. |
| `LabelBoundary.J_bounds`, `transition_bounds`, `rd_bounds` consumers | L | Use sufficient coarse geometric statements, not the old narrow interval conclusions. |
| `BoundaryProfiles.transitionF_pos` | J | Same statement; stronger reserve 1/32000. |
| `BoundaryProfiles.diagonal_value_pos` | J's angle-order argument | Same statement; reserve 1/640. |
| `BoundaryProfiles.diagonal_angle_bounds` consumers | L | Use 3/5<angle<5/8; this preserves the circular-domain caller. |
| `Labels.side_selected_label_gt`, `side_selected_a_lt`, `axial_sum_lt` | M | All three original statements unchanged. |
| `TargetBoundaryMonotonicity.ratio_derivative_lt_one` | B | Same derivative inequality. |
| `TargetBoundaryMonotonicity.ratio_zero_lt` and initialization | N | Prefer the geometric tangent comparison; an exact proof of the original 51/200 helper is also given. |
| `InwardAxialTarget.inward_turn_profile` | C | Same trigonometric statement. |
| `OppositeForward.opposite_axial_scalar` | D | Same strict scalar statement. |
| `ForwardNegativeTarget.axial_target_support` | E1/E2 | Same complete turn domain. |
| `ForwardNegativeTarget.sideTarget_negative_pos` | E3 | Same strict z>0 domain. |
| `ForwardNegativeTarget.side_transition_trade` | L's coarse tangent reserve | Same statement, without tight state enclosures. |
| `InwardOppositeMinima.radialPolynomial_pos` | F | Same polynomial statement and positive-turn consumers. |

Do not try to prove a formerly tight helper's old numerical conclusion from a
weaker replacement enclosure. The notes explicitly say when only the consumer's
required geometry is preserved. There is no weakening of public packing or
classification statements.

## Principal second-pass reserves

These are consequences of the written proofs, not sampled minima.

| Item | Reserve / whole-domain estimate |
| --- | --- |
| J curvature | `transitionFDD > 5/8` on the entire circular profile interval |
| J diagonal endpoint | `F(td)>1/640`, `0<F'(td)<7/160` |
| J whole profile | `F(t)>1/32000` |
| J diagonal value | `diagonalValue>1/640`, by angle order |
| K envelope | `e(x)<=353/648-(x-2/9)^2/16` |
| K vertical marker | Final rational reserve `167/129600` using pi>157/50 |
| L side tangent | `Y0-(12/25)X0>1/100` |
| L diagonal window | `3/5<diagonalAngle<5/8` |
| M side-state exclusion | The comparison corner exceeds the disk radius squared by `1/1024` |
| N initial angle | Cleared comparison reduces to `7-4sqrt(3)>0` |

The stronger curvature in J is essential: simply moving the old, weaker
3/8-curvature argument to td is not justified. Likewise K changes its internal
envelope constant deliberately rather than claiming the old estimate.

## Remaining rational numbers

There are still large derived fractions in some expansions and endpoint
calculations. For example, J's 2351/3744 is the angle obtained from a specified
comparison corner; F retains the explicit degree-11 discriminant polynomial.
Neither is supplied as unexplained discovered data. The sign arguments are
geometric comparison, curvature, and monotonicity, with exact arithmetic at the
end. See SECOND_PASS_AUDIT for the retained-number inventory and explanations.

The original production five-/six-decimal constants remain physically present
because this research PR does not edit production files.

## Assembly and strictness

[G_BREAKPOINTS_AND_ASSEMBLY.md](G_BREAKPOINTS_AND_ASSEMBLY.md) documents the
other cutoffs and the fixed-gap/all-gaps assembly. The following remain:

```text
admissible states and markers
  -> separating-axis support inequalities
  -> the same strict fixed-gap sector statements
  -> marker gap at least pi/3, equality only at the same contacts
  -> six exterior markers form a regular hexagon
  -> contact-cycle and central-square rigidity
  -> the unchanged three-parameter column family.
```

Geometric sign/label boundaries and capped-triangle convexity are not numerical
search. E3 and F still require positive turn where needed; C still permits its
zero-turn equality. No contact case is accidentally excluded by extending a
strict inequality to a boundary where it is false.

## Verification and limits

The earlier notes record 52 exact cross-checks for A–G. This continuation ran
89 exact symbolic/rational checks for J–N/P, including derivative identities,
comparison domains, tangent squares, and positive reserves. All 89 passed.
These checks corroborate the displayed mathematical proofs and are not theorem
premises or replacements for those proofs.

The Lean blocks are proposed statements and implementation recipes, not
compiled proof bodies. The integrator should implement and compile one local
replacement at a time, avoiding circular use of the old target theorem, then
check elaborated dependencies and the unchanged public theorem statements.

Not performed here: production integration, Lean compilation, Comparator,
axiom audit, or independent kernel replay. Those remain maintainer tasks.
All commits in the second-pass completion use `[skip ci]`.
