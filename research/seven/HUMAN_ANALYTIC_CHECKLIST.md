# n=7 human-analytic proof checklist

## Scope and completion boundary

PR #8, branch `research/seven-human-analytic`.
Frozen production baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.

**The identified mathematical humanization tasks are complete:** all eight
Bernstein sites A–F and the second-pass numerical hotspots J–N now have written
human-proof replacements and integration recipes. This does not mean that the
production Lean has been changed, implemented or compiled.

Start with [HANDOFF.md](HANDOFF.md). The second-pass dependency and arithmetic
audit is [SECOND_PASS_AUDIT.md](SECOND_PASS_AUDIT.md).

- [x] Keep repository changes under `research/seven/**`.
- [x] Leave production Lean, public statements, general documentation, CI,
      repository metadata and other research subtrees unchanged.
- [x] Preserve the marker/contact/hexagon mathematical architecture.
- [x] Deliver proofs for a maintainer to integrate separately.
- [x] Use `[skip ci]` on every commit in the second-pass completion.

## Standard

The objective is a visible reason for every substantive inequality: geometric
support, monotonicity, curvature, a derived endpoint, or an explicit square.
Exact rational arithmetic is allowed; an opaque coefficient list is not the
primary explanation. Completion does not mean there are no large integers
anywhere in an expanded identity.

- [x] No external numerical success is a premise of a replacement proof.
- [x] No exhaustive angle-box partition or generated stress table is introduced.
- [x] Explain domains, signs, denominator positivity, and equality/strictness.
- [x] Keep geometric finite cases rather than replacing them with a mesh.
- [x] Distinguish a written proof, arithmetic cross-checks, and kernel acceptance.
- [x] Identify internal helper conclusions that change while their geometric
      callers retain their original statements.

## First pass — eight Bernstein sites

| ID | Old device | Human argument | Proof |
| --- | --- | --- | --- |
| A | Marker curvature: degree 8, nine coefficients | A radicand-ratio factorization and one derived maximum | [A](A_MARKER_CURVATURE_PROOF.md); [K](K_MARKER_ENVELOPE_PROOF.md) now supplies quantitative curvature as well |
| B | Boundary derivative ratio: degree 5, six coefficients | Concavity of its numerator and two endpoints | [B](B_BOUNDARY_RATIO_PROOF.md) |
| C | Inward turn: degree 5, six coefficients | Completed square, factored Taylor error and an increasing tail | [C](C_INWARD_TURN_PROOF.md) |
| D | Opposite-forward scalar: degree 5, six coefficients | Cauchy–Schwarz bounds the total possible decrease | [D](D_OPPOSITE_FORWARD_PROOF.md) |
| E1 | Small axial target: degree 14, fifteen coefficients | A residual-force cone and a tangent parabola | [E](E_FORWARD_TARGET_PROOF.md) |
| E2 | Large axial target: degree 7, eight coefficients | Half-angle support is concave | [E](E_FORWARD_TARGET_PROOF.md) |
| E3 | Negative side target: degree 6, seven coefficients | Transition-tangent force signs and a cubic disk margin | [E](E_FORWARD_TARGET_PROOF.md) |
| F | Inward-opposite discriminant: degree 11, twelve coefficients | Complete the geometric square; the polynomial is decreasing and positive at its endpoint | [F](F_INWARD_OPPOSITE_PROOF.md) |

- [x] Explain original quantities before polynomial expansion.
- [x] Provide a reason for positivity independent of a Bernstein vector.
- [x] Preserve contact/equality boundaries.
- [x] Avoid invoking the old theorem in its own replacement.

The first-pass 52 exact-arithmetic cross-checks remain documented in the
individual notes. These are not a substitute for formal compilation.

## J — transition-profile interior anchor — COMPLETE

Proof: [J_TRANSITION_ENDPOINT_PROOF.md](J_TRANSITION_ENDPOINT_PROOF.md).

- [x] Remove the numerically selected `testLabel=18/25` from the proposed proof.
- [x] Use the actual diagonal endpoint `td`, where `X/Z=12/13` exactly.
- [x] Strengthen the whole-domain curvature estimate to `F''>5/8`.
- [x] Keep the circle correlation while making a monotone endpoint comparison.
- [x] Prove `F(td)>1/640` and `0<F'(td)<7/160` by explicit endpoint arithmetic.
- [x] Complete the tangent parabola to obtain `F(t)>1/32000`.
- [x] Derive `diagonalValue>1/640` by angle order, removing its separate
      trigonometric bracket certificate.
- [x] Preserve `transitionF_pos` and `diagonal_value_pos` as statements.

The old test-value, test-slope and test-angle enclosure chains are unnecessary.
A short Taylor calculation at a derived comparison endpoint remains; its
origin and the needed value/slope reserve are explicit.

## K — quantitative marker envelope — COMPLETE

Proof: [K_MARKER_ENVELOPE_PROOF.md](K_MARKER_ENVELOPE_PROOF.md).

- [x] Remove the tangent at `x=1/8` and its six-digit radical/reciprocal brackets.
- [x] Prove uniform envelope curvature at most `-1/8` by a factored ratio bound.
- [x] Use exact origin data: `e(0)=13/24`, `e'(0)=1/36`.
- [x] Complete the parabola: `e(x)<=353/648-(x-2/9)^2/16`.
- [x] Preserve the original marker half-width `801/1600` with a positive
      rational reserve using only `pi>157/50`.
- [x] Explain the downstream `1/3200` perturbations as half the arc-width reserve.
- [x] Audit the remaining lower-marker constants as explicit Taylor and
      Cauchy–Schwarz arithmetic, not unexplained data.

Important: K supplies a sufficient new internal envelope bound `353/648`.
It does **not** claim the old bound `5443/10000`. The helper and its local
caller must be updated together; `marker_vertical_endpoint` is unchanged.

## L — tight transition/radical enclosures — COMPLETE

Proof: [L_COARSE_TRANSITION_PROOF.md](L_COARSE_TRANSITION_PROOF.md).

- [x] Select the intended circle/line intersection using coarse bounds only.
- [x] Use the monotone function `9sqrt(13/4-y^2)+11y` to locate it.
- [x] Derive coarse coordinate bounds without approximating J to five decimals.
- [x] Choose the upper transverse comparison point from the required
      `diagonalAngle<5/8` condition.
- [x] Establish `55/71<rd<31/40` by two explicit squared comparisons.
- [x] Prove `3/5<diagonalAngle<5/8` directly.
- [x] Trace tight-bound consumers and state sufficient replacements for each.
- [x] Replace the side-tangent's tight data by `Y0-(12/25)X0>1/100`.
- [x] Avoid circular dependence on the old `transition_coarse` proof.

The old five-decimal helper statements are not reproved or silently assumed.
Their consumers receive weaker, sufficient geometric bounds as documented in L.

## M — tuned state exclusions — COMPLETE

Proof: [M_STATE_SEPARATION_PROOF.md](M_STATE_SEPARATION_PROOF.md).

- [x] Prove `side_selected_label_gt` using the disk projection in direction (2,1).
- [x] Prove `side_selected_a_lt` with a constrained corner-distance contradiction,
      replacing the unexplained `2862/10000` square center.
- [x] Explain the corner used by `axial_sum_lt` from its sum threshold and tie line.
- [x] Preserve all three original strict conclusions and hypotheses.
- [x] Leave the already transparent `side_remainder_quadratic` argument intact.

## N — initial derivative ratio — COMPLETE

Proof: [N_INITIAL_RATIO_PROOF.md](N_INITIAL_RATIO_PROOF.md).

- [x] Replace the decimal enclosure of sqrt(3) by the geometric comparison
      `ratio(0)<tan(pi/12)`.
- [x] Show the cleared inequality is simply `7-4sqrt(3)>0`.
- [x] Initialize the monotonicity proof using the smallest possible angle.
- [x] Also supply a bracket-free proof of the unchanged `51/200` helper for
      integrators preferring that interface.

## Elementary constants and retained arithmetic

[P_ELEMENTARY_PI_BOUNDS.md](P_ELEMENTARY_PI_BOUNDS.md) derives the pi bounds
used by L from a rational tangent identity and short integral remainders.
This gives a human explanation independent of high-precision library witnesses.

- [x] Explain all newly introduced comparison points and margins.
- [x] Distinguish input constants from expanded outputs of exact arithmetic.
- [x] Record remaining large rationals and their roles in
      [SECOND_PASS_AUDIT.md](SECOND_PASS_AUDIT.md).
- [x] Do not claim that the expanded degree-11 coefficients or all large
      endpoint fractions disappear.

In particular, J's derived angle `2351/3744`, its endpoint arithmetic, and F's
expanded polynomial remain explicit. Their sign arguments are monotonicity,
curvature or completed squares, not acceptance of an unexplained coefficient
vector. Production still contains its original constants until integration.

## Breakpoints, assembly and equality

See [G_BREAKPOINTS_AND_ASSEMBLY.md](G_BREAKPOINTS_AND_ASSEMBLY.md) and the
updated dependency order in [SECOND_PASS_AUDIT.md](SECOND_PASS_AUDIT.md).

- [x] Replace the old axial-target `1/3` cut by the dual-force zero at pi/6.
- [x] Replace the negative side-target `1/6` cut by the actual tangent-force sign.
- [x] Supply a monotone profile replacing the inward side-target `2/3` split.
- [x] Derive the separate opposite-side/axial cutoff from crossing clearance bounds.
- [x] Explain/sharpen the forward-positive threshold and the retained `2/5` overlap.
- [x] Keep four-axis/sign/label cases and the capped triangle exhaustive.
- [x] Keep the small-gap marker argument and the continuous leftmost-minimum proof.
- [x] Preserve the same three contact types, regular hexagon and column family.
- [x] Keep the construction and public Packing/Congruent statements unchanged.

## Second-pass validation

- [x] Run 89 exact symbolic/rational checks covering J–N and P; all passed.
- [x] Check partial derivative identities and the signs used in the comparison domains.
- [x] Check the final positive reserves and internal helper-interface changes.
- [x] Distinguish source-level dependency review from elaborated Lean dependencies.

The checks corroborate the proofs; their success is not a premise. Completion
means the identified mathematical research tasks have solutions, not universal
agreement that every remaining calculation is short.

## Maintainer integration — NOT PERFORMED

- [ ] Implement the proposed Lean helper statements and proof bodies.
- [ ] Compile replacements against the pinned Lean/mathlib setup.
- [ ] Integrate selected changes into production modules.
- [ ] Check elaborated dependencies for accidental use of old target proofs.
- [ ] Run case tests, public theorem checks, Comparator, axiom audit and replay.

No new compiled Lean proof or production integration is claimed. These tasks
remain separate from the completed human-proof research handoff.
