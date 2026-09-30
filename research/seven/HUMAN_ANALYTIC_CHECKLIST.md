# n=7 human-analytic proof checklist

## Scope and status

PR #8, branch `research/seven-human-analytic`.
Production baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.

**The mathematical research handoff is complete for all eight Bernstein sites.**
Each now has a written replacement proof, its exact domain and strictness
conditions, and a Lean integration recipe. None of the proposed replacements
needs a Bernstein coefficient vector.

This is not a claim that the production formalization has been changed or that
new Lean code has been compiled. Production integration belongs to the
maintainer. Read [HANDOFF.md](HANDOFF.md) for the replacement map and validation
boundary.

- [x] Keep this work under `research/seven/**`.
- [x] Leave production Lean, public statements, root files, general docs, CI,
      repository metadata, and other research subtrees unchanged.
- [x] Preserve the marker/contact/hexagon architecture.
- [x] Deliver mathematical proofs and proposed Lean helper statements/recipes.

## Acceptance criterion

The objective is to expose why the original geometric or analytic quantity has
the required sign. Exact rational constants are allowed when their roles and
inequalities are explicit. A long unexplained coefficient vector is not an
adequate primary explanation of a central inequality.

- [x] No external numerical success is a mathematical premise.
- [x] No exhaustive interval-box cover or generated stress table is introduced.
- [x] Domains, signs, denominator positivity and strictness are stated.
- [x] The proofs use whole-domain bounds, monotonicity, concavity, geometric
      support, or completed-square/factored identities.
- [x] Rational constants are tied to a support slope, derivative bound,
      endpoint enclosure, or explicit slack margin.
- [x] Exploratory verification is distinguished from the written proof.

## Completed replacement inventory

| ID | Original certificate | New reason for the sign | Proof |
| --- | --- | --- | --- |
| A | Marker-arc curvature, degree 8 / 9 coefficients | A factored bound on the radicand ratio, followed by a one-variable maximum at the derived critical point 3/5 | [A](A_MARKER_CURVATURE_PROOF.md) |
| B | Axial-boundary ratio, degree 5 / 6 coefficients | The numerator is concave throughout the radial enclosure; both endpoints are positive | [B](B_BOUNDARY_RATIO_PROOF.md) |
| C | Inward turn, degree 5 / 6 coefficients | A positive square plus factored Taylor error on [0,1], then a uniformly increasing trigonometric tail | [C](C_INWARD_TURN_PROOF.md) |
| D | Opposite-forward axial scalar, degree 5 / 6 coefficients | Cauchy–Schwarz bounds the derivative vector; the total possible decrease is smaller than the initial reserve | [D](D_OPPOSITE_FORWARD_PROOF.md) |
| E1 | Small axial target, degree 14 / 15 coefficients | The axial dual force lies in a proved cone; a linear disk-support bound and one tangent parabola give positive slack | [E, sections 1–4](E_FORWARD_TARGET_PROOF.md#1-axial-targets-the-statement-and-the-actual-support-switch) |
| E2 | Large axial target, degree 7 / 8 coefficients | The original half-angle support expression is concave, with exact positive endpoints | [E, section 5](E_FORWARD_TARGET_PROOF.md#5-large-axial-turns-half-angle-support-is-concave) |
| E3 | Negative side target, degree 6 / 7 coefficients | Split by the actual tangent-force sign; the remaining small regime has a simple cubic disk margin | [E, sections 6–9](E_FORWARD_TARGET_PROOF.md#6-side-targets-the-statement-and-transition-tangent) |
| F | Inward opposite discriminant, degree 11 / 12 coefficients | After the circle comparison and completed square, the polynomial is strictly decreasing and positive at 5/8 | [F](F_INWARD_OPPOSITE_PROOF.md) |

These were the eight sites carrying 69 displayed Bernstein coefficients in the
baseline. The proposed replacements prove the same statements; C, D, and E
work directly with the original trigonometric/support inequalities rather than
preserving unnecessary auxiliary polynomials.

## Readability audit, completed for A–F

- [x] State the original quantity before polynomialization.
- [x] State the exact continuous domain and its source.
- [x] Explain the reduction from geometry to the scalar inequality.
- [x] Give a visible reason for the sign, not a coefficient acceptance test.
- [x] Explain non-obvious constants and their explicit verification.
- [x] Preserve strictness and contact/equality boundaries.
- [x] Provide helper statements or a precise Lean implementation recipe.
- [x] Avoid circular use of the old positivity theorem in its replacement.

The large E and F items were not declared resolved merely because their
original coefficients were exact. E has new support arguments replacing all
three polynomial certificates. F retains its useful geometric quadratic and
polynomial interface, but replaces the opaque sign proof by a short derivative
comparison and one exact endpoint.

## Breakpoints audit

The complete audit and additional proofs are in
[G_BREAKPOINTS_AND_ASSEMBLY.md](G_BREAKPOINTS_AND_ASSEMBLY.md).

- [x] Remove the axial-target split at 1/3: the two support methods now meet at
      pi/6, where the nonnegative dual multiplier becomes zero.
- [x] Remove the negative side-target split at 1/6: use the sign of the force
      along the transition tangent. The small-angle bound is derived from
      that sign, not imposed as a new case partition.
- [x] Supply one monotone-profile proof replacing the inward side-target split
      at 2/3 and its accompanying pi/6 split.
- [x] Supply a replacement for the separate opposite-side/axial 1/3 cut: use the
      actual crossing of the two available affine clearance bounds.
- [x] Explain the forward-positive cutoff 5/16 and show it can be sharpened to
      3/10, the exact zero of its coarse support reserve.
- [x] Explain the retained 2/5 source-label cutoff by an explicit 1/1050
      marker-support reserve and the adjoining boundary-support domain.
- [x] Distinguish whole-domain enclosures from subdivisions.
- [x] Explain the new unit-interval split in C by its factored error and
      derivative-positive tail.
- [x] Retain geometric label transitions, sign walls, and genuine support
      switches. No fine mesh is introduced.

Not every rational endpoint is removed. The remaining ones have an explicit
mathematical function, and their validity is proved as an inequality rather
than inferred from numerical sampling.

## Fixed-gap, all-gaps, and equality handoff

- [x] Keep the four separating axes and two transverse signs exhaustive.
- [x] Keep the active axial/side labels.
- [x] Keep capped labels reduced by convexity to their triangle vertices.
- [x] Keep the marker-arc contradiction for small gaps.
- [x] Keep the continuous leftmost-minimum argument for larger gaps.
- [x] Check at source level that each replacement supplies the original
      sector statement with the required strictness.
- [x] Preserve the three contact types, regular hexagon, and column family.
- [x] Preserve the original Packing, Congruent and theorem statements.

The source-level map is documented in G/H and HANDOFF. It is not an elaborated
Lean dependency audit.

## Validation performed

- [x] Independently check the principal algebraic identities, derivative
      factorizations, and rational margins using exact symbolic/rational
      arithmetic: 52 checks passed.
- [x] Review the domain and sign conditions in the written arguments.
- [x] Check the named calculus helpers against the baseline
      `Seven/Analysis.lean`.
- [x] Keep mathematical proof, exact-arithmetic cross-check, and kernel
      acceptance distinct.

The exact checks are development cross-checks, not imported proof premises.
The complete mathematical arguments are written in the notes.

## Maintainer integration — not performed here

These items are deliberately not marked complete:

- [ ] Implement the proposed Lean helper statements and replacement bodies.
- [ ] Compile the research replacements against the pinned Lean/mathlib setup.
- [ ] Integrate selected changes into production modules.
- [ ] Check elaborated dependencies for accidental use of the old Bernstein
      results while establishing their replacements.
- [ ] Run the case and public theorem tests, axiom audit and independent replay.

No new compiled Lean proof is claimed. The deliverable is the completed human
proof research and integration handoff, confined to `research/seven/**`.
