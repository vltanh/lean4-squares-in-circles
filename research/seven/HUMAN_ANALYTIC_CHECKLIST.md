# n=7 human-analytic proof checklist

## Scope and status

PR #8, branch `research/seven-human-analytic`.
Production baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.

**The mathematical research handoff is complete for all eight Bernstein sites, but the broader human-readability audit is not complete.**
Each Bernstein site now has a written replacement proof, its exact domain and
strictness conditions, and a Lean integration recipe. None of those proposed
replacements needs a Bernstein coefficient vector.

A second-pass audit found additional computational-looking exact arithmetic
outside the Bernstein blocks: fixed interior anchor points, tight radical and
trigonometric brackets, and tuned quadratic certificates. These are now open
items below. The goal is to determine which are merely harmless arithmetic
closure and which still hide the mathematical reason for a bound.

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


## Second-pass audit — non-Bernstein numerical engineering

The Bernstein audit was not the end of the story. The following production
arguments are exact, but still look engineered enough that they should be
reviewed under the same human-readable standard.

### J — transition profile anchor in `BoundaryProfiles` — OPEN

The current transition-profile proof chooses the interior label

```text
testLabel = 18/25
```

and proves

```text
testValue > 1/10000
|testSlope| < 1/150
```

through tight rational enclosures of `D`, `Z`, `X`, `Y`, `Y0`, the
test angle, and the ratio `X/Z`.

Representative bounds include

```text
59525/100000 < D(testLabel) < 59527/100000
13545/10000  < Z(testLabel) < 13547/10000
13330/10000  < X(testLabel) < 13332/10000
6913/10000   < testAngle   < 6915/10000.
```

This is currently the strongest remaining certificate-like point outside the
old Bernstein blocks.

- [ ] Explain why `18/25` is chosen.
- [ ] Determine whether it is close to an actual minimizer or zero-slope point.
- [ ] Try to anchor the curvature argument at a structural point such as
      `s0`, `td`, or a derived critical point.
- [ ] Try to prove positivity from monotonicity/convexity and endpoint data
      without a hand-picked interior test point.
- [ ] If an interior anchor is genuinely simplest, derive it from an explicit
      optimization criterion and replace five-decimal brackets by coarser
      symbolic inequalities where possible.
- [ ] Revisit whether `testValue > 1/10000` and `|testSlope| < 1/150` are
      natural margins or merely arithmetic conveniences.

### K — quantitative marker-arc envelope — OPEN

The curvature certificate itself has a new human proof, but the later
`arcEnvelope_bound` still takes a tangent at `x=1/8` and uses tight
approximations such as

```text
992156/1000000 < sqrt(63/64) < 99216/100000
140867/100000  < sqrt(127/64) < 140868/100000
10079/10000    <= 1/sqrt(63/64) <= 100791/100000
2662/10000     <= (9/8)/(3 sqrt(127/64)) <= 26621/100000.
```

These establish

```text
arcEnvelope(1/8) <= pi/6 + 5430/10000
-1/100 <= arcEnvelope'(1/8) <= 0
arcEnvelope(x) <= pi/6 + 5443/10000.
```

- [ ] Explain or derive the tangent point `1/8`.
- [ ] Determine the true qualitative shape / location of the maximum of
      `arcEnvelope`.
- [ ] Try a direct maximum or derivative-zero argument.
- [ ] Try a tangent at a structurally defined point instead of a convenient
      rational point.
- [ ] Derive the amount of uniform marker slack actually required downstream.
- [ ] Re-express `801/1600 = 1/2 + 1/1600` as the required half-width plus
      explicit reserve.
- [x] Explain `1/3200`: it is half of the extra `1/1600` marker reserve and
      is used symmetrically at `0, +/-1/3200`; it is not numerical sampling.
- [ ] See whether a cleaner proof can give any explicit reserve
      `1/2 + epsilon` without six-digit square-root brackets.

### L — tight transition-state and radical enclosures — OPEN

The geometric definitions in `LabelBoundary` are meaningful, but the source
also carries very tight enclosures:

```text
1069547/100000 < J  < 1069549/100000
111979/100000  < a0 < 111980/100000
29136/100000   < u0 < 29137/100000
77475/100000   < rd < 77476/100000.
```

The coarse consequences are much more readable:

```text
11/10 < a0 < 9/8
29/100 < u0 < 3/10
9/25 < s0 < 2/5.
```

- [ ] Trace every use of the five-decimal enclosures.
- [ ] Remove any tight enclosure used only by J or K after those proofs are
      simplified.
- [ ] Prefer the exact circle/line identities and coarse rational bounds.
- [ ] Keep a tight enclosure only if a later human argument genuinely needs its
      precision, and explain that need.

### M — tuned state inequalities in `Labels` — OPEN

Several useful state lemmas have proofs containing constants that look
reverse-engineered rather than derived in the presentation.

Examples:

```text
side_selected_label_gt:
  332/225 - (44/45)t
  139744/50625 - (3232/2025)(t+9/25)

side_selected_a_lt:
  (u - 2862/10000)^2

axial_sum_lt:
  (a - 9/8)^2, (u - 23/80)^2.
```

The statements themselves are useful and plausible. The issue is whether the
proof makes the underlying constrained minimization visible.

- [ ] Re-derive `side_selected_label_gt` as a disk/line optimization or an
      explicit completed square with a derived center.
- [ ] Re-derive `side_selected_a_lt` without an unexplained decimal square
      center if possible.
- [ ] Re-express `axial_sum_lt` as a transparent tangent/support argument.
- [ ] Use `side_remainder_quadratic` as the style model: meaningful variables,
      exact identities, then an explicit nonnegative remainder.

### N — small remaining tight constants — OPEN / LOW PRIORITY

A few isolated tight constants remain outside the main hotspots, for example
`17321/10000` as an upper enclosure for `sqrt 3` in
`TargetBoundaryMonotonicity.ratio_zero_lt`.

- [ ] Replace isolated over-precise bounds by existing coarse bounds such as
      `1733/1000` whenever the proof still closes.
- [ ] Otherwise document why the extra digit is actually needed.

## Large-rational inventory

For this checklist, “large” means a rational with a long numerator or
denominator whose mathematical role is not immediately obvious. It is a
readability flag, not a formal defect.

### Still present in the production baseline outside Bernstein vectors

- **`Labels.lean`**:
  `139744/50625`, `3232/2025`, `2862/10000`.
- **`MarkerArc.lean`**:
  `1331/256000`, `2171/1200`,
  `992156/1000000`, `99216/100000`,
  `140867/100000`, `140868/100000`,
  `10079/10000`, `100791/100000`,
  `2662/10000`, `26621/100000`.
- **`LabelBoundary.lean`**:
  `1069547/100000`, `1069549/100000`,
  `111979/100000`, `111980/100000`,
  `29136/100000`, `29137/100000`,
  `77475/100000`, `77476/100000`.
- **`BoundaryProfiles.lean`**:
  `59525/100000`, `59527/100000`,
  `13545/10000`, `13547/10000`,
  `13330/10000`, `13332/10000`,
  `12138/10000`, `6913/10000`, `6915/10000`,
  `79136/100000`, `79137/100000`,
  `61979/100000`, `61980/100000`,
  plus the derived ratio bounds `13330/13547` and `13332/13545`.
- **`TargetBoundaryMonotonicity.lean`**:
  `17321/10000`.

The old production Bernstein vectors contain much larger rationals still, but
A--F already provide replacement proofs for those sites. They remain in the
repository only because production integration is intentionally out of scope
for this research PR.

### Files audited with no comparable large-rational concern

The construction, contact, marker-separation, separating-axis, uniqueness,
central-square, and contact-cycle modules contain only small structural
rationals such as `1/2`, `3/2`, `13/4`, and `2/15`.
`FixedGap`, `AllGaps`, and `SmoothMinima` are conceptually substantial but
do not rely on long rational certificates; their unusual small constants have
structural explanations or are now explicitly audited.

## Revised definition of done

The full human-readability audit is complete only when:

- [x] the eight Bernstein sites A--F have human-readable replacement proofs;
- [ ] J: the `18/25` transition-profile anchor is eliminated or derived
      conceptually;
- [ ] K: the marker-envelope tangent/bracketing calculation is simplified or
      its chosen point and reserve are conceptually derived;
- [ ] L: unnecessary five-decimal state/radical enclosures are removed;
- [ ] M: tuned state-lemma constants are derived from visible optimization or
      completed-square arguments;
- [ ] N: isolated over-precise constants are coarsened or justified;
- [ ] no remaining long rational is carrying the substantive mathematical idea
      without explanation.


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

No new compiled Lean proof is claimed. The Bernstein replacement handoff is
complete, while the broader second-pass readability audit J--N is now open.
All work remains confined to `research/seven/**`.
