# Roadmap to a draft Lean proof of the n=6 theorem

## Goal

Produce a draft Lean formalization of HAND_PROOF.md **after the audited mathematical repair gate below is closed**.

The draft does not need to compile. Its purpose is to settle final definitions,
module boundaries, theorem statements, dependency direction, scalar arithmetic
lemmas, and the equality chain. During this phase proof bodies may be
by sorry.

No theorem statement may depend on Python, interval boxes, certificate files,
or the former branch-and-bound verifier.

HAND_PROOF.md is the sole mathematical source of truth.

## Phase -1 — close the downstream audit and normalization theorem

Most defects found by the September downstream audit have explicit repairs in
HAND_PROOF.md.  One verification item remains before that gate is closed:
run one comprehensive exact direct-support audit over every non-hard A2.3
classification row using the corrected bookkeeping (the common half-width
constant counted once and the true cap/vertex switch).  Repair any row that
fails; only then promote (A23C0).

Independently, §2.3 of HAND_PROOF.md still requires the global n=6
normalization theorem from the N0 boundary, without importing any A2
conclusion.

Do not start the Lean draft until both tracks are closed.

### N0. Proven starting point

The normalization proof may assume only:

1. six unit squares form a packing with R^2 <= q_* < 13/4;
2. exactly one square C contains the disk centre O;
3. after translation/rotation, O=0 and C is axis-parallel;
4. the other five squares are exterior admissible Seven charts;
5. their genuine Seven markers are pairwise more than pi/3 apart;
6. their five cyclic successive marker gaps lie in (pi/3,2pi/3).

No A2 classification, fixed pin, side category, or 23/200 centre bound may
be used in proving normalization.

### N1. Rebuild the exact normalization checker from the correct boundary

Create a new exact checker whose state starts at N0, not at the old already-
normalized 17-dimensional box.

Suggested variables:

    Cx, Cy,
    (phase_i, a_i, b_i) for the five exterior SquareCharts.

Initial constraints may use only central containment, exteriority, candidate-
radius containment, pairwise separating-axis disjointness, the genuine Seven
marker definitions, and the marker-gap inequalities.

Do not seed it with any conclusion we are trying to prove: 23/200, the a/b
bounds, E/N/W/D/S sectors, fixed pins, or the central separator bit choices.

Use exact rational endpoints, rigorous Taylor/trigonometric enclosures, and
the exact separating-axis/support formulas from the archived fixed verifier.

Commit the checker skeleton before optimizing it.

### N2. Certify the central-core bound first

First target only

    |Cx|, |Cy| < 23/200.

Exhaust the complementary regions |Cx|>=23/200 or |Cy|>=23/200. Every
terminal box must carry a named reason: containment contradiction, unavoidable
overlap, marker-gap contradiction, or radial-sweep/support contradiction.

Then inspect the last residual boxes and extract a scalar hand theorem,
preferably an angular-budget inequality built from the existing APIs
`safe_openRay_of_disjoint`, `rayRegions_disjoint`, `SquareChart.edge_arc`,
`Seven.marker_arc`, and `Seven.all_gap_pos_below`.

Acceptance criterion: HAND_PROOF.md contains a direct proof of the 23/200
bound with only scalar endpoint inequalities at the leaves.

Commit immediately when the core bound is hand-closed.

### N3. Side-nearest theorem from the core bound

Using the core bound, prove for each exterior chart

    177/200 < a < 223/200,    |b| < 117/250 < 1/2.

Use candidate containment for upper bounds and central disjointness/core
geometry for the lower radial bound. Then prove that the closest point to O
is in the relative interior of the near edge, not at a corner.

Finally show that the Seven label is axial on this smaller domain, so after
restoring the chart sign the marker is

    phi_hat = phi + (5/4)b.

Acceptance criterion: no search remains after the core bound; only scalar
monotonic/rational inequalities.

Commit.

### N4. Derive sectors and the five fixed pins

Use the affine markers, their cyclic gaps, and the central frame to prove the
sector theorem. After a dihedral symmetry of C, the five primary directions
must occur in cyclic categories

    E, N, W, D, S.

Then prove the radius-9/10 pin inclusions at angles

    0, pi/2, 11pi/12, 5pi/4, 19pi/12.

Do this by substituting the sector/marker bounds into the chart membership
inequalities. A discovery checker may help locate endpoint inequalities, but
the final argument must list those scalar inequalities explicitly.

Acceptance criterion: the five pins are independent hand lemmas and imply the
moving-pin formulas already used later.

Commit.

### N5. Cap-piercing and one helper per side

Use the pins and core bound to prove moving piercing points such as

    P_E=(1+Cx,0),    P_N=(0,1+Cy)

lie in the respective exterior squares, and analogously for W/D/S whenever
a cardinal side is used.

Then prove: two distinct exterior squares cannot both occupy the same
cardinal side of C. Use true square disjointness, not bounding-box
disjointness.

Acceptance criterion: this theorem is proved before canonical bit patterns
are introduced.

Commit.

### N6. Central separator two-choice theorem

For each central/exterior pair, use separating-axis completeness. With the
core, side-nearest, sector and pin bounds, eliminate:

- the exterior secondary normal;
- the opposite exterior primary direction;
- the two wrong cardinal normals of C.

The only survivors are the matching cardinal normal of C and the exterior
square's own primary normal. Then impose the cardinal-preferred tie rule.

Acceptance criterion: the 2^5 central-pattern encoding is now a theorem, not
a verifier convention.

Commit.

### N7. Normalize D to own-primary

Use exactly two west-category helpers, their cyclic order, the one-helper-per-
side theorem, and horizontal reflection. Choose the labeling so that any
west-cardinal helper is W. Hence D is own-primary.

This is distinct from the invalid diagonal-reflection shortcut removed from
the survivor analysis.

Commit.

### N8. End-to-end normalization audit

Add a pattern-to-lemma table to HAND_PROOF.md:

| Output used later | Proven by |
|---|---|
| unique central square | N0 / Seven exterior theorem |
| central-core bound | N2 |
| side-nearest and a,b bounds | N3 |
| affine marker | N3 |
| E,N,W,D,S cyclic sectors | N4 |
| five open pins | N4 |
| one helper per side | N5 |
| central separator two-choice | N6 |
| D own-primary | N7 |
| marker gaps | N0 |

Then rerun the archived exact scalar checkers that consume these bounds.

The normalization theorem is closed only if every table row points to an
explicit proof, no checker assumes its own conclusion, no argument uses A2
circularly, and every checker failure is understood.

Commit the completed normalization theorem.

### N9. Final cleanup before Lean

Once N0--N8 are complete:

1. remove the audited-working-draft/open-normalization status;
2. state the unrestricted theorem as hand-complete;
3. remove stale research/checker prose from the mathematical proof;
4. squash the repair history again while preserving the checker archive;
5. request independent review of the resulting single hand proof.

Only after that begin Phase 0 below.

## Existing APIs to reuse

The current library already provides:

- SquaresInCircles/Geometry.lean: squares, packings, congruence;
- Common/Separation.lean: exact separating functional;
- Common/Support.lean: common support estimates;
- Common/Optimum.lean: the Optimum n package;
- Seven/: the proved exterior theorem used to force a central square.

Do not modify Challenge.lean, optimalRadius, optimalPackings, or the root
import file until the n=6 draft theorem chain exists.

## Proposed module tree

    SquaresInCircles/Six/
      Constants.lean
      Construction.lean
      Scalar.lean
      Support.lean
      Stress.lean
      Normalization.lean

      Pair/
        Basic.lean
        CardinalCardinal.lean
        OwnCardinal.lean
        OwnOwn.lean
        Diagonal.lean

      A2/
        Common.lean
        A21.lean
        A22.lean
        A23.lean
        Complete.lean

      Global/
        Symmetry.lean
        Pattern27.lean
        Pattern11.lean
        Pattern8.lean
        Coverage.lean

      Uniqueness.lean
      Optimum.lean

This is intentionally coarser than the discovery history. Do not create a
Lean file for every former stress/checker branch.

## Phase 0 — compile-shaped skeletons (only after Phase -1)

Create every file above with plausible imports, namespace
SquaresInCircles.Six, real definitions/theorem statements, and by sorry
bodies where necessary.

Milestone: a reviewer can navigate from Six.optimum down to every leaf lemma
without consulting research/six.

Commit this phase separately.

## Phase 1 — candidate constants and construction

### Constants.lean

Define

\[
h=1/\sqrt2,\qquad
A=(1466+1940h)/267,\qquad
B=(327+432h)/712,
\]

\[
s={2B\over A+\sqrt{A^2-4B}},\qquad
t=(-20+30h)s+7/2-9h/2,
\]

\[
d=1/2+h-t,\qquad
q_*=2s^2+4s+5/2,\qquad R_*=\sqrt{q_*},
\]

and

\[
\rho_*=\sqrt{q_*-1/4}-1/2.
\]

Draft interfaces:

    lemma h_pos : 0 < h := by sorry
    lemma s_bounds : (84 : ℝ)/1000 < s ∧ s < 85/1000 := by sorry
    lemma t_bounds : (420 : ℝ)/1000 < t ∧ t < 421/1000 := by sorry
    lemma d_bounds : (786 : ℝ)/1000 < d ∧ d < 787/1000 := by sorry

    lemma radius_sq_EN : qstar = ... := by sorry
    lemma radius_sq_WS : qstar = ... := by sorry
    lemma radius_sq_D  : qstar = ... := by sorry

    lemma radius_lt_17_10 : radius < 17/10 := by sorry
    lemma radius_gt_42_25 : 42/25 < radius := by sorry
    lemma rho_lt_9_8 : rho < 9/8 := by sorry

### Construction.lean

Define the six model squares and draft:

    def model : Fin 6 → UnitSquare := ...

    theorem model_packing : Packing model (0,0) radius := by sorry
    theorem model_reaches :
        ∃ i p, closedSquare (model i) p ∧ radius^2 ≤ normSq p := by sorry

Commit.

## Phase 2 — scalar arithmetic

### Scalar.lean

Formalize the finite rational trigonometric inequalities used repeatedly in
HAND_PROOF.md.

Examples:

    lemma cos_two_fifths_gt :
        (9:ℝ)/10 < Real.cos (2/5) := by sorry

    lemma sin_two_fifths_lt :
        Real.sin (2/5) < 2/5 := by sorry

    lemma cos_three_fifths_gt :
        (4:ℝ)/5 < Real.cos (3/5) := by sorry

    lemma cos_two_thirds_gt :
        (3:ℝ)/4 < Real.cos (2/3) := by sorry

    lemma sin_two_thirds_lt :
        Real.sin (2/3) < 5/8 := by sorry

    lemma sin_31_100_gt :
        (3:ℝ)/10 < Real.sin (31/100) := by sorry

    lemma sin_one_fifth_lt :
        Real.sin (1/5) < 5/17 := by sorry

Add named lemmas for every fixed endpoint inequality in Appendices A/B.

Do not formalize interval arithmetic. Prefer elementary Taylor estimates,
monotonicity, ring, nlinarith, positivity, and norm_num.

Milestone: every rational margin in HAND_PROOF.md has a theorem name.

Commit.

## Phase 3 — exact square-center support

### Support.lean

Extend Common/Support.lean with the exact disk-constrained center support

\[
U(x,y)
=\min\left(
 \rho\max(|x|,|y|),
 R\sqrt{x^2+y^2}-{ |x|+|y|\over2}
\right).
\]

Draft API:

    def centerSupport (R ρ x y : ℝ) : ℝ := ...

    lemma centerSupport_le_cap ... := by sorry
    lemma centerSupport_le_vertex ... := by sorry
    lemma centerSupport_eq_cap ... := by sorry
    lemma centerSupport_eq_vertex ... := by sorry

    lemma cap_vertex_value_match ... := by sorry
    lemma cap_vertex_derivative_match ... := by sorry
    lemma far_vertex_support ... := by sorry

Also expose central-square rectangular support and reflection/quarter-turn
invariance.

The wall-matching lemmas are important: later monotonicity and concavity
theorems should cross cap/vertex walls without reopening local cases.

Commit.

## Phase 4 — one generic reverse-stress theorem

### Stress.lean

Formalize the completed-square stress argument exactly once.

The theorem should accept containment weights, separator multipliers,
directed normals, induced forces, and support upper bounds and return the
reverse-stress lower bound used throughout the proof.

Conceptual draft:

    theorem reverse_stress
        (hweights : ...)
        (hsep : ...)
        (hsupport : ...) :
        qstar - R^2 ≤ stressDefect ... := by
      sorry

All A1, A2, and survivor stresses should instantiate this theorem. Avoid
encoding old row numbers or checker-specific data in the API.

Commit.

## Phase 5 — global normalization

### Normalization.lean

Define a normalized configuration structure containing only downstream data
actually used by the hand proof.

Tentative fields:

    structure Normalized where
      central : UnitSquare
      sq : OuterName → UnitSquare
      R : ℝ
      cx cy : ℝ
      e n w dAngle s : ℝ
      packing : ...
      centralBounds : ...
      sideNearest : ...
      cyclicOrder : ...
      pins : ...
      markerGaps : ...
      separatorChoice : ...

Draft theorem chain:

    theorem unique_central_square ... := by sorry
    theorem central_center_bound ... := by sorry
    theorem exterior_side_nearest ... := by sorry
    theorem cyclic_order ... := by sorry
    theorem five_open_pins ... := by sorry
    theorem marker_gap_bounds ... := by sorry
    theorem central_separator_two_choice ... := by sorry
    theorem cardinal_preferred ... := by sorry
    theorem at_most_one_cardinal_side ... := by sorry
    theorem normalize_D_own ... := by sorry

Gateway:

    theorem normalize
        {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
        (hp : Packing S o R)
        (hR : R^2 ≤ qstar) :
        ∃ P : Normalized, Represents P S o R := by
      sorry

Use the existing n=7 theorem directly.

Commit.

## Phase 6 — pair-factorized API

This is the highest-value abstraction layer.

### Pair/Basic.lean

Define the four source-axis choices and the pair terms

\[
A_u(n,w),\qquad B_v(e,s),
\]

plus the diagonal term

\[
D(w,s,\epsilon).
\]

### Pair/CardinalCardinal.lean

Formalize the Pattern-12 source reduction and envelope:

    theorem es_envelope
        (src : PairSource) :
        B src e s ≥ b s := by sorry

    theorem nw_envelope
        (src : PairSource) :
        A src n w ≥ b (-w) := by sorry

Derive the second by reflection.

Expose the scalar facts used by Pattern 8:

    lemma b_deriv_neg ... : deriv b x < 2/5 := by sorry
    lemma b_deriv_pos ... : 1 < deriv b x := by sorry

### Pair/OwnCardinal.lean

Package the Pattern-10 and Pattern-26 envelopes.

### Pair/OwnOwn.lean

Package the Pattern-14 reserves, especially

\[
A(n,w)\ge A_*+\frac{73}{100}(-w).
\]

### Pair/Diagonal.lean

Formalize D_cap, D_vert, their branch criteria, switch matching, and reusable
derivative bounds:

    lemma diagonal_dw_lt_four_fifths ...
    lemma diagonal_ds_lt_neg_half ...
    lemma diagonal_ds_gt_neg_nineteen_twentieths ...
    lemma diagonal_dw_gt_nine_twentieths_at_s_zero ...

Milestone: Pattern 8 can be stated using only pair APIs.

Commit.

## Phase 7 — draft Pattern 8 early

Formalize Pattern 8 before the full A2 case tree. It is now the cleanest
integration test for the abstraction boundaries.

### Global/Pattern8.lean

After importing the transferred Pattern-10 graph/tail theorem as an initial
placeholder, prove/draft

\[
\Phi\ge b(-w)+b(s)+D(w,s,\epsilon).
\]

Prefer endpoint-movement lemmas to a large general calculus framework:

    lemma F8_move_w_neg ... :
        F8 w s eps ≥ F8 0 s eps := by sorry

    lemma F8_move_s_neg ... :
        F8 w s eps ≥ F8 w 0 eps := by sorry

    lemma F8_move_s_pos ... :
        F8 w s eps ≥ F8 w 0 eps := by sorry

    lemma F8_move_w_pos_at_zero ... :
        F8 w 0 eps ≥ F8 0 0 eps := by sorry

Then:

    theorem F8_reduce :
        F8 w s eps ≥ F8 0 0 eps := by sorry

    lemma F8_zero :
        F8 0 0 eps =
          2*m*(d - 1/Real.sqrt 2)*(1-Real.cos eps) := by sorry

    theorem pattern8_lower_bound ... :
        qstar ≤ P.R^2 := by sorry

This phase should be used to revise the Support/Stress/Pair interfaces before
drafting all of A2.

Commit.

## Phase 8 — A2 as four modules

Do not reproduce the discovery chronology.

### A2/Common.lean

Common D-edge terminology, chamber definitions, reflection helpers, and
generic concavity-to-boundary lemmas.

### A2/A21.lean

Patterns 10, 14, 26:

    theorem exclude_pattern10 ... := by sorry
    theorem exclude_pattern14 ... := by sorry
    theorem exclude_pattern26 ... := by sorry

### A2/A22.lean

Patterns 12 and 13. Organize by final proof structure:

- nonnegative-W pair factorization;
- negative-W D-edge classification;
- candidate reserve.

### A2/A23.lean

Patterns 28--31 with the common D-edge classification and universal tails.

### A2/Complete.lean

    theorem forbidden_pattern_impossible
        (hpattern :
          P.pattern ∈ {10,12,13,14,26,28,29,30,31}) :
        False := by
      sorry

If useful, represent the central pattern by a finite type instead of raw
numerals.

Commit A21, A22, and A23 separately.

## Phase 9 — surviving patterns

### Global/Symmetry.lean

Define diagonal reflection of a normalized packing and its bit-pattern action.

    lemma reflect_pattern_9  : reflectPattern 9 = 10 := by decide
    lemma reflect_pattern_24 : reflectPattern 24 = 12 := by decide
    lemma reflect_pattern_25 : reflectPattern 25 = 14 := by decide
    lemma reflect_pattern_15 : reflectPattern 15 = 27 := by decide

### Global/Pattern27.lean

Transfer Pattern-26 graph/tail lemmas and formalize the E-own/S-own middle
reserve.

### Global/Pattern11.lean

Transfer Pattern-10 graph/tail lemmas, use the W-cardinal/S-cardinal bridge,
then force w=s=0.

### Global/Coverage.lean

Combine A2, symmetry, Pattern27, Pattern11, and Pattern8:

    theorem normalized_lower_bound
        (P : Normalized) :
        qstar ≤ P.R^2 := by
      sorry

Commit.

## Phase 10 — equality and Optimum

### Uniqueness.lean

Keep equality separate from the lower-bound theorem.

Trace strictness:

1. A2 patterns are impossible;
2. Patterns 11, 15, 27 are strict;
3. equality therefore lies in Pattern 8;
4. Pattern-8 movement inequalities force w=s=0;
5. pair-envelope equality forces n=e=0 and the equality source axes;
6. diagonal equality forces eps=0;
7. equality in the stress/containment identities fixes all centers.

Draft:

    theorem lower_bound
        (S : Fin 6 → UnitSquare) (o : Point) (R : ℝ)
        (hp : Packing S o R) :
        radius ≤ R := by
      sorry

    theorem congruent_of_optimal
        (S : Fin 6 → UnitSquare) (o : Point)
        (hp : Packing S o radius) :
        Congruent S o model := by
      sorry

### Optimum.lean

Finish in the existing library style:

    def optimum : Optimum 6 :=
      Optimum.ofUnique model
        model_packing
        model_reaches
        congruent_of_optimal

At this point the draft Lean proof is complete even if proofs still contain
sorry.

Do not integrate n=6 into the public root definitions yet.

Commit.

## Phase 11 — compile-driven formalization

Only after the draft theorem graph is stable:

1. compile Constants, Construction, Scalar;
2. compile Support and Stress;
3. compile Normalization;
4. compile Pair APIs;
5. compile Pattern 8;
6. compile A2 family-by-family;
7. compile surviving-pattern coverage;
8. compile Uniqueness and Optimum;
9. finally update public optimalRadius/optimalPackings, root imports, and
   Challenge.lean.

Pattern 8 should be the first serious analytic proof after the infrastructure:
it exercises the full path with minimal case branching.

## Draft-complete acceptance criteria

The roadmap phase is finished when:

- every proposed Six/*.lean file exists;
- important definitions have actual Lean syntax;
- every hand lemma in HAND_PROOF.md maps to a named Lean theorem;
- Six.optimum : Optimum 6 is present;
- proof bodies may contain sorry;
- no statement mentions Python, interval boxes, or certificates;
- lower-bound and equality chains are both explicit;
- public library integration remains intentionally deferred.

The first compilation pass should then be interface repair rather than
mathematical redesign.
