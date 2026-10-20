# Geometric eight-square model: uncompiled Lean draft

## Delivery and verification boundary

This is the Lean source pass requested on 20 October 2026, after completion
of the geometric hand model. The user requested a draft of the complete
model and theorem, with **no compilation and no audit until the end**.
The implementation was written first. The final section records the limited
static audit performed only after the complete draft existed. The delivery
adds 26 Lean modules containing 5,561 lines, with public integration and
documentation alongside them.

No Lean command, lake command, CI job, generated certificate replay, or
kernel dependency/axiom inspection is part of this delivery. Proof bodies
are draft source and have not been accepted by Lean. The existing verified
results through seven squares are not evidence that this extension compiles.

The public entry point is
[`GeometricModel/Theorem.lean`](../../../SquaresInCircles/Eight/GeometricModel/Theorem.lean).
The pure statement is
[`StatementEightGeometric.lean`](../../../SquaresInCircles/StatementEightGeometric.lean).
The new statement replaces the eighth entry of
[`Optimal.lean`](../../../SquaresInCircles/Optimal.lean), and
[`SquaresInCircles.lean`](../../../SquaresInCircles.lean) uses the new geometric
`Optimum 8` directly. The old stationary statement and theorem names remain
available for compatibility.

## 1. The radius is a geometric minimum

`FiveCorner` contains an actual angle and five Euclidean points, ordered
`A, B, D, E, H`. Its `spans` predicate states

\[
\begin{aligned}
0\le t&\le\pi/4,\\
(B-A)_y&\ge2, & (B-D)_x&\ge3, & (D-E)_y&\ge2,\\
\langle f_t,E-H\rangle&\ge1+\sin t,
&\langle e_t,A-H\rangle&\ge2+\cos t.
\end{aligned}
\]

`fits d R` means `0 ≤ R` and `normSq (d.point i) ≤ R²` for every point.
`FiveCorner.radius` is the infimum of the radii for which such a chain
exists. `FiveCorner.selected` chooses a minimizing chain. Neither definition
contains the old rational radius bracket, a narrow coordinate window, a
stationary equation, or a generated certificate.

The proof modules establish the facts needed to justify those definitions:

- A feasible radius exists and the infimum is attained.
- The width-three span gives the structural bound `3/2 ≤ radius`.
- Arbitrary feasible points reduce to the full circle-chain domain.
- One support inequality excludes the high-tilt interval; the nominal
  polynomial stress supplies the small-angle localization.
- Position convexity and angular envelope geometry identify the minimum
  with the stationary construction.
- Positive force balance recovers the original five points at equality,
  proving uniqueness of the minimizer in the normalized frame.

The main exports are `FiveCorner.radius_eq_stationary`,
`radius_sq_eq_stationary`, `existsUnique_minimizer`, `selected_eq_canonical`,
`selected_spans`, `selected_fits`, and `radius_lt_two`.

## 2. The optional two-height coordinates are exact

The polynomial expression

\[
q(u,v)=\frac{(9+(u-v)^2)(9+(4-u-v)^2)}{36}
\]

eliminates both upper circle roots. The upper coordinates are

\[
U=\frac{9+(u-v)(4-u-v)}6,
\qquad
V=\frac{9-(u-v)(4-u-v)}6.
\]

The remaining lower coordinates are `sqrt (q-u²)` and `sqrt (q-v²)`.
`TwoHeights.InDomain` uses the natural conditions
`0 ≤ u`, `0 ≤ v`, `u² ≤ q`, `v² ≤ q`, `q < 4`, and
`0 ≤ angle ≤ π/4`. The positive upper coordinates follow from these
conditions and `U+V=3`; they are not additional numerical restrictions.

`TwoHeights.lean` drafts the polynomial identities, the equivalence between
the squared and square-root versions of the domain, the five-point chain,
and the exact scalar fifth-circle condition `defect ≤ 0`.
`TwoHeightMinimum.lean` connects this description to the full five-corner
problem below radius two and to the selected minimum.

## 3. Five geometric equality parameters

The new `Parameters` consists of the central square's `center : Point`,
its actual `angle : ℝ`, the top slider, and the tilted slider. Thus it has
five real coordinates. Its angle representative is half-open:
`-π/4 ≤ angle ∧ angle < π/4`.

The admissible domain states exactly:

1. The two moving exterior squares lie in the sharp disk, using the exact
   farthest-vertex function `containmentCost`.
2. The top square lies above the horizontal axis, and the tilted square
   lies below it, with weak contact permitted.
3. The origin lies in the open central square.
4. The central square is separated from each of the seven exterior squares,
   using the maximum of the four physical separating-axis projections.

The five anchor centers and the two contact lines are derived directly from
the minimizing corners. The 21 exterior pair separations are proved once
for the full wider rail domain. Central containment follows from its
interiority cost being less than two and the structural radius-square
bound being at least `9/4`. The seven central constraints then complete
all 28 pair separations.

The new domain is proved equivalent to the older exact chart. In the
geometric-to-old direction, the proof first constructs an actual packing,
then invokes the central-core theorem to recover the old narrower core
and rail inequalities. This order avoids putting those proof constants
back into the definition of the geometric model.

`EqualityAngles.lean` handles the actual-angle/half-angle inverse and the
physical quarter-turn equivalence. `EqualityEquivalence.lean` supplies
`Parameters.admissibleEquiv`. `EqualityFamily.lean` proves
`models_eq_stationary`, including both reflected families and all weak
contact endpoints.

The draft also gives a product box of five nondegenerate parameter intervals.
`Parameters.five_freedoms` states that this entire box packs the sharp disk,
and that two members are congruent under arbitrary Euclidean isometries
and square relabelings exactly when their parameters agree.

## 4. The containing circle is intrinsic

`EqualityCircle.lean` uses four actual boundary vertices with positive
convex weights whose weighted center is zero. The second-moment identity
gives the quantitative statement

\[
R_*^2+\|o\|^2\le r
\]

whenever every square in a model lies in the disk of squared radius `r`
centered at `o`. Thus the least containing circle has the stated center
and radius; its center is not a free choice hidden in the normalization.

The main exports are `Parameters.enclosing_radius_sq_bound`,
`Parameters.least_enclosing_radius`, and `Parameters.unique_least_circle`.

## 5. Exact-radius assembly uses the original packing

The unrestricted proof takes an arbitrary packing at its actual squared
radius `q`. If `q ≤ qStar`, it constructs the boundary reduction freshly
at `qStar`, while retaining the unchanged normalized packing at `q`.
The construction also retains equality of the initially selected signed
axes with the recovered boundary selection.

After conditional boundary equality identifies the physical frames and
selected normal directions, the dual is applied to the original centers
and original contact gaps. Its two inequalities are

\[
q_*+\sum_i\mu_i\|p_i-p_i^*\|^2
\;=\;D(p)\;\le\;q.
\]

The actual vertex bounds and nonnegative original gaps supply the upper
bound. Positivity gives `qStar ≤ q`, and under `q ≤ qStar` it fixes all five
anchors and all seven gaps. The two slider lines and the full equality
family are reconstructed only after that step.

The proof does not apply a lower working floor to the original `q`, assume
the original centers are boundary points, replace an originally selected
weak witness by a convenient new one, or assume radius equality in order
to prove radius equality.

Main exports include `fresh_normalization_with_retained_source_exists`,
`origin_sharp_rigidity`, `sharp_squared_radius_lower_bound`,
`sharp_radius_lower_bound`, and `sharp_uniqueness`.

## 6. Concrete proof route and retained dependencies

Every public lower-bound and classification statement has a concrete proof
body in this draft. They are not conditional on an unimplemented entry
assumption. The source entry currently used is explicitly named
`compatibility_source_entry`: it uses the repository's existing
`Candidate.capture` and conditional `Terminal.boundary_rigid` at the fresh
sharp ceiling. It does not import or call the older unrestricted theorem
in `Eight/Theorem.lean`.

This choice retains generated affine/owner capture dependencies and the
existing normalization and stationary-existence dependencies. The draft
does **not** claim that its complete Lean import closure is table-free.

The newer hand route through same-radius G/T endpoint transports and global
terminal exclusions is not yet fully transcribed as a replacement for
capture. `TableFree/EntryReduction.lean` separates the mathematical source
equality conclusion, its concrete compatibility proof, and that alternate
proof route. This is a remaining dependency-replacement task, rather than
an additional premise of the public theorem.

Concrete newly drafted parts of the hand route include the exhaustive
seven-row source classification, the reflected T classification, weak
zero-error owner ties, strict mixed-owner comparisons on actual source
squares, and physical-normal transport to the original packing.

## 7. Source map

Paths below are relative to `SquaresInCircles/Eight/`.

| Source | Responsibility |
|---|---|
| `GeometricModel/Basic.lean`, `SquareGeometry.lean` | Actual-angle frames, exact containment, physical SAT, quarter turns and reflection. |
| `GeometricModel/TwoHeights.lean`, `TwoHeightMinimum.lean` | Polynomial radius, natural-domain chain, and equivalence of minimization models. |
| `GeometricModel/FiveCornerReduction.lean` | Arbitrary-point capping and full-domain position convexity. |
| `GeometricModel/FiveCornerHighTilt.lean` | One high-tilt support, concavity and endpoint comparisons. |
| `GeometricModel/FiveCornerNominal.lean`, `FiveCornerNominalTrial.lean` | Nominal stress, scalar tails, exact trial and stationary ceiling. |
| `GeometricModel/FiveCornerSelection.lean` | Global radius comparison, attainment and original-point uniqueness. |
| `GeometricModel/EqualityModel.lean` | Re-export of the proof-independent geometric definitions. |
| `GeometricModel/EqualityAngles.lean` | Actual-angle representatives and exact chart conversion. |
| `GeometricModel/EqualityGeometry.lean` | Anchor/slider geometry, all exterior pairs and packing sufficiency. |
| `GeometricModel/EqualityEquivalence.lean` | Both domain directions and exact wider rail intervals. |
| `GeometricModel/EqualityCircle.lean` | Four-vertex second moment and unique least circle. |
| `GeometricModel/EqualityFamily.lean` | Model-set equality, attainment and five freedoms. |
| `GeometricModel/SharpOriginal.lean`, `SharpBoundary.lean` | Original dual at actual radius; fresh normalization and retained witnesses. |
| `GeometricModel/SharpAssembly.lean`, `SharpEquality.lean` | Concrete unrestricted lower bound and equality reconstruction. |
| `TableFree/OriginalWitnesses.lean` | Original vertices, contact gaps and physical-normal transport. |
| `TableFree/SourceEquality.lean`, `StationarySourceOwners.lean` | Source rows and actual mixed-owner pruning. |
| `TableFree/SharpEntry.lean`, `EntryReduction.lean` | Source-entry interfaces, concrete implementation and proof-route boundary. |
| `GeometricModel/Theorem.lean` | Geometric `Optimum 8`, least radius and full parameter classification. |

The pure definition mirror in `Challenge.lean` is materialized by
`python3 scripts/sync-challenge.py --write`, which copies source text and
never invokes Lean. Its two intentional challenge theorem placeholders
remain separate from the library proof source.

## 8. Public statements

With `SquaresInCircles.Eight.GeometricModel` open, the principal statements
are:

```lean
lower_bound (hp : Packing S o R) : FiveCorner.radius ≤ R

squared_radius_lower_bound (hp : SqPacking S o q) :
  FiveCorner.radius ^ 2 ≤ q

optimum : Optimum 8

isLeast :
  IsLeast {R | ∃ (S : Fin 8 → UnitSquare) (o : Point), Packing S o R}
    FiveCorner.radius

packing_iff (S : Fin 8 → UnitSquare) (o : Point) :
  Packing S o FiveCorner.radius ↔ ∃ M ∈ models, Congruent S o M

equality_iff_parameters (S : Fin 8 → UnitSquare) (o : Point) :
  Packing S o FiveCorner.radius ↔
    ∃ reflected : Bool, ∃ p : Parameters,
      p.Admissible FiveCorner.selected ∧
      Congruent S o (reflectedModel reflected p)
```

The root `optimal_radius`, `optimal_packings`, and `optimal_packings_rigid`
continue through `n = 8`, with the eighth case now using these geometric
definitions directly.

## 9. End-only static audit

The audit began after all source modules, public integration, and this report
had been drafted. Independent source reviews covered the five-corner and
two-height arguments, the complete equality family, and the pure/public
interfaces. The original-center and source-witness modules were checked
against the existing normalization, dual, and central-parameter APIs.

| Source-only check | Result |
|---|---|
| Repository imports | 351 project modules; no missing project import and no import cycle. |
| Pure geometric statement | Its repository import closure consists only of itself and `Geometry`. |
| New geometric theorem assembly | 246 project modules in its closure; the old unrestricted `Eight.Theorem` is absent. |
| Retained generated inputs | 108 modules with `.Generated.` in their names remain in that closure. This is a source inventory, not an elaborated dependency or execution report. |
| New proof-source admissions | No `sorry`, `admit`, `axiom`, or `unsafe` declaration token found outside comments in the 26 new Lean modules. The two pre-existing intentional Challenge theorem placeholders remain. |
| Independent statement mirror | The source-only `sync-challenge.py` comparison passes. |
| Documentation links | All 125 local links in the five edited documentation files resolve. |
| Whitespace | Tracked diff check passes; no trailing whitespace in the new Lean modules. |

The exact rational checks confirmed the nominal residual's zero constant
coefficient and ten positive nonconstant coefficients, both high-tilt
endpoint reserves, all five rational trial-circle reserves, and the GA/core
comparison reserves and radius-level relations used in the source adapters.
These were small rational calculations, not executions of the generated
certificate machinery or Lean proof bodies.

The review checked all 21 exterior separator orientations, both admissibility
directions, the half-open angle endpoints, the four-anchor barycenter and
second-moment identity, the absence of a lower cutoff for the original radius,
and preservation of the original weak signed witnesses. No mathematical gap
was identified by that review.

Concrete source repairs included the association of the four SAT alternatives,
explicit signed-axis arguments in physical-normal transport, the square-root
identity in the half-angle sine calculation, positivity hypotheses for the
four convex weights, exact projection-subtraction proofs for the tilted
spans, and robust handling of simplification that had already closed a goal.
No mathematical statement, admissible domain, or constant was weakened.

This remains an **uncompiled draft**. Source review does not establish
elaboration, tactic termination, kernel acceptance, certificate evaluation,
or the elaborated axiom/dependency closure. No Lean, lake, comparator, CI,
large certificate replay, or kernel inspection was run. Those checks remain
deferred exactly as requested.
