# PR #10 — table-free Lean source handoff (20 October 2026)

## Delivery state

**Branch:** `formalize/eight-uncompiled-draft` in [`vltanh/lean4-squares-in-circles`](https://github.com/vltanh/lean4-squares-in-circles/pull/10), stacked on `research/eight-proof`.

**Latest source-delivery commits:**

- [`794c8a2`](https://github.com/vltanh/lean4-squares-in-circles/commit/794c8a2048e660eac58fa48f2f1984e1f5d94928) — signed-coordinate and actual-circle foundations (first two modules).
- [`125f36e`](https://github.com/vltanh/lean4-squares-in-circles/commit/125f36e1fc00327dabf82cc9278d76f5aee2ce0f) — geometric/core/continuation/negative-primary part 1.
- [`a6a7d84`](https://github.com/vltanh/lean4-squares-in-circles/commit/a6a7d840fba709ad9ab8d20f7c698737bfc25a7f) — remaining endpoint, original-five-corner, and central replacements.

These commits preserve **31 draft Lean files**, **7,666 lines** and **360 textual `theorem` declarations**. The first two files had been pushed before the current handoff request; the remaining 29 are now pushed. Two files replace existing central modules, while the other 29 reside in `SquaresInCircles/Eight/TableFree/`.

The preceding geometric-model draft is already on the same PR (commit [`3f5ec9f`](https://github.com/vltanh/lean4-squares-in-circles/commit/3f5ec9f8161ac5a700edb8fd8e495f32abd44bef)); its separate [report](LEAN_GEOMETRIC_MODEL_DRAFT.md) describes the five-corner minimum, equality domain, and current public `Optimum 8` assembly.

**Status: source draft preserved, NOT a completed table-free formalization.** The newly written modules express local geometric transports and scalar certificates but are **not yet joined into an unrestricted table-free entry theorem**. The current public theorem still uses the historical compatibility path through `Candidate.capture` / `Terminal.boundary_rigid` and generated data. No claim is made that that path has been deleted or that the new Lean proof is checked.

## What the new draft contains

| Layer | Files | Mathematical content |
|---|---|---|
| Actual signed geometry | `SignedCoordinates`, `CircleGeometry`, `Variation`, `NecessaryCycle`, `LossLedger` | Signed own-frame coordinates, true core/actual outer circle, original feasible SAT normals, reflection and radial tags, separation of strict H/D circle loss from motion of G/T. |
| Intrinsic analytic tools | `TrigonometricReserves`, `EndpointPrinciples`, `ContactArcMinimum`, `ContactContinuation`, `AffineCircleEntry`, `PrimaryCap` | Whole-interval trigonometric bounds, contact-arc minima, derivative/continuation criteria, same-radius outerization and flat-core caps. |
| Positive primary and paired contact | `PrimaryPairReduction`, `PositivePairEndpoints`, `ZeroTangentPrimary`, `PairedPrimaryScalars`, `PairedPrimaryGeometry`, `PositivePrimaryNonpositiveTotal`, `WrongSignNonpositiveTotal` | Positive-sum and nonpositive-sum cases, aligned/diagonal/contact endpoints, simultaneous weak owners, and same-radius H/D reserves. |
| Genuine negative primary | `NegativeContactScalars`, `NegativeContactGeometry`, `FlatCoreNegativePrimary`, `FlatCoreCancelingPrimary`, `NegativePrimaryEntry`, `CancelingSupport` | Signed cancellation, negative GA with noncanceling/canceling transverse owners, actual-circle endpoint transports, and their strict anchor-loss ledgers. |
| Central geometry, replacing generated inputs | `Arithmetic/CentralBandPolynomials.lean`, `CentralSegment`, `CentralAngleCalculus`, `CentralScalarArithmetic`, `CentralForbiddenWidths`, `CentralForbidden.lean` | Continuous polynomial and forbidden-width proofs instead of the previous central band/rectangle-row data. The replacement `CentralForbidden.lean` reexports the new geometric theorems. |
| Direct original-center route | `OriginalFiveCorner` | Convert five *original* selected physical corners and seven retained gap inequalities into the five-corner geometric minimum; derive `R_* ≤ R` without applying the stationary force dual, and recover anchor/contact/sliding equality conditionally. |

The new local endpoint theorems preserve the actual squared-radius parameter `q` in constructed points; rational values such as `qLow` and `qCap` are only estimates/eligibility domains, not alternative circles. The source intentionally retains ordinary exact rational constants in some scalar estimates; “table-free” refers to replacing generated lookup tables with continuous geometric arguments, **not** banning rational proof estimates.

## Remaining mathematical and integration gates

1. **Make the source elaborate before believing any theorem.** The 360 declarations are written scripts only. The static inspection finds no textual `sorry`, `admit`, or `axiom` tokens, but this does not imply that tactic invocations, lemma names, coercions, signs, or imported Mathlib APIs succeed. No Lean command was used.
2. **Complete the global necessary-cycle interface.** Connect the actual `BoundaryCycle`/physical-axis capture to the `TableFree.NecessaryCycle.BoundaryInput` and preserve the *initially selected* original witnesses, including weak ties. Reflection must preserve the E-sign-independent positive-primary hypotheses.
3. **Prove exhaustive G/T primary-owner entry.** Combine positive-total, zero-total, genuine negative, canceling, and noncanceling pair transports at a single actual radius. Include all E radial/sign/secondary/paired-primary cases and all T owner regimes. No complete global owner matrix is yet exposed as a theorem in the new TableFree folder.
4. **Close hard-owner source recovery and original equality.** A transport descendant having GA0/BT2 does not show those axes were available at the untouched boundary source. Prove source equality and retained physical normals before applying the original-center chain. Never use a strict loss at free G/T as an equality contradiction; only H/D circle loss is rigid.
5. **Join the five-corner route to public statements.** The local `OriginalFiveCorner.radius_lower_bound` requires original physical frames and seven genuine nonnegative gaps. Establish them for arbitrary packings after an isometry/reflection, including the low-radius case. Then recover the geometric five-parameter equality domain and both reflected models.
6. **Remove compatibility/generated imports only after the replacement is complete.** The current public `GeometricModel/Theorem.lean` still invokes `Candidate.capture`. A source-only import inventory after integration should demonstrate that the new theorem closure no longer traverses generated affine/owner/adaptive table modules. Do not interpret the present local folder's lack of direct table imports as proof of this global property.
7. **Review the central replacements.** `CentralBandPolynomials.lean` and `CentralForbidden.lean` overwrite earlier modules. Check their exact exported declaration names and every downstream usage before replacing more generated files. The import-only `CentralForbidden.lean` intentionally obtains `bandA_forbidden` and `bandB_forbidden` through `TableFree/CentralForbiddenWidths.lean` in the original namespace.

### Recommended order

Preserve the current sources as-is and work bottom-up: signed geometry → single-radius circle estimates → endpoint/continuation lemmas → core and negative transports → complete positive/negative terminal matrix → boundary-source and original-axis recovery → original five-corner lower bound and equality → public theorem bridge → source dependency reduction → compilation/kernel/Palomar verification **only when separately authorized**.

For the hand mathematics consult [the full geometric theorem](HAND_UNRESTRICTED_EIGHT_SQUARE_THEOREM_WITHOUT_TABLES.md), [global owner entry](HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md), [original equality pullback](HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md), and [geometric family](EIGHT_SQUARE_GEOMETRIC_EQUALITY_MODEL.md). These are completed hand arguments; their translation into this new TableFree Lean package is incomplete.

## Verification and constraints

- **Not run:** Lean, lake, CI, certificate replay, comparator, axiom audit, native evaluation or external proof scripts.
- **Source-only check:** 31 local files; 7,666 source lines; 360 textual theorem declarations; no `sorry`/`admit`/`axiom` tokens; no missing imports *among the newly written `TableFree` modules* and no cycles in that new-only import graph. This is neither whole-repository import verification nor elaboration.
- **Do not claim:** compile success, formal theorem closure, removal of all generated inputs, Palomar-standard verification, or correctness of any unexecuted tactic proof.
- **PR policy:** `[skip ci]`, frequent commits, no forced ref updates; preserve all original mathematical hypotheses and sharp equality/weak-contact semantics. No native kernel or outside trusted scripts.

The primary deliverable of this handoff is the complete saved **source state**, with remaining proof gates visible and not silently assumed. The PR remains open as a draft.