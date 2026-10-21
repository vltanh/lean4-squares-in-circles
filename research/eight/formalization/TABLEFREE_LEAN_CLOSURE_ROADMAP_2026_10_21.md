# PR #10 — table-free Lean closure roadmap and progress ledger

The [live implementation roadmap](TABLE_FREE_FORMALIZATION_PROGRESS.md) records
later source checkpoints, exact remaining owner families, active assignments
and dependencies. This document retains the aggregate G0–G9 acceptance gates.

**Checkpoint:** 2026-10-21 (UTC).  
**Repository:** `vltanh/lean4-squares-in-circles`.  
**PR:** [#10](https://github.com/vltanh/lean4-squares-in-circles/pull/10), draft, branch `formalize/eight-uncompiled-draft`, base `research/eight-proof`.  
**Initial source reference:** `51094d7d6fd5e76d739334d5613727c5da17dfcf`; latest source checkpoint: [`c8247b6`](https://github.com/vltanh/lean4-squares-in-circles/commit/c8247b6f7f9ce48c724d2d6469ba0b203f34cea7), 2026-10-21 16:13:39 UTC.  
**Workflow:** Uncompiled Lean drafts, small `[skip ci]` commits, no Lean/lake/CI, no audit until the draft is complete. No native-kernel substitution or external trusted proof scripts.

## Status semantics and non-negotiable exit condition

- **HAND:** A complete hand argument is documented; this is **not** kernel verification.
- **DRAFT:** A concrete Lean proof body exists in the pushed source, but has **not** been elaborated or checked.
- **PARTIAL:** Some concrete Lean cases/bridges are drafted, but the **universally quantified target theorem** is not connected.
- **OPEN:** The stated unconditional Lean theorem/bridge has not been delivered.
- **DEFERRED:** Verification/cleanup that must follow the complete drafting pass, as authorized.

An individual subclass, sampled interval, favorable separating owner, generated local box, or shifted configuration **never** closes a gate. Close a gate only by exposing its advertised full-domain theorem over the **original packing** (or an explicitly proved equivalence), with weak owner ties, both signs, exact common radius, and equality information preserved where required.

**Overall:** hand-level global theorem documented; geometric public theorem drafted **using compatibility capture**; fully table-free unrestricted Lean proof **OPEN**. Never conflate these three claims.

## Dependency order

```text
G0 geometric five-corner minimizer/rigidity ────────────────────────┐
G1 continuous all-type pair inequalities → frame/variation capture ┤
G2 quarter word + all wrong-word physical owner exclusions ────────┤
G3 original-axis owner restrictions and signed normal cycle ───────┤
G4 full same-radius G/T primary-owner matrix (all E cases) ────────┤
G5 sharp hard terminal + strict ORIGINAL anchor-loss/equality ─────┤
G6 untouched source recovery + initial physical-normal equality ──┤
                                                                    ↓
G7 replace compatibility_source_entry / Candidate.capture
                                                                    ↓
G8 public lower bound, equality and five freedoms without generated route
                                                                    ↓
G9 import-dependency cleanup and deferred Lean/Palomar verification
```

G0 may be developed independently. G1–G3 provide **global** eligibility for G4; G4–G6 are the main logical blockers. G7 must not be declared done while the public import closure still uses `Candidate.capture`.

## Gate ledger (as of this checkpoint)

| Gate | Status | Current saved evidence | Precisely required for closure |
|---|---|---|---|
| **G0 — Geometric sharp datum** | **DRAFT** | `GeometricStationaryExistence.lean`, `FiveCornerNominalTrial.lean`, `CanonicalNegativeSharp.lean`, `StationaryCanonicalRigidity.lean`, `GeometricModel/FiveCornerSelection.lean` | Full stationary existence, minimum equality, all original five points and their circle equalities available to terminal proofs; no assumed local stationary box. Drafts exist; verify only in final authorized phase. |
| **G1 — Continuous frame + physical transport** | **DRAFT / integrated** | `GlobalNormalization.lean` obtains the genuine source-radius lift from `FramePhysicalTransport.quarter_lift`; `NormalizationBridge.lean` retains literal squares, strict spread, both variations and initial physical witnesses. | The continuous G1 data are connected to normalization without generated pair lookup. Word selection still uses the separate generated G2 route until its replacement is complete. Final verification remains deferred. |
| **G2 — Quarter word + wrong-word exclusions** | **PARTIAL** | Five complete second-word outer representatives; every upper opposite-three owner; lower inverse/contact data; `NearestAxisRecode.lean` and `EDiagonalExclusion.lean`. | Single original-cycle theorem excluding every noncanonical word with all weak axes, signs and radial types. Finish two opposite-three lower-secondary minima and all-owner cycle join, four zero-quarter outer families, mixed/core dispatch and both binary-word aggregates. |
| **G3 — Owner admissibility on original source** | **PARTIAL** | `GlobalZeroSignBridge.lean`, `GlobalQuarterSignCycle.lean` classify every original zero/quarter axis; D<0 and DE in {2,3} follow from E≤0. `GlobalGAPositiveTDExclusion.lean` closes the full secondary TD0/2 row. | Derive all remaining normal owner sets, radial anchors and signed primary-total alternatives for every normalized original source. The boundary bridge now derives zero-sign implications and D's sign; an unconditional owner classifier is still missing. |
| **G4 — Full same-radius G/T matrix** | **PARTIAL; central blocker** | `PositiveGABT2TD0Exclusion.lean` covers both E signs and its reflected positive-BT row; `PositiveGAOuterSoleReduction.lean` gives an actual sole-primary endpoint for every preprocessed T/E branch; negative and paired modules remain available. | Expose one theorem dispatching all primary signs, owner alternatives, E signs/radial kinds, T regimes and AB alternatives. Close remaining sole-E families and preserve exact q plus original rigid-anchor loss in every row. |
| **G5 — Hard equality and strict loss** | **PARTIAL** | `NonpositiveOuterSharp.lean` closes both nonpositive outer errors with arbitrary middle/E frames. `OrderedNormalSharp.lean` closes every ordered-normal owner/error case. `SignedOppositeHardSigns.lean` proves both larger-middle normal signs with unrestricted opposite sign. | Finish crossed outer/middle orders and small wrong intermediate signs, then expose the arbitrary hard-input theorem. Its sharp equality must retain all original rigid anchor circles and frames, with strict original H/D/A/B loss excluding moved descendants. |
| **G6 — Recover untouched original source** | **PARTIAL; unconditional entry OPEN** | `SourcePrimaryRecovery.lean` recovers original hard axes from source-aware paired contacts; `BoundarySourceRigidity.lean` joins original points and physical normals for the completed nonpositive class. | Extend recovery to every primary/terminal branch. GA0 and BT2 must be feasible at the initial unmoved source, then the full hard theorem must yield initial stationary frames and selected normal equality. The unconditional `SharpSourceEntry` is still open. |
| **G7 — Replace compatibility capture** | **OPEN** | `TableFree/SharpEntry.lean` states `SharpSourceEntry`; `GeometricModel/SharpAssembly.lean` currently implements `compatibility_source_entry` through `Candidate.capture`. | Prove `SharpSourceEntry` from G1–G6, change `SharpAssembly` to use it, and remove `Candidate.capture` / generated owner-entry data from the unrestricted proof route. No reliance on old `Eight.Theorem`. |
| **G8 — Public theorem and equality** | **DRAFT; new table-free dependency OPEN** | `StatementEightGeometric.lean`, `GeometricModel/Theorem.lean`, `SharpAssembly.lean`, `SharpEquality.lean`, `EqualityFamily.lean`. | After G7, retain the pure five-corner minimum as `optimal_radius 8`, the full five-parameter equality family and unique least circle, with radius lower bound applied to the **original q** and original centers. No hidden rational bracket in the mathematical statement. |
| **G9 — Dependency closure and verification** | **DEFERRED** | Prior 20-Oct source report records generated modules in the then-public import closure; never infer table-freeness from local direct imports alone. | After complete uncompiled drafting: source audit, resolve import/API/sign mistakes, check no admissions and exact original hypotheses, prune generated closure, then (only when separately authorized) compile by standard Lean/Mathlib kernel, no native kernel/external scripts, optimize proof compilation and inspect elaborated axioms/dependencies. |

**Important distinction:** `PositiveGABT2TD0Exclusion.original_G_nonpos` is meaningful **DRAFT coverage of one full fixed-owner sector**. It is **not** the global G4 statement until every other original owner and reflected T sector is dispatched. Likewise `FrameAllPairs.continuous_pair_bound` is drafted but not a checked proof.

## Next work packages, in priority order

- [ ] **P1 — Finish G2 physical word classification.** Positive-three and positive-negative-three now have all-original-axis cycle drafts. Finish opposite-three contact families, four zero-quarter outer families and mixed/core dispatch; join both actual binary-word exclusions. Deliver a single word-selection theorem. Track all remaining finite words explicitly, rather than introducing sampled-angle tables.
- [ ] **P2 — Finish G3 and G4 owner matrix.** Write a *finite source-state dispatch* from original normalized witnesses. Hook in positive-GA both T signs, core/outer and diagonal E, reflected positive-BT, GA2 secondary, aligned zero-owner, negative and canceling transport. Target: original cycle `→` hard terminal or strict rigid-anchor loss, at the same radius.
- [ ] **P3 — Terminal equality / source backtracking (G5–G6).** For each of the four terminal cells, retain source H/D loss. Prove **untouched-source GA0 and BT2 availability**, initial physical normals and stationary equality. This is the gate that prevents a local endpoint proof being mistaken for global sharpness.
- [ ] **P4 — Public entry swap (G7–G8).** Implement unconditional `SharpSourceEntry`; replace the compatibility proof in `SharpAssembly`. Recheck logically that original-center dual gives (q_* \le q), not just a bound for a displaced representative.
- [ ] **P5 — End-only verification (G9).** When drafting is fully assembled, perform the requested audit and (only on explicit new authorization) Lean compilation. Remove remaining generated dependency paths and optimize to Palomar-standard ordinary kernel proofs.

Parallel work is safe on **word-contact**, **GA/T stress/terminal**, and **source-recovery** modules. Do not edit the same branch/file concurrently without checking the live head. The public assembly should be edited **only after** P2–P3 provide the necessary exports.

## Closure checklist (unrestricted target)

- [x] Geometric hand theorem, five-corner minimum and equality family documented ([hand statement](HAND_UNRESTRICTED_EIGHT_SQUARE_THEOREM_WITHOUT_TABLES.md), [global hand entry](HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md), [original equality hand pullback](HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md)).
- [x] Initial table-free Lean source packages and subsequent per-sector drafts pushed.
- [ ] A full source-radius frame, variation and quarter-word theorem joined **without generated lookups**.
- [ ] Complete finite original-owner G/T classification and sharp terminal matrix, including E and all weak ties.
- [ ] Sharp original-source rigidity: untouched anchors, initially selected normals and loss ledger.
- [ ] Unconditional `SharpSourceEntry`, replacing `compatibility_source_entry`.
- [ ] Public `Optimum 8`/equality theorem derives through that new table-free path.
- [ ] The import closure contains no old generated capture/owner/affine-table route.
- [ ] Final requested audit and subsequently authorized kernel verification.

## Progress log and update protocol

| UTC date | Published checkpoint | What the event means |
|---|---|---|
| 2026-10-20 | `9d83bb7` and `HANDOFF_2026_10_20_TABLEFREE_LEAN_SOURCE.md` | 31 local uncompiled draft files preserved; **not** the global entry theorem. |
| 2026-10-21 | `109f171` | Original-point whole-variation GA one-angle support drafted. |
| 2026-10-21 | `c142d72` | All-pairs, GA-secondary, opposite-three and positive-three extensions visible remotely. |
| 2026-10-21 | `51094d7` (snapshot) | E-diagonal exclusion, original physical frame transport and new positive-TD/positive-three work visible. |
| 2026-10-21 | **This ledger** | G0–G9 statuses distinguished, with acceptance criteria; no Lean/CI/audit run. |
| 2026-10-21 | [`29e5884`](https://github.com/vltanh/lean4-squares-in-circles/commit/29e58841e1d79f4beca7ce105d0d869aac1250ed), [`4f5f2e3`](https://github.com/vltanh/lean4-squares-in-circles/commit/4f5f2e3dae8123c241910e15787002819c43724a) | PositiveThree and PositiveNegativeThree now have complete original-owner/reflection/physical/cycle drafts. Five of ten second-word outer representatives are drafted; G2 remains open. |
| 2026-10-21 | [`4d60885`](https://github.com/vltanh/lean4-squares-in-circles/commit/4d6088530750b38d034e7c63a7b030a3a0929bc4), [`332e321`](https://github.com/vltanh/lean4-squares-in-circles/commit/332e3216f979593ee901d967042b048b6734e4d1) | Positive-TD2 weights, coordinate bounds, low-angle endpoint reduction and four polynomial reserves drafted. Analytic scalar transfer, upper-angle envelope and the original-sector join remain. G3/G4 remain open. |

The [continuation checkpoint table](TABLE_FREE_FORMALIZATION_PROGRESS.md#8-continuation-checkpoints-through-1613-utc) records every subsequent source commit through 16:13:39 UTC, its affected gate and its precise scope. G1 is integrated; G2–G6 remain partial, G7–G8 remain open on the new route, and G9 stays deferred.

For every further commit, record date/time UTC, new SHA, affected gate, exact new full-domain theorem, and whether it **closes the gate**, merely adds an uncompiled draft, or discovers a blocker. Update the gate row and checklist only when its stated exit condition is met. Use `[skip ci]` and keep PR #10 draft.

**Hand-off invariant:** the current public theorem is a concrete **compatibility-capture** draft, *not* the requested fully geometric/table-free Lean proof. The most important missing interface is a proof of `TableFree.SharpSourceEntry` for the untouched original source.
