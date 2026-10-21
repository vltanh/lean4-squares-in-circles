# PR #10 — table-free Lean closure roadmap and progress ledger

**Checkpoint:** 2026-10-21 (UTC).  
**Repository:** `vltanh/lean4-squares-in-circles`.  
**PR:** [#10](https://github.com/vltanh/lean4-squares-in-circles/pull/10), draft, branch `formalize/eight-uncompiled-draft`, base `research/eight-proof`.  
**Source reference inspected:** `51094d7d6fd5e76d739334d5613727c5da17dfcf` (later fast-forward commits should be recorded below).  
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
| **G1 — Continuous frame + physical transport** | **DRAFT / integration PARTIAL** | `FrameAllPairs.lean` exports `continuous_pair_bound`; `FrameDiagonalOriginal.lean` transports all four original axes; `FramePhysicalTransport.lean` drafts source-radius lifts/variation. | Prove the actual boundary input gets the 7/10 spread, signed positive/negative variations and original selected weak axes **at its own radius**, with no generated pair table. Connect to normalization entry. |
| **G2 — Quarter word + wrong-word exclusions** | **PARTIAL** | `NearestAxisRecode.lean`, `EDiagonalExclusion.lean`; complete negative-three original-owner/cycle drafts; positive-three early/contact drafts; opposite-three **aligned** drafts. | Single original-cycle theorem excluding **every** noncanonical word with all four axes, both signs and all radial/frame types; finish positive-three and opposite-three unaligned/contact/cycle wrappers and combine existing word exclusions. No selected-axis substitution. |
| **G3 — Owner admissibility on original source** | **PARTIAL** | `NecessaryCycle.lean`, `SourceEquality.lean`, `StationarySourceOwners.lean`, `GlobalGASecondaryExclusion.lean` (specific original row), `FramePhysicalTransport.lean`. | Derive finite HG/GA/AB/BT/TD/DE/EH owner sets and zero-owner sign implications for **every** normalized source, including all weak ties and core/outer E choices. Produce one exhaustive source-owner classifier, not an expanding list of subclasses. |
| **G4 — Full same-radius G/T matrix** | **PARTIAL; central blocker** | `PositiveGABT2TD0Exclusion.lean` closes the specific positive-GA BT2/TD0 draft via `EDiagonalExclusion`; `GlobalGANonpositiveTD.lean`, `GlobalGAPositiveTDStress.lean`, `NegativePrimaryEntry.lean`, E-core/outer and one-/two-negative modules. | Expose one theorem dispatching **all** G/T primary signs and owner alternatives, both E signs/radial kinds, both T regimes, AB alternatives and negative/canceling routes. Every row either contradicts original q or reaches a sharp hard class with a loss ledger; include reflected T+ proof. |
| **G5 — Hard equality and strict loss** | **PARTIAL** | `CanonicalNegativeCycle.lean`, `CanonicalNegativeSharp.lean`, `LossLedger.lean`, hard endpoint modules. | Discharge every one of the **four** surviving G/T terminal cells (G0/T0, G−/T0, G0/T−, G−/T−). Equality at q* forces H/A/B/D/E **original** circles and stationary frames. A strict loss only on H/D (or another proved rigid anchor) excludes a moved descendant; never use loss only on free G/T. |
| **G6 — Recover untouched original source** | **OPEN; central blocker** | `OriginalWitnesses.lean`, `SourceEquality.lean`, `StationarySourceOwners.lean`, `SharpEntry.lean` describe the contract. | Prove GA0 and BT2 are **feasible on the initial unmoved source**, not just a transport descendant. Reapply the hard theorem there; establish initial selected normal equality and frame equality, including weak ties, without invoking the compatibility source entry. The proof must yield the `SharpSourceEntry` proposition. |
| **G7 — Replace compatibility capture** | **OPEN** | `TableFree/SharpEntry.lean` states `SharpSourceEntry`; `GeometricModel/SharpAssembly.lean` currently implements `compatibility_source_entry` through `Candidate.capture`. | Prove `SharpSourceEntry` from G1–G6, change `SharpAssembly` to use it, and remove `Candidate.capture` / generated owner-entry data from the unrestricted proof route. No reliance on old `Eight.Theorem`. |
| **G8 — Public theorem and equality** | **DRAFT; new table-free dependency OPEN** | `StatementEightGeometric.lean`, `GeometricModel/Theorem.lean`, `SharpAssembly.lean`, `SharpEquality.lean`, `EqualityFamily.lean`. | After G7, retain the pure five-corner minimum as `optimal_radius 8`, the full five-parameter equality family and unique least circle, with radius lower bound applied to the **original q** and original centers. No hidden rational bracket in the mathematical statement. |
| **G9 — Dependency closure and verification** | **DEFERRED** | Prior 20-Oct source report records generated modules in the then-public import closure; never infer table-freeness from local direct imports alone. | After complete uncompiled drafting: source audit, resolve import/API/sign mistakes, check no admissions and exact original hypotheses, prune generated closure, then (only when separately authorized) compile by standard Lean/Mathlib kernel, no native kernel/external scripts, optimize proof compilation and inspect elaborated axioms/dependencies. |

**Important distinction:** `PositiveGABT2TD0Exclusion.original_G_nonpos` is meaningful **DRAFT coverage of one full fixed-owner sector**. It is **not** the global G4 statement until every other original owner and reflected T sector is dispatched. Likewise `FrameAllPairs.continuous_pair_bound` is drafted but not a checked proof.

## Next work packages, in priority order

- [ ] **P1 — Finish G2 physical word classification.** Join positive-three and opposite-three **all-axis** contact families to the actual cycle word exclusions; include both opposite signs. Deliver a single word-selection theorem. Track all remaining finite words explicitly, rather than introducing sampled-angle tables.
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

For every further commit, record date/time UTC, new SHA, affected gate, exact new full-domain theorem, and whether it **closes the gate**, merely adds an uncompiled draft, or discovers a blocker. Update the gate row and checklist only when its stated exit condition is met. Use `[skip ci]` and keep PR #10 draft.

**Hand-off invariant:** the current public theorem is a concrete **compatibility-capture** draft, *not* the requested fully geometric/table-free Lean proof. The most important missing interface is a proof of `TableFree.SharpSourceEntry` for the untouched original source.
