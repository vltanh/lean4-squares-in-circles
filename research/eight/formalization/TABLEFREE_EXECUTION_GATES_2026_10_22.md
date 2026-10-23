# PR #10 — executable gate tree for the table-free eight-square hand proof

**Prepared:** 2026-10-22 (America/Chicago), against the live source branch `formalize/eight-uncompiled-draft`. **Target:** a new public Lean/Mathlib proof of the unrestricted n=8 sharp radius and full five-parameter equality classification, without using generated affine/owner capture. **Rule:** write and push faithful, uncompiled Lean first; audit and ordinary-kernel compilation only after source assembly, with separate authorization. [PR #10](https://github.com/vltanh/lean4-squares-in-circles/pull/10).

## 0. What “closed” means

Each item may have one of four independent states: **H** = hand argument documented; **D** = Lean source drafted with a proof body; **J** = imported into the actual end-to-end source theorem; **V** = ordinary Lean kernel verified. `H` or `D` never implies `J` or `V`. No `sorry`, new axioms, generated owner/word lookup or silently strengthened hypotheses. No premature percentage-complete estimates.

At each leaf, record (i) actual theorem name, (ii) initial and terminal hypotheses, (iii) whether the physical selected normal, source radius, original centers and weak ties are retained, (iv) the commit SHA and timestamp, and (v) whether it is source-only. Do not create new families of increasingly narrow cases unless their union is demonstrably exhaustive.

**Global acceptance:** a term of the unconditional `TableFree.SharpSourceEntry`, then a public theorem whose *transitive* import path does not use `Candidate.Capture` or its generated owner lookup, with the original radius, exact equality family and least-circle uniqueness. Standard-kernel verification is G9, not implied by a checked-in draft.

## 1. Foundational gates (G0–G2)

### G0 — Stationary sharp datum and complete equality family (D; verification pending)

- [x] **G0.1 — Exact sharp configuration and stationary equations, draft.**
  - [x] G0.1.1 Define the five corner anchors, two free intermediates, physical frame vectors and sharp squared radius, without decimal enclosure in theorem statements.
  - [x] G0.1.2 Give the complete positive dual balance and exact contact identities.
  - [x] G0.1.3 Transcribe existence and global five-anchor minimum/rigidity: `GeometricStationaryExistence`, `FiveCornerNominalTrial`, `StationaryCanonicalRigidity`.
- [x] **G0.2 — Original equality family, draft.**
  - [x] G0.2.1 Two zero slider forces and all contact equalities.
  - [x] G0.2.2 Necessary and sufficient five-parameter inequalities and converse.
  - [x] G0.2.3 Noncongruent open five-dimensional subfamily and unique least circle, source claims.
- [ ] **G0.3 — Exit:** trace the exact stationary statements to the final new imports, then kernel-check once G8 is joined. *Do not redo the stationary calculation as a new numeric search.*

### G1 — Original-radius boundary reduction and physical frame transport (D/J, unverified)

- [x] **G1.1 — Fresh original representative, draft:** fixed-witness recession at the *working* radius; never simply relabel old outer centers with a new ceiling.
  - [x] G1.1.1 Keep the original central-square packing and original seven selected physical normals.
  - [x] G1.1.2 Original sortedness, core avoidance, one-winding cycle, physical gaps.
- [x] **G1.2 — Continuous Q/Q0 support transfer, draft:** actual angle gaps, frame spread, signed errors, all actual radial kinds; `FramePhysicalTransport`.
  - [x] G1.2.1 Physical reflection/reversal and cyclic reindexing preserve selected normal projections.
  - [x] G1.2.2 Radius-level transfer between the outer word-classification ceiling and the original sharp ceiling retains its stated hypotheses.
- [x] **G1.3 — Normalization join drafted:** `GlobalNormalization` imports `TableFree.QuarterWordSelection`.
- [ ] **G1.4 — Exit:** check every imported source lemma in the end-only audit; no generated word-selection side route in the new public dependency closure.

### G2 — Seven quarter words to the candidate word (J at source level; V pending)

**Source inspection 22 October:** `QuarterDoubleExclusion.lean`, `ShortWordExclusion.lean`, `SecondWordExclusion.lean`, and `QuarterWordSelection.lean` form a complete *drafted* assembly. Historical ledgers calling the four zero-quarter and four mixed-quarter cases untouched are stale; inspect concrete source, not the older table.

- [x] **G2.1 — Exhaustive integer quarter-word classification, draft.**
  - [x] G2.1.1 All seven admissible dihedral representatives.
  - [x] G2.1.2 Four representatives with double increments excluded by continuous common edge costs.
  - [x] G2.1.3 Physical dihedral normalization of representatives, not an arbitrary frame change.
- [x] **G2.2 — Short binary wrong word, source join present.**
  - [x] G2.2.1 Original zero-quarter edge, both radial kinds and every weak witness.
  - [x] G2.2.2 Original outer/core quarter edge, reflected owners and signs.
  - [x] G2.2.3 Literal vertex markers telescope; strict total > 2π.
  - [x] G2.2.4 `ShortWord.not_dihedral`.
- [x] **G2.3 — Second binary wrong word, source join present.**
  - [x] G2.3.1 Outer–outer zero-quarter: four original sign/edge representatives with owner adapters.
  - [x] G2.3.2 Outer–outer quarter: six edge/sign representatives.
  - [x] G2.3.3 Mixed zero-quarter: both source/target radial directions, both signs.
  - [x] G2.3.4 Mixed quarter: all concrete families and original-owner physical wrappers.
  - [x] G2.3.5 Core–core edges and closed shared endpoints.
  - [x] G2.3.6 Same original marker on both incident edges; strict total > 2π; `SecondWord.not_dihedral`.
- [x] **G2.4 — Actual word exit drafted:** `TableFreeWordGeometry.quarter_word_candidate` excludes both wrong binary classes, then `GlobalNormalization.candidate_normalization_of_word` consumes it.
- [ ] **G2.5 — Exit:** kernel-check these source imports; confirm no indirect fallback to generated `Candidate.Capture` or unproved owner hypotheses. *No new case enumeration while the assembled source is present.*

## 2. Owner and terminal gates (G3–G5)

### G3 — Global original physical owner eligibility (D partially; J missing)

- [ ] **G3.1 — Canonical actual source and case-domain theorem.**
  - [ ] G3.1.1 From G1/G2 derive sorted outer H,A,B,D; E true-core or genuine outer at the same q; G,T either radial kind.
  - [ ] G3.1.2 Derive real-frame spread and both signed variations, including all weak/contact endpoints.
  - [ ] G3.1.3 Derive original zero-edge HG, TD signs as necessary consequences of the chosen original witnesses.
  - [ ] G3.1.4 Export a single source-domain constructor, with the original squares and actual q, *not* a transported copy.
- [ ] **G3.2 — Exhaustive retained owner classifier on the original cycle.**
  - [ ] G3.2.1 HG and TD allowed two zero owners, including ties, with their actual sign implications.
  - [ ] G3.2.2 GA, AB and BT primary/secondary quarter owners: both weak alternatives where geometrically possible, with sign restrictions.
  - [ ] G3.2.3 DE and EH owners for E core and E outer; all-high DE and diagonal/low alternatives.
  - [ ] G3.2.4 Produce a *single* statement collecting all seven actual physical witnesses and owner restrictions; do not assume a particular GA/EH/BT owner.
- [ ] **G3.3 — A/E signed primary preparation.**
  - [ ] G3.3.1 Exhaust whether selected A total is nonnegative or negative.
  - [ ] G3.3.2 Exhaust E nonnegative total, genuine negative EH1, genuine negative DE3, and boundary ties.
  - [ ] G3.3.3 Under negative A and/or E retain actual true-core eligibility and use the same-radius normal forms; track whether statements hold for source or only transported necessary cycles.
- [ ] **G3.4 — Exit:** one `BoundaryCycle` / `SignedCycle` theorem exposing complete allowed original owners, radial alternatives, sign and tie cases to G4; no generated lookup and no sector assumption disguised as universal.

### G4 — Complete finite G/T same-radius source matrix (D locally; J missing)

- [x] **G4.1 — Positive-BT3 scalar/source leaves drafted** (proof bodies exist; no compilation).
  - [x] G4.1.1 Nonnegative selected A/E totals, arbitrary signed TD0.
  - [x] G4.1.2 Negative flat A, nonnegative E; short and long E.
  - [x] G4.1.3 Joint negative flat A/E, arbitrary signed TD0.
  - [x] G4.1.4 Genuine negative DE3, nonnegative A, positive BT3: `GlobalGANegativeDEBT3Source`.
  - [x] G4.1.5 Genuine negative EH1, nonnegative A, positive BT3: `GlobalGANegativeEHBT3Source` / physical frame adapter (latest concurrent source commits). *All marked D, not verified.*
- [x] **G4.2 — Positive BT2/TD2 scalar/source leaves drafted** where concrete source file exists.
  - [x] G4.2.1 Nonnegative A/E selected totals and both TD2 signs.
  - [x] G4.2.2 Negative DE3, nonnegative A, positive TD2.
  - [x] G4.2.3 Negative EH1, nonnegative A, positive TD2, both small/far EH intervals: `GlobalGANegativeEHTD2Source`.
  - [x] G4.2.4 Negative A, negative E and mixed-sign descendants: stated-owner source packages, not a universal dispatcher.
- [ ] **G4.3 — Remaining nonpositive/zero T cases: global source join.**
  - [x] G4.3.1 Aligned genuine negative BT3 with zero TD endpoint can acquire actual BT2, conditional source draft.
  - [x] G4.3.2 `TTransport.reduce_complete`: resulting T pair has BT2 or positive BT3/TD0.
  - [ ] G4.3.3 Eliminate the latter *on the transported actual same-q cycle*, without assuming signs or owner choices absent from `SourceDomain`.
  - [x] G4.3.4 Export BT2 on a same-q necessary descendant via `TTransport.SecondaryResult`; source anchor preservation is stated and drafted. This is not yet a contradiction.
- [ ] **G4.4 — G-side owner/transport full join.**
  - [ ] G4.4.1 Original GA0 already available → preserve source.
  - [ ] G4.4.2 Positive total, wrong-sign nonpositive total, positive-GA nonpositive total: all reflected and zero cases.
  - [ ] G4.4.3 Negative flat-core GA1: canceling/noncanceling HG companions.
  - [ ] G4.4.4 At a hard endpoint retain strict HG slack or invariant positive total; non-hard endpoints classified G+/G-.
- [ ] **G4.5 — T-side reflected full join.**
  - [ ] G4.5.1 Original BT2 available → preserve source.
  - [ ] G4.5.2 Positive total, wrong sign, nonpositive total, TD0 sign: explicit true reflection including E data.
  - [ ] G4.5.3 Negative BT3 core / aligned cases, T+/T-/T0.
  - [ ] G4.5.4 At a hard endpoint retain strict TD slack or invariant positive total; preserve opposite G evidence.
- [ ] **G4.6 — Explicit finite terminal dispatcher** from G3 source. Partition by original A-sign × E-sign/type × G-primary × T-primary and both zero-owner alternatives. Discharge each cell by *actual source* theorem or a same-q transport, including every weak tie.
  - [ ] G4.6.1 No omitted simultaneous negative A/E or positive T case.
  - [ ] G4.6.2 Transported output's actual available owners derived, not asserted by selecting a hypothetical normal.
  - [ ] G4.6.3 Output is exactly one of hard G0/T0, positive G+/T+, negative G-/T-, and mixed terminal pairs, with original source evidence retained.
- [ ] **G4.7 — Exit:** a single `original_source_to_terminal`-style theorem with explicit original-q and original-witness invariants; *individual `...Source.actual_false` lemmas alone cannot close G4*.

### G5 — Sharp hard terminal and strict source-anchor loss (D conditional; J missing)

- [x] **G5.1 — Hard normal-owner sharp theorem drafted:** `UniversalHardSharp.HardInput.hard_sharp`, complete H/A/B/D/E anchors and actual contact equalities under `HardInput`.
- [ ] **G5.2 — Eliminate positive terminals from G4:** all E signs, both HG/TD owners, arbitrary signed errors; contradiction at q ≤ q*.
- [ ] **G5.3 — Eliminate genuine negative terminals:**
  - [ ] G5.3.1 G-/T0 yields strict *original H-anchor* circle loss before applying sharp hard theorem.
  - [ ] G5.3.2 G0/T- yields strict *original D-anchor* circle loss.
  - [ ] G5.3.3 G-/T- second conversion preserves the earlier strict H loss and adds strict D loss.
  - [ ] G5.3.4 Never substitute a moved G/T circle loss for loss at an unchanged anchor.
- [ ] **G5.4 — Exit:** only hard G0/T0 survives at q=q*, with the same original five anchor coordinates/frames. Emit enough retained data for G6, not just `q=qStar`.

## 3. Recovery and public theorem gates (G6–G9)

### G6 — Recover the *untouched* original source (D partial; J missing)

- [ ] **G6.1 — G original-hard-witness audit** (seven source rows in the hand equality pullback).
  - [ ] G6.1.1 Actual GA0 available: identity/no motion.
  - [ ] G6.1.2 Missing GA0 / positive total: impossible stationary frame invariant.
  - [ ] G6.1.3 Missing GA0 / nonpositive wrong sign or positive GA: strict original HG slack.
  - [ ] G6.1.4 Missing GA0 / negative flat-core, HG owner 0 or 2, canceling and noncanceling: strict surviving HG slack.
  - [ ] G6.1.5 Aligned genuine G- cannot be the final sharp hard terminal, via G5 anchor loss.
- [ ] **G6.2 — Reflected original BT2 audit:** all T rows, TD0/TD2 signs, matching strict TD slack and invariant positive total. No reflection error in E or original radius.
- [ ] **G6.3 — Independence:** changing G preserves T-side strict evidence; changing T preserves G-side evidence. The hard equality rigidities force the retained HG and TD slacks to zero, ruling out sources lacking original GA0 or BT2.
- [ ] **G6.4 — Reapply hard theorem to source itself:** derive stationary original H/A/B/D/E and original physical frames, without equating moved intermediates to ancestors.
- [ ] **G6.5 — Initially selected signed normals:**
  - [ ] G6.5.1 Every original choice belongs to the G3 allowed-owner sets, including ties.
  - [ ] G6.5.2 Prove original GA1 is strictly infeasible at the stationary data; retain source true-core bound.
  - [ ] G6.5.3 Prove original EH0 strictly infeasible by the exact mixed contact and signs.
  - [ ] G6.5.4 All remaining tied owners yield identical *physical* stationary normals at aligned frames.
- [ ] **G6.6 — Original-center dual and five freedoms:** all original anchor residuals and selected contact gaps vanish; original G/T sliders satisfy contact lines; original central square and pairwise separation yield the exact five-parameter domain and converse.
- [ ] **G6.7 — Exit:** a source theorem giving stationary frames, the original initially selected physical normal at *every* edge and stationary original anchor coordinates at q=q*, with weak ties; no compatibility-capture assumption.

### G7 — Unconditional sharp source entry (D/J source; V pending)

- [ ] G7.1 Instantiate `GlobalNormalization S qStar` and the actual source-domain theorem from G1–G3.
- [x] G7.2 Conditional assembly from normal owners is written in `NormalizedSourceEntry.original_hard_owners`, `original_sharp`, and `source_witnesses_of_normal_owners`; universal normal-owner eligibility remains unproved.
- [ ] G7.3 Construct **`TableFree.SharpSourceEntry`** *without an argument of type `SharpSourceEntry`*, `Candidate.capture`, a `sorry`, or an unstated original-owner premise.
- [ ] G7.4 Ensure `source_witnesses_of_recovered_equality` uses the unchanged source and initially retained normals.
- [ ] **G7 exit:** actual inhabitant of the proposition in `TableFree/SharpEntry.lean` under the exact `GlobalNormalization` hypotheses.

### G8 — Public sharp theorem and full equality (D/J source; V pending)

- [ ] G8.1 Replace `GeometricModel.SharpAssembly.compatibility_source_entry` with G7; remove `Candidate.Capture` from *all transitive public imports*.
- [ ] G8.2 Lower bound is for original arbitrary-radius packing: `qStar ≤ q` / `sqrt qStar ≤ R`, not merely a moved representative.
- [ ] G8.3 Equality gives original stationary physical frames and five original anchors; G/T exactly two slider coordinates.
- [ ] G8.4 Five-parameter weak necessary-and-sufficient domain, converse, noncongruent open family and unique least enclosing circle survive the new route.
- [ ] **G8 exit:** the requested unrestricted theorem and equality family exist as source terms with a demonstrably capture-free import graph.

### G9 — Final checking and repair (DEFERRED BY REQUEST)

- [ ] G9.1 One interface/sign/case-coverage audit of the *finished* uncompiled draft (not endless rolling audits); pay particular attention to q vs Q0/Q1, original vs transported axes, zero errors, radial endpoints and omitted nonneighbor inequalities.
- [ ] G9.2 Ordinary Lean/Mathlib kernel compilation of the public theorem, once separately authorized. Fix all actual elaboration errors, not just syntactic declarations.
- [ ] G9.3 Check no new axioms/admissions, no native-kernel trust shortcut, no external numeric checker and no hidden generated `Candidate.Capture` dependency.
- [ ] G9.4 Inspect proof term dependencies, equality converse, public API and practical compilation size; optimize only after verified proof exists.
- [ ] **G9 exit:** reproducibly kernel-checked public proof and complete equality theorem, with a final commit and reproducible provenance.

## 4. Execution order and stop rules

1. **Verify the source *already present* for G2 at the level of textual imports; do not redo eight representative families.** Its formal verification is G9.
2. **G3:** establish original owner/sign/radial admissibility in one object. Only prove a new leaf if a specific finite original-owner cell is genuinely uncovered.
3. **G4:** join the currently drafted signed A/E/BT2/BT3 subcases, then close T and G source terminals and the exhaustive matrix. This is the central exit gate.
4. **G5–G6:** prove original anchor-loss terminal join, invariant strict source obstruction, and original physical normal recovery.
5. **G7, G8:** instantiate `SharpSourceEntry`, swap the public imports, preserve exact optimality/equality.
6. **G9** only after an explicit request to validate/compile.

If a subgate cannot be completed, record **one exact missing hypothesis/theorem** and whether it is logically false, not simply “more scalar work needed.” Never call a collection of restricted-case source lemmas an unrestricted original-packing proof. Mark the PR as still open until G7/G8 are actually joined; no false “closure” statement for an uncompiled draft.

## 5. Concrete first source targets

- `SquaresInCircles/Eight/TableFree/GlobalGATransportTComplete.lean`: inspect `TTransport.CompleteResult` and eliminate its positive-BT3/TD0 alternative under the *actual* available hypotheses; if a global assumption is missing, expose it as a typed prerequisite instead of silently strengthening it.
- `SquaresInCircles/Eight/TableFree/GlobalGANegativeEHBT3Frame.lean` and `GlobalGANegativeDEBT3Source.lean`: consume their original frame contradictions in a finite G4 owner dispatcher, with correct E type/sign partition.
- `SquaresInCircles/Eight/TableFree/SourceEquality.lean`, `UniversalHardSharp.lean`, `SharpEntry.lean`: join strict source evidence, original normals and hard equality.
- `SquaresInCircles/Eight/GeometricModel/SharpAssembly.lean`: edit only after G7 is genuinely inhabited.

**Current source-level high-water mark:** G2 is assembled as a draft; positive-BT3/TD0 DE/EH local exclusions are drafted; the global G3–G6 dispatcher, unconditional G7, capture-free G8 and verified G9 remain open. Recheck live HEAD because concurrent source commits may supersede these observations.

## 5. Reconciled immediate blocker — one exhaustive BT2 theorem

**New commits 22 October:** `GlobalGAHighPositiveTFrame.lean` (`e75bc243`) closes the original physical positive-BT3/TD0 high-GA lane as source; `GlobalGAHighOwnerExit.lean` (`6956c16f`) connects T-to-BT2, original high-GA owner restriction and the conditional source-to-public proof. **It explicitly does not construct** `HighGABT2Exclusion`.

Thus the operative whole-domain target is exactly:

```lean
def HighGABT2Exclusion : Prop :=
  ∀ {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C),
    qLow ≤ q → q ≤ qCap → C.Feasible B 2 → False
```

Once an inhabitant is produced, `sharp_source_entry_of_BT2_exclusion` already drafts the rest of the original-normal-owner → same-radius hard-terminal → original-equality → `SharpSourceEntry` chain. The actual final source **must** supply the inhabitant; a conditional adapter is not closure.

### BT2.0 — Input conservation
- [ ] BT2.0.1 Original high GA and all six other originally selected axes belong to `SourceDomain`; H,G,B,D outer at actual q; E core/outer; weak ties allowed.
- [x] BT2.0.2 T-only reduction supplies actual BT2 at unchanged q with a *new* valid `SourceDomain` (`TTransport.reduce_secondary`, draft).
- [ ] BT2.0.3 No assumption that the transported T equals original T or that a changed E/A remains an actual initial packing.

### BT2.1 — TD owner exhaustive split
- [ ] BT2.1.1 TD0 selected: T primary total zero even when the individual BT/TD errors are not zero; handle arbitrary signed TD0 error.
- [ ] BT2.1.2 TD2 selected and its actual signed error ≤0: include zero as a weak tie and every E/A owner allocation.
- [ ] BT2.1.3 TD2 selected and its actual signed error >0: include positive-magnitude full range and all remaining A/E signs.

### BT2.2 — Exact A/E normal-form split inside *each* TD row
- [ ] BT2.2.1 E outer: choose its physically feasible secondary/nonnegative E total at the current same-q state; do not move E.
- [ ] BT2.2.2 E true-core: negative/zero/nonnegative selected total; if negative, normalized genuine DE3/EH1 primary with the other actual secondary.
- [ ] BT2.2.3 A selected total ≥0 vs <0; negative A normal form contains original GA3 or AB2 genuine primary, alternate secondary, and zero-boundary ties.
- [ ] BT2.2.4 A and E simultaneous negative: use joint-negative source, not separate one-negative theorems with incompatible premises.

### BT2.3 — Required finite source leaves
- [x] BT2.3.1 Nonnegative A/E selected totals with BT2 and TD0/TD2 source packages drafted (`GlobalGANonnegativeTotalsTD0Source`, `GlobalGANonnegativeTotalsNegativeTDSource`, `GlobalGANonnegativeTotalsSource`).
- [x] BT2.3.2 Negative E with nonpositive TD2 and nonnegative A source package drafted (`GlobalGANegativeENonpositiveTDSource`); check zero and outer-E joins in the final dispatcher.
- [x] BT2.3.3 Negative A/negative E with positive TD2 local sources drafted (`GlobalGAJointNegativeAETD2Source`); apply only after the actual A/E normal-form preservation lemmas.
- [x] BT2.3.4 Negative DE3 / EH1 with positive TD2, nonnegative A drafted (`GlobalGANegativeDETD2Source`, `GlobalGANegativeEHTD2Source`).
- [x] BT2.3.5 Negative E EH1 with BT2/TD0 high-A draft newly present (`GlobalGANegativeEHTD0Source`); **does not cover every A regime or E source unless separately joined**.
- [ ] BT2.3.6 Complete any genuinely missing cross-sign terminal, then connect every leaf to `SourceDomain` under original weak-owner hypotheses.

### BT2.4 — Whole-domain terminal / no uncaught case
- [ ] BT2.4.1 Construct one theorem dispatching BT2 + TD0 or TD2, two T error signs, three A-sign regimes and three E-sign/radial regimes with actual feasible owners.
- [ ] BT2.4.2 Prove every A/E transport retains the source-domain necessary constraints when reapplied; maintain original q and physical signs.
- [ ] BT2.4.3 Export **unconditional** `HighGABT2Exclusion`. If a branch is missing, name its exact input signature rather than claiming near-closure.

### BT2.5 — Rejoin finished modules
- [ ] BT2.5.1 `high_GA_source_false_of_BT2_exclusion` discharges all high-GA source records.
- [ ] BT2.5.2 `original_normal_owners_of_BT2_exclusion` yields every permitted original owner, including all ties.
- [ ] BT2.5.3 `sharp_source_entry_of_BT2_exclusion` gives an unconditional `SharpSourceEntry` when fed BT2.4.3.
- [ ] BT2.5.4 G8 public import swap follows; G9 deferred kernel verification still required.

**Execution priority:** finish BT2.3.5/BT2.3.6 and BT2.4 before any new local endpoint estimate. G4–G6 already possess a conditional normal-owner-to-original-equality assembly; do not redo that work.


## 6. Live execution ledger — 2026-10-22, current session

**Do not confuse a source lemma with an unconditional entry.** The BT2 negative-A case is being closed against the exact original source at the same working q. Kernel validation is still deferred to G9.

### BT2.3 negative-A refinement

- [x] **BT2.3.7 (D only)** Extract a radial-kind-independent *necessary-cycle* contradiction for one genuinely negative flat A primary, positive TD2, and **nonnegative selected E total**, with both short- and long-E charge ranges and both HG weak owners. The source takes the actually feasible DE/EH witnesses, not a transported re-creation of a packing. Lean theorem: `HighGABT2.negative_A_nonnegative_E_positive_TD2_false` in `GlobalGAHighBT2NegativeANonnegativeESource.lean`. Commit [`13ea96275`](https://github.com/vltanh/lean4-squares-in-circles/commit/13ea96275d03679a688fdaf19cf5035dffc96188), 2026-10-23T01:46:26Z. **Not imported into the whole-domain dispatcher yet; uncompiled.**
- [x] **BT2.3.8 (D only)** Apply BT2.3.7 to the E-first/A-second *core-E* normalized necessary cycle when `R.E_reduced` selects the nonnegative E branch. Derive actual A flat tangent cut by `NegativeA.GA_entry` or its AB analogue; handle secondary A re-selection instead of silently assuming a genuine primary. Draft `HighGABT2.negative_A_nonnegative_E_positive_TD2_false` in `GlobalGAHighBT2CoreEFirstNegativeNonnegativeE.lean`, commit [`34a4773e`](https://github.com/vltanh/lean4-squares-in-circles/commit/34a4773ed3623ca004dca7f6e1f7510ac512eaf6). Explicitly passes nonnegative selected E total and original BT2, TD2, HG and E owners to the short/long raw stress; no compilation.
- [x] **BT2.3.9 (D only)** For the E-first/A-second core-E **negative E** branch, extract the two genuine negative A/E primary magnitudes from `R.A.reduced` and `R.E_reduced`; derive the EH1 short angle (`s≤1/4`) either from the original E-first source or by EH0 secondary re-selection; feed `JointNegativeAETD2.original`. Preserve original q, H/D signs, T's signed error and both real selected witnesses.
- [x] **BT2.3.10 (D only)** Finish the core-E negative-A positive-TD2 dispatcher: nonnegative E → BT2.3.8; negative E → BT2.3.9, with all simultaneous weak owner alternatives.
- [x] **BT2.4.4 (D only)** Partition the remaining original negative-A sources by `I.radial E`: outer E uses `negative_A_outer_E_all_T_false`; core E must normalize **E first**, then A, and dispatch on `R.A.reduced`, T owner, and signed error.
- [ ] **BT2.4.5** Prove `HighGABT2Exclusion` itself, instantiate `sharp_source_entry_of_BT2_exclusion`, and swap the public dependency. None of these are finished as of this ledger entry.

**Invariant audit per new lemma:** original q unchanged; `SignedCycle` only after A motion; HG belongs to 0/2 on that same cycle; no hypothetical owner or radial kind is inserted; proof uses the exact signed E sum, not separate nonnegative error assumptions; zero ties remain in the short interval. H→D source anchors and original initially chosen normals are to be recovered at G6, not assumed here.


**2026-10-22 ledger checkpoint:** BT2.3.8 drafted at commit `34a4773e`; genuine negative E + negative A + positive TD2 (BT2.3.9) remains the first open source subgate. Core E-first full dispatcher and unconditional `HighGABT2Exclusion` remain open. This checkpoint is source-only, not a Lean check.

### 2026-10-22 source-draft closure checkpoint

- [x] **BT2.3.9 (D)** Joint genuine A/E negative positive-TD2 source theorem: `GlobalGAHighBT2CoreEFirstJointNegative.lean`, commit [`dfe7be58`](https://github.com/vltanh/lean4-squares-in-circles/commit/dfe7be58e2e852fb0c77373280a90a50e0857437). Actual DE3 or EH1, short EH1 bound obtained by genuine-entry geometry if EH0 is infeasible, or by real same-state EH0 secondary re-selection if feasible. Both negative A locations handled; H/B/D/T untouched. No physical packing reconstructed from moved A.
- [x] **BT2.3.10 (D)** Core E-first/A-second all-T and all-A-sign dispatcher: `GlobalGAHighBT2CoreEFirstAllT.lean`, commit [`9a95c1f1`](https://github.com/vltanh/lean4-squares-in-circles/commit/9a95c1f1ce23eabf0f1c12813709b98e29f3a1fa). Covers TD0, nonpositive signed TD2, strictly positive signed TD2 and ties; E and A normal forms both three-way exhaustive.
- [x] **BT2.4.4 (D)** Outer/core original E split: `GlobalGAHighBT2Complete.high_GA_BT2_exclusion` proves `HighGABT2Exclusion` directly, commit [`304501f6`](https://github.com/vltanh/lean4-squares-in-circles/commit/304501f64c52971ca4c4470b5d293adc4e68e9d7).
- [x] **G7 (D only)** `GlobalGAHighSourceComplete.table_free_sharp_source_entry : SharpSourceEntry` has no uninhabited input; it combines the G4 BT2 source proof with G/T source recovery and initial selected-normal equality. Commit [`d89955c7`](https://github.com/vltanh/lean4-squares-in-circles/commit/d89955c703a5b187554314dc1ec0c6f4c4506642). This establishes a *drafted Lean proof body*, not a compiled theorem.
- [x] **Source-level naming fix (D)** The generic signed-E stress and core-E application had accidentally shared a theorem name. The raw one is now `negative_A_nonnegative_E_positive_TD2_raw_false`, the core adapter is `negative_A_nonnegative_E_positive_TD2_false` (commit [`a9a0d973`](https://github.com/vltanh/lean4-squares-in-circles/commit/a9a0d9737307903dd457c1572df6461e3715b048)).

**First remaining source gate:** G8 public import replacement. Then G9: ordinary Lean elaboration, exact dependency check, and kernel verification. Do not call the PR verified/merged while this is uncompiled. Record each follow-up SHA/time and any concrete unsupported premise. Never restore the generated `Candidate.Capture` dependency as a convenient fallback.


## 7. Public G7/G8 source completion (D/J only), 2026-10-22

**This is not Lean kernel verification.** The source now has proof bodies with the original arguments and has been connected to the public n=8 geometric theorem. The new source is to be audited and then compiled *only when separately authorized*. No CI has run.

- [x] **BT2.3.9, source-only** joint genuine negative A/E + positive TD2: `GlobalGAHighBT2CoreEFirstJointNegative.lean`, commit [`dfe7be58`](https://github.com/vltanh/lean4-squares-in-circles/commit/dfe7be58e2e852fb0c77373280a90a50e0857437). The genuine EH1 short-angle cut is obtained from original E-first geometry or a feasible EH0 secondary on the same necessary cycle.
- [x] **BT2.3.10, source-only** true-core E-first/A-second normalized all-T dispatch: `core_E_all_T_false`, commit [`9a95c1f1`](https://github.com/vltanh/lean4-squares-in-circles/commit/9a95c1f1ce23eabf0f1c12813709b98e29f3a1fa).
- [x] **BT2.4 and G4, source-only** `high_GA_BT2_exclusion : HighGABT2Exclusion` handles original E outer or true-core, all A and T signs/weak owners, commit [`304501f6`](https://github.com/vltanh/lean4-squares-in-circles/commit/304501f64c52971ca4c4470b5d293adc4e68e9d7).
- [x] **G7.1–G7.4, D/J only** `table_free_sharp_source_entry : SharpSourceEntry` is an unconditional proof body in `GlobalGAHighSourceComplete.lean`, commit [`d89955c7`](https://github.com/vltanh/lean4-squares-in-circles/commit/d89955c703a5b187554314dc1ec0c6f4c4506642). Its original selected-normal and frame conclusions are inherited from source recovery. No new axiom/admission declared.
- [x] **G8.1, D/J only** replace `Candidate.capture` in `GeometricModel.SharpAssembly`, call `table_free_original_rigidity` at the unchanged q, commit [`739d9428`](https://github.com/vltanh/lean4-squares-in-circles/commit/739d9428c84a25ce60afeb65e308f94a9b8a470b). The old capture route remains in a separate historical legacy module.
- [x] **G8.2–G8.4, D/J only** `GeometricModel.Theorem` consumes new `SharpEquality` and `SharpAssembly` for squared-radius lower bound, five-parameter equality family and full rigid uniqueness. `SquaresInCircles.lean` no longer imports the legacy `Eight.Theorem`, commit [`e542f7ae`](https://github.com/vltanh/lean4-squares-in-circles/commit/e542f7aeee45b4f6e8f8919b1ddf3ceca3fcd062).
- [x] **G8.EntryReduction repair, D/J only** rewrite obsolete `via_capture` users in `TableFree.EntryReduction.lean` as `recovered_source_entry_table_free` and `fresh_sharp_entry_table_free`, commit [`b57bc3ca`](https://github.com/vltanh/lean4-squares-in-circles/commit/b57bc3ca42b5b1847fab92daf353fdda639eec69).
- [x] **Canonical handoff refreshed** [`TABLEFREE_HANDOFF_CURRENT.md`](TABLEFREE_HANDOFF_CURRENT.md), commit [`cc2f0935`](https://github.com/vltanh/lean4-squares-in-circles/commit/cc2f093553882ec11d6243611afdba341e171866).
- [ ] **G9.1 transitive source/interface import audit**: inspect the complete public graph, stale compatibility references and all owner/sign endpoints; record and correct any exact source mismatch. No kernel claims.
- [ ] **G9.2 standard Lean/Mathlib compilation and repair (separate authorization required)**: no `sorry`, native kernel, generated owner lookup or new axioms.
- [ ] **G9.3/G9.4 trusted axiom and performance validation**: `AxiomAudit.lean` now stages `#print axioms` commands but has not been executed.

**Exit criterion is unchanged:** the PR must remain unverified until ordinary Lean confirms the new public theorem and exact equality family, including no `Candidate.Capture` in the transitive new proof route. D/J source progress is not V.

## 8. G9 source-only static audit progress — 2026-10-22

**Method:** read code via the GitHub connector; no Lean, Mathlib build, lake, tests, CI, axiom inspection or generated checker executed. This can expose stale names/direct imports, but it CANNOT certify elaboration or mathematical soundness.

- [x] **G9.1.a (textual, not kernel)** inspected the eight new high-GA source/bridge modules and five public-path modules. Found no visible source `sorry`, explicit new `axiom`, `native_decide`, `Candidate.capture` call or deleted `compatibility_source_entry` call in those thirteen code bodies. This does not quantify over every transitive module.
- [x] **G9.1.b (textual repair)** `GlobalGAHighBT2CoreEFirstNegativeNonnegativeE.lean` mistakenly qualified `ActualCoreEBlocks` as `GlobalGA.ActualCoreEBlocks`; actual source is `SquaresInCircles.Eight.TableFree.ActualCoreEBlocks`. Fixed 14 occurrences at commit [`e66ac312`](https://github.com/vltanh/lean4-squares-in-circles/commit/e66ac31253dd62bd7a264640d462851335063146). **Not elaborated**.
- [x] **G9.1.c (textual repair)** restore two old independent frame lemmas in the capture-free `GeometricModel.SharpAssembly` to avoid needless API breakage, commit [`760e6728`](https://github.com/vltanh/lean4-squares-in-circles/commit/760e672835c0d8f9763fdafb46dd9e8124061d14). No capture proof restored.
- [x] **G9.1.d (textual repair)** `GlobalGAHighSourceComplete` now opens the exact geometry/co-ordinate namespaces for `sharpData`, `OriginalDual` and original radius API, commit [`9abfad8f`](https://github.com/vltanh/lean4-squares-in-circles/commit/9abfad8f591752699d2c17ba5b0e734ad332f16c). **Not elaborated**.
- [x] **G9.1.e (limited import chain)** examined direct imports through the new `GeometricModel.Theorem` and initial G4 source paths, to a bounded depth. The sampled edges do not reach `Candidate.Capture` or legacy `Eight.Theorem`; exhaustive transitive capture-free import check remains **OPEN**.
- [x] **G9.1.f (important qualification)** a transitive public dependency still imports `SquaresInCircles/Eight/ExactFamily/Generated/EqualityBox.lean`, an 818-line ordinary rational interval equality certificate (not the old generated affine owner-capture budget). Therefore **no claim of zero generated certificates across the entire public proof** is justified. Its ordinary Lean trust/performance must be checked at G9; removing it is a distinct project, not a reason to reopen completed geometric owner case analysis.
- [ ] **G9.1.g** finish transitive import traversal and full exact theorem-signature/typecheck audit when Lean compilation is authorized. Record every error by file/line and patch source without modifying the hand theorem's hypotheses.
- [ ] **G9.2–9.4** ordinary-kernel compilation, axiom/dependency audit, equality reverse direction and reproducible proof. Not run.

**Static audit verdict:** G7/G8 are a written, connected source draft. Two concrete namespace problems were repaired; no code execution has verified them. The final gate remains **V pending**.

### Auditable commit timeline (UTC; local Chicago date Oct 22)

| Commit | UTC creation | Source or ledger event |
|---|---|---|
| `13ea96275` | 2026-10-23 01:46:26 | Negative-A, nonnegative-E necessary signed stress |
| `34a4773ed` | 2026-10-23 01:49:40 | E-first/A-second core application |
| `a9a0d9737` | 2026-10-23 01:53:42 | Generic/core duplicate theorem-name repair |
| `dfe7be58e` | 2026-10-23 01:56:06 | Joint genuine negative A/E positive TD2 |
| `9a95c1f1c` | 2026-10-23 01:57:51 | Core E-first all T dispatcher |
| `304501f64` | 2026-10-23 01:59:05 | Whole original high-GA BT2 exclusion |
| `d89955c70` | 2026-10-23 02:00:46 | Unconditional table-free SharpSourceEntry proof body |
| `739d9428c` | 2026-10-23 02:02:45 | Public SharpAssembly capture replacement |
| `b57bc3ca4` | 2026-10-23 02:06:58 | EntryReduction caller repair |
| `e542f7aee` | 2026-10-23 02:10:07 | Public aggregate n8 geometric route and axiom-check staging |
| `6a57d7be0` | 2026-10-23 02:16:50 | SharpEntry interface documentation |
| `cc2f09355` | 2026-10-23 02:18:08 | Canonical handoff source reconciliation |
| `63377bee1` | 2026-10-23 02:19:12 | Nested gate D/J logging |
| `760e67283` | 2026-10-23 02:21:36 | Preserve pure geometric frame API |
| `e66ac3125` | 2026-10-23 02:25:21 | Correct actual core E block namespace (14 sites) |
| `9abfad8f5` | 2026-10-23 02:26:08 | Source entry geometry namespaces opened |
| `44aa756db` | 2026-10-23 02:29:05 | Static G9 audit ledger |

All timeline rows are GitHub commit author timestamps. None is a Lean compilation or proof-verification event.


### G9.1 source-path reinspection — Chicago Oct 22, 21:52–22:00 (UTC Oct 23)

This record supersedes the prior live-head snapshot; it is **source inspection only**.

- [x] **G7 / G8 confirmed in live branch:** unconditional `GlobalGAHighBT2Complete.high_GA_BT2_exclusion` ([`304501f64`](https://github.com/vltanh/lean4-squares-in-circles/commit/304501f64)), `GlobalGAHighSourceComplete.table_free_sharp_source_entry` ([`d89955c70`](https://github.com/vltanh/lean4-squares-in-circles/commit/d89955c70)) and the public `GeometricModel.SharpAssembly` import of the new source ([`739d9428c`](https://github.com/vltanh/lean4-squares-in-circles/commit/739d9428c)) are **present as uncompiled proof bodies**. Public `GeometricModel.Theorem` imports `SharpEquality` and `EntryReduction`, which in turn import `SharpAssembly`.
- [x] **G9.1.h — recent namespace repair recorded:** live head `79dfcf135386f4f01fd0ac7aab71644211643b77` (2026-10-23 02:34:39 UTC) is `[skip ci] Fix LongE and joint-negative source theorem namespace references`. This is textual source maintenance, not elaboration.
- [x] **G9.1.i — inspected top-level dependent modules:** `SquaresInCircles.lean` imports `Eight.GeometricModel.Theorem`; `GeometricModel.Theorem` imports `EqualityFamily`, `TwoHeightMinimum`, `SharpEquality`, `TableFree.EntryReduction`, `ExactFamily.StatementLink`, `Common.Optimum`. `SharpEquality` and `EntryReduction` both import `SharpAssembly`; `SharpAssembly` imports the new `GlobalGAHighSourceComplete`. No legacy `Candidate.Capture` appears in **these direct inspected edges**, but all transitive imports have **not** been checked.
- [x] **G9.1.j — separate generated equality certificate:** `Eight.Equality` → `ExactFamily.EqualityBox` and an existing `ExactFamily.Generated.EqualityBox.lean` (818 lines) remain in the broader source. This is not `Eight.Generated.AffineBudgets`; do not claim complete absence of any generated certificates. The generated equality certificate still needs kernel trust/performance checking.
- [x] **G9.1.k — audit entry location:** root `AxiomAudit.lean` (not `Eight/TableFree/AxiomAudit.lean`) already includes `#print axioms` for `TableFree.high_GA_BT2_exclusion`, `TableFree.table_free_sharp_source_entry` and public bound/equality. It **has not been run**.
- [ ] **G9.1.l — exhaustive transitive public imports, exact theorem signatures, all source proof terms:** remains open. A bounded module-inspection attempt hit tool-call limits; no full import-graph conclusion. No Lean compilation or kernel verification.
- [ ] **G9.2–G9.4 unchanged:** compile through the ordinary kernel when authorized; fix source errors, inspect actual axiom/dependency outputs, verify sharp equality in both directions, and benchmark runtime. Nothing in this update changes the unverified status.

**No false closure:** G0–G8 are D/J (source drafted and joined); G9 still V pending, despite the apparent mathematical source closure.


## 9. Full uncompiled public proof entry — 2026-10-22 Chicago

- [x] **G8.5.a** Add `SquaresInCircles/Eight/TableFree/UncompiledFullProof.lean` as the **single-source import** for the complete unrestricted theorem; source commit [`0e2b684ca9`](https://github.com/vltanh/lean4-squares-in-circles/commit/0e2b684ca9610ac58b393a921205e43b7129ea87). This is a real conjunction proof body from the existing main theorem, not a newly postulated condition.
- [x] **G8.5.b** Expose original squared-radius bound and full rigid equality witness, including explicit isometry/permutation and preservation of open/closed square membership; source commit [`a80e002d61`](https://github.com/vltanh/lean4-squares-in-circles/commit/a80e002d61fdc9040cdd71924f710fecfe89c558).
- [x] **G8.5.c** Stage `#print axioms` commands for the final theorem and precise equality statements in root `AxiomAudit.lean`; source commit [`2b9d54d92d`](https://github.com/vltanh/lean4-squares-in-circles/commit/2b9d54d92d93dbf27e0f9ff94cc802b65c3cf552). **Staged, not run.**
- [x] **G8.5.d** Publish the [full uncompiled source manifest](UNCOMPILED_FULL_DRAFT_2026_10_22.md), pinned source link, download archive, exact Lean import and hand-theorem dependencies; source commit [`40e65a9f1d`](https://github.com/vltanh/lean4-squares-in-circles/commit/40e65a9f1dc7c8d676a84d35dd6f2674bfbd4ec7).
- [x] **G9.1.m** Inspect the concrete uncompiled final entry and directly imported theorem modules against actual GitHub source. `GeometricModel.Theorem` imports `SharpEquality` and `EntryReduction`, both of which lead to `SharpAssembly`; `SharpAssembly` imports `GlobalGAHighSourceComplete` with `table_free_sharp_source_entry : SharpSourceEntry`; `GlobalGAHighSourceComplete` imports the total `GlobalGAHighBT2Complete`. **This verifies textual source declarations only**, not typing.
- [x] **G9.1.n** Verify the recent namespace corrections from commit [`79dfcf1353`](https://github.com/vltanh/lean4-squares-in-circles/commit/79dfcf135386f4f01fd0ac7aab71644211643b77) against current namespace boundaries: `GlobalGA.JointNegativeAETD2.original` is outside its inner `Source` namespace; `GlobalGA.NegativeA.LongE.original` likewise. This was an important **static** correction, but the source has not been elaborated.
- [ ] **G9.1.o — remaining:** full transitive import graph and all source-level theorem names/signatures, especially generated equality certificate independence; static inspection remains incomplete. An attempt to walk deeper dependencies via the connector hit per-call limits. Do not claim full capture-free transitive closure without finishing.
- [ ] **G9.2–G9.4 — unchanged, explicitly postponed by user:** Lean/Mathlib compilation, error repair, kernel/axiom validation and performance. Do not run Lean, Lake, tests or CI now.

**No verification claim:** G0–G8 have full uncompiled source; G9 is only partly audited, without kernel execution. The new full entry makes the deliverable easier to inspect but does not resolve elaboration or independent mathematical validity.

### G8.5 final equality completeness — October 22 (21:15–22:00 Chicago)

- [x] **G8.5.e — unique least containing circle:** `TableFree.unrestricted_model_unique_least_circle` reuses `GeometricModel.Parameters.unique_least_circle` (four positively weighted original anchor support vertices), source commit [`d1eb93776321`](https://github.com/vltanh/lean4-squares-in-circles/commit/d1eb93776321d02e5da7f96969eea6e2433ffb60).
- [x] **G8.5.f — nontrivial five-parameter equality family:** `TableFree.unrestricted_five_freedoms` reuses the `GeometricModel.Parameters.five_freedoms` witness on the strict five-dimensional parameter box; same source commit [`d1eb93776321`](https://github.com/vltanh/lean4-squares-in-circles/commit/d1eb93776321d02e5da7f96969eea6e2433ffb60).
- [x] **G9.1.p — exact final-entry axiom targets staged:** `AxiomAudit.lean` prints the aggregate theorem, squared-radius theorem, unique enclosing circle, five freedoms and rigid equality (not run), source commit [`384c5f4653aa`](https://github.com/vltanh/lean4-squares-in-circles/commit/384c5f4653aabda869a51e46f0bee2123c02f8a6).
- [x] **Full source handoff updated:** complete source [manifest](UNCOMPILED_FULL_DRAFT_2026_10_22.md), pinned revision, one-module final import, theorem index and original signed-owner hand argument.
- [ ] **G9.1.q** remaining full import traversal/source interface and any necessary repairs; no claim of source/type checking.
- [ ] **G9.2–G9.4** deferred compilation, axioms and runtime **not run at user's direction**.

**Status:** the whole handwritten n=8 theorem including circle-center uniqueness and five independent equalities has an uncompiled Lean draft in GitHub. The G9 verification gate is still genuinely open.
