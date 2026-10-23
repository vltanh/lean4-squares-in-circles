# PR #10 — executable gate tree for the table-free eight-square hand proof

**Prepared:** 2026-10-22 (America/Chicago), against the live source branch \`formalize/eight-uncompiled-draft\`. **Target:** a new public Lean/Mathlib proof of the unrestricted n=8 sharp radius and full five-parameter equality classification, without using generated affine/owner capture. **Rule:** write and push faithful, uncompiled Lean first; audit and ordinary-kernel compilation only after source assembly, with separate authorization. [PR #10](https://github.com/vltanh/lean4-squares-in-circles/pull/10).

## 0. What “closed” means

Each item may have one of four independent states: **H** = hand argument documented; **D** = Lean source drafted with a proof body; **J** = imported into the actual end-to-end source theorem; **V** = ordinary Lean kernel verified. \`H\` or \`D\` never implies \`J\` or \`V\`. No \`sorry\`, new axioms, generated owner/word lookup or silently strengthened hypotheses. No premature percentage-complete estimates.

At each leaf, record (i) actual theorem name, (ii) initial and terminal hypotheses, (iii) whether the physical selected normal, source radius, original centers and weak ties are retained, (iv) the commit SHA and timestamp, and (v) whether it is source-only. Do not create new families of increasingly narrow cases unless their union is demonstrably exhaustive.

**Global acceptance:** a term of the unconditional \`TableFree.SharpSourceEntry\`, then a public theorem whose *transitive* import path does not use \`Candidate.Capture\` or its generated owner lookup, with the original radius, exact equality family and least-circle uniqueness. Standard-kernel verification is G9, not implied by a checked-in draft.

## 1. Foundational gates (G0–G2)

### G0 — Stationary sharp datum and complete equality family (D; verification pending)

- [x] **G0.1 — Exact sharp configuration and stationary equations, draft.**
  - [x] G0.1.1 Define the five corner anchors, two free intermediates, physical frame vectors and sharp squared radius, without decimal enclosure in theorem statements.
  - [x] G0.1.2 Give the complete positive dual balance and exact contact identities.
  - [x] G0.1.3 Transcribe existence and global five-anchor minimum/rigidity: \`GeometricStationaryExistence\`, \`FiveCornerNominalTrial\`, \`StationaryCanonicalRigidity\`.
- [x] **G0.2 — Original equality family, draft.**
  - [x] G0.2.1 Two zero slider forces and all contact equalities.
  - [x] G0.2.2 Necessary and sufficient five-parameter inequalities and converse.
  - [x] G0.2.3 Noncongruent open five-dimensional subfamily and unique least circle, source claims.
- [ ] **G0.3 — Exit:** trace the exact stationary statements to the final new imports, then kernel-check once G8 is joined. *Do not redo the stationary calculation as a new numeric search.*

### G1 — Original-radius boundary reduction and physical frame transport (D/J, unverified)

- [x] **G1.1 — Fresh original representative, draft:** fixed-witness recession at the *working* radius; never simply relabel old outer centers with a new ceiling.
  - [x] G1.1.1 Keep the original central-square packing and original seven selected physical normals.
  - [x] G1.1.2 Original sortedness, core avoidance, one-winding cycle, physical gaps.
- [x] **G1.2 — Continuous Q/Q0 support transfer, draft:** actual angle gaps, frame spread, signed errors, all actual radial kinds; \`FramePhysicalTransport\`.
  - [x] G1.2.1 Physical reflection/reversal and cyclic reindexing preserve selected normal projections.
  - [x] G1.2.2 Radius-level transfer between the outer word-classification ceiling and the original sharp ceiling retains its stated hypotheses.
- [x] **G1.3 — Normalization join drafted:** \`GlobalNormalization\` imports \`TableFree.QuarterWordSelection\`.
- [ ] **G1.4 — Exit:** check every imported source lemma in the end-only audit; no generated word-selection side route in the new public dependency closure.

### G2 — Seven quarter words to the candidate word (J at source level; V pending)

**Source inspection 22 October:** \`QuarterDoubleExclusion.lean\`, \`ShortWordExclusion.lean\`, \`SecondWordExclusion.lean\`, and \`QuarterWordSelection.lean\` form a complete *drafted* assembly. Historical ledgers calling the four zero-quarter and four mixed-quarter cases untouched are stale; inspect concrete source, not the older table.

- [x] **G2.1 — Exhaustive integer quarter-word classification, draft.**
  - [x] G2.1.1 All seven admissible dihedral representatives.
  - [x] G2.1.2 Four representatives with double increments excluded by continuous common edge costs.
  - [x] G2.1.3 Physical dihedral normalization of representatives, not an arbitrary frame change.
- [x] **G2.2 — Short binary wrong word, source join present.**
  - [x] G2.2.1 Original zero-quarter edge, both radial kinds and every weak witness.
  - [x] G2.2.2 Original outer/core quarter edge, reflected owners and signs.
  - [x] G2.2.3 Literal vertex markers telescope; strict total > 2π.
  - [x] G2.2.4 \`ShortWord.not_dihedral\`.
- [x] **G2.3 — Second binary wrong word, source join present.**
  - [x] G2.3.1 Outer–outer zero-quarter: four original sign/edge representatives with owner adapters.
  - [x] G2.3.2 Outer–outer quarter: six edge/sign representatives.
  - [x] G2.3.3 Mixed zero-quarter: both source/target radial directions, both signs.
  - [x] G2.3.4 Mixed quarter: all concrete families and original-owner physical wrappers.
  - [x] G2.3.5 Core–core edges and closed shared endpoints.
  - [x] G2.3.6 Same original marker on both incident edges; strict total > 2π; \`SecondWord.not_dihedral\`.
- [x] **G2.4 — Actual word exit drafted:** \`TableFreeWordGeometry.quarter_word_candidate\` excludes both wrong binary classes, then \`GlobalNormalization.candidate_normalization_of_word\` consumes it.
- [ ] **G2.5 — Exit:** kernel-check these source imports; confirm no indirect fallback to generated \`Candidate.Capture\` or unproved owner hypotheses. *No new case enumeration while the assembled source is present.*

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
- [ ] **G3.4 — Exit:** one \`BoundaryCycle\` / \`SignedCycle\` theorem exposing complete allowed original owners, radial alternatives, sign and tie cases to G4; no generated lookup and no sector assumption disguised as universal.

### G4 — Complete finite G/T same-radius source matrix (D locally; J missing)

- [x] **G4.1 — Positive-BT3 scalar/source leaves drafted** (proof bodies exist; no compilation).
  - [x] G4.1.1 Nonnegative selected A/E totals, arbitrary signed TD0.
  - [x] G4.1.2 Negative flat A, nonnegative E; short and long E.
  - [x] G4.1.3 Joint negative flat A/E, arbitrary signed TD0.
  - [x] G4.1.4 Genuine negative DE3, nonnegative A, positive BT3: \`GlobalGANegativeDEBT3Source\`.
  - [x] G4.1.5 Genuine negative EH1, nonnegative A, positive BT3: \`GlobalGANegativeEHBT3Source\` / physical frame adapter (latest concurrent source commits). *All marked D, not verified.*
- [x] **G4.2 — Positive BT2/TD2 scalar/source leaves drafted** where concrete source file exists.
  - [x] G4.2.1 Nonnegative A/E selected totals and both TD2 signs.
  - [x] G4.2.2 Negative DE3, nonnegative A, positive TD2.
  - [x] G4.2.3 Negative EH1, nonnegative A, positive TD2, both small/far EH intervals: \`GlobalGANegativeEHTD2Source\`.
  - [x] G4.2.4 Negative A, negative E and mixed-sign descendants: stated-owner source packages, not a universal dispatcher.
- [ ] **G4.3 — Remaining nonpositive/zero T cases: global source join.**
  - [x] G4.3.1 Aligned genuine negative BT3 with zero TD endpoint can acquire actual BT2, conditional source draft.
  - [x] G4.3.2 \`TTransport.reduce_complete\`: resulting T pair has BT2 or positive BT3/TD0.
  - [ ] G4.3.3 Eliminate the latter *on the transported actual same-q cycle*, without assuming signs or owner choices absent from \`SourceDomain\`.
  - [ ] G4.3.4 Export BT2 with unchanged five anchors, actual witness and all eligible signed budgets.
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
- [ ] **G4.7 — Exit:** a single \`original_source_to_terminal\`-style theorem with explicit original-q and original-witness invariants; *individual \`...Source.actual_false\` lemmas alone cannot close G4*.

### G5 — Sharp hard terminal and strict source-anchor loss (D conditional; J missing)

- [x] **G5.1 — Hard normal-owner sharp theorem drafted:** \`UniversalHardSharp.HardInput.hard_sharp\`, complete H/A/B/D/E anchors and actual contact equalities under \`HardInput\`.
- [ ] **G5.2 — Eliminate positive terminals from G4:** all E signs, both HG/TD owners, arbitrary signed errors; contradiction at q ≤ q*.
- [ ] **G5.3 — Eliminate genuine negative terminals:**
  - [ ] G5.3.1 G-/T0 yields strict *original H-anchor* circle loss before applying sharp hard theorem.
  - [ ] G5.3.2 G0/T- yields strict *original D-anchor* circle loss.
  - [ ] G5.3.3 G-/T- second conversion preserves the earlier strict H loss and adds strict D loss.
  - [ ] G5.3.4 Never substitute a moved G/T circle loss for loss at an unchanged anchor.
- [ ] **G5.4 — Exit:** only hard G0/T0 survives at q=q*, with the same original five anchor coordinates/frames. Emit enough retained data for G6, not just \`q=qStar\`.

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

### G7 — Unconditional sharp source entry (OPEN)

- [ ] G7.1 Instantiate \`GlobalNormalization S qStar\` and the actual source-domain theorem from G1–G3.
- [ ] G7.2 Consume the exhaustive G4 matrix, G5 hard equality and G6 original-source audit.
- [ ] G7.3 Construct **\`TableFree.SharpSourceEntry\`** *without an argument of type \`SharpSourceEntry\`*, \`Candidate.capture\`, a \`sorry\`, or an unstated original-owner premise.
- [ ] G7.4 Ensure \`source_witnesses_of_recovered_equality\` uses the unchanged source and initially retained normals.
- [ ] **G7 exit:** actual inhabitant of the proposition in \`TableFree/SharpEntry.lean\` under the exact \`GlobalNormalization\` hypotheses.

### G8 — Public sharp theorem and full equality (OPEN new route)

- [ ] G8.1 Replace \`GeometricModel.SharpAssembly.compatibility_source_entry\` with G7; remove \`Candidate.Capture\` from *all transitive public imports*.
- [ ] G8.2 Lower bound is for original arbitrary-radius packing: \`qStar ≤ q\` / \`sqrt qStar ≤ R\`, not merely a moved representative.
- [ ] G8.3 Equality gives original stationary physical frames and five original anchors; G/T exactly two slider coordinates.
- [ ] G8.4 Five-parameter weak necessary-and-sufficient domain, converse, noncongruent open family and unique least enclosing circle survive the new route.
- [ ] **G8 exit:** the requested unrestricted theorem and equality family exist as source terms with a demonstrably capture-free import graph.

### G9 — Final checking and repair (DEFERRED BY REQUEST)

- [ ] G9.1 One interface/sign/case-coverage audit of the *finished* uncompiled draft (not endless rolling audits); pay particular attention to q vs Q0/Q1, original vs transported axes, zero errors, radial endpoints and omitted nonneighbor inequalities.
- [ ] G9.2 Ordinary Lean/Mathlib kernel compilation of the public theorem, once separately authorized. Fix all actual elaboration errors, not just syntactic declarations.
- [ ] G9.3 Check no new axioms/admissions, no native-kernel trust shortcut, no external numeric checker and no hidden generated \`Candidate.Capture\` dependency.
- [ ] G9.4 Inspect proof term dependencies, equality converse, public API and practical compilation size; optimize only after verified proof exists.
- [ ] **G9 exit:** reproducibly kernel-checked public proof and complete equality theorem, with a final commit and reproducible provenance.

## 4. Execution order and stop rules

1. **Verify the source *already present* for G2 at the level of textual imports; do not redo eight representative families.** Its formal verification is G9.
2. **G3:** establish original owner/sign/radial admissibility in one object. Only prove a new leaf if a specific finite original-owner cell is genuinely uncovered.
3. **G4:** join the currently drafted signed A/E/BT2/BT3 subcases, then close T and G source terminals and the exhaustive matrix. This is the central exit gate.
4. **G5–G6:** prove original anchor-loss terminal join, invariant strict source obstruction, and original physical normal recovery.
5. **G7, G8:** instantiate \`SharpSourceEntry\`, swap the public imports, preserve exact optimality/equality.
6. **G9** only after an explicit request to validate/compile.

If a subgate cannot be completed, record **one exact missing hypothesis/theorem** and whether it is logically false, not simply “more scalar work needed.” Never call a collection of restricted-case source lemmas an unrestricted original-packing proof. Mark the PR as still open until G7/G8 are actually joined; no false “closure” statement for an uncompiled draft.

## 5. Concrete first source targets

- \`SquaresInCircles/Eight/TableFree/GlobalGATransportTComplete.lean\`: inspect \`TTransport.CompleteResult\` and eliminate its positive-BT3/TD0 alternative under the *actual* available hypotheses; if a global assumption is missing, expose it as a typed prerequisite instead of silently strengthening it.
- \`SquaresInCircles/Eight/TableFree/GlobalGANegativeEHBT3Frame.lean\` and \`GlobalGANegativeDEBT3Source.lean\`: consume their original frame contradictions in a finite G4 owner dispatcher, with correct E type/sign partition.
- \`SquaresInCircles/Eight/TableFree/SourceEquality.lean\`, \`UniversalHardSharp.lean\`, \`SharpEntry.lean\`: join strict source evidence, original normals and hard equality.
- \`SquaresInCircles/Eight/GeometricModel/SharpAssembly.lean\`: edit only after G7 is genuinely inhabited.

**Current source-level high-water mark:** G2 is assembled as a draft; positive-BT3/TD0 DE/EH local exclusions are drafted; the global G3–G6 dispatcher, unconditional G7, capture-free G8 and verified G9 remain open. Recheck live HEAD because concurrent source commits may supersede these observations.
