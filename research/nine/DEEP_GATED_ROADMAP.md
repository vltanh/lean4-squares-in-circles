# n=9: deep gated roadmap — exhaustive tree cases and remaining cyclic branch

**Branch:** `research/nine-tablefree-hand`; **PR:** #11, draft.
**Checkpoint:** 2026-10-23, finite-tree continuation after base `c27384b`.

**Global mathematical status:** the unrestricted lower bound and complete unrestricted equality theorem remain **OPEN**. The common-coordinate-separable theorem has a hand proof. The unrestricted minimizing-stress route now has an **exhaustive six-case reduction for every positive tree component in the declared radius window**, with **two full nine-square completion cases excluded**. Four tree completion cases and the cyclic branch remain open. No Lean compilation, CI, independent full audit, or global closure is claimed.

This document consolidates the prior roadmap; all historical versions and exact commit times remain in Git history. It does not delete or weaken any earlier theorem. The previously local cap/tree manuscripts are committed. The new exact finite-tree regression script **and its executed report are also committed**, unlike the older conversation-local cap regression package.

## Canonical records and completion rules

- [PROGRESS_LEDGER.md](PROGRESS_LEDGER.md): append-only UTC source/commit and proof-scope history.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): current six-case tree inventory, checkboxes and precise completion obligations.
- [G2_SUBGATES.md](G2_SUBGATES.md): live G2 mathematical ledger.
- [TREE_FINITE_VALIDATION.md](TREE_FINITE_VALIDATION.md): exact physical stress witnesses, counterexamples to tempting shortcuts and reproducible regression provenance.

**CLOSED hand** means the complete quantified implication is written with no sampled computation as a proof premise; independent audit and Lean verification remain separate. **PARTIAL** means only the stated parent subclasses are covered. **REJECTED** means a precise false implication has an exact witness. A global necessary condition is not automatically a sharp lower bound. A finite inventory must retain **all nine physical squares**, including unstressed bodies and zero-stress contacts.

## 0. Target and dependency map

Put Q=1105/256, R*=sqrt(1105)/16. The exact construction proves R9<=R*. The missing theorem is:

> **T9:** every family of nine independently oriented unit squares satisfying the repository's original Packing predicate in a disk of radius R satisfies R^2>=Q.

Closed squares may touch; their open interiors must be disjoint. All orientations and disk centers are permitted. Equality necessity and sufficiency must use the actual project congruence convention, preserving continuous slider/rotation freedom.

```text
G0 exact model / construction / negative controls             CLOSED hand
G1 short signed/grid/cap/row terminal inequalities            CLOSED hand at stated scopes
G2.C entire common-coordinate-separable class                 CLOSED hand
 |
G2.O3.0 minimizer -> actual-contact stress                    CLOSED hand reduction
G2.O3.1 physical force/torque incidence, radial bridges        CLOSED hand reduction
 |
 +-- TREE.F1 all tree bodies localized                        CLOSED hand
 +-- TREE.F2.I origin-interior tree roots excluded             CLOSED hand
 +-- TREE.F2.R ALL positive tree radii equal 17/4              CLOSED hand, explicit window
 +-- TREE.F2.C exactly six central-incidence cases            CLOSED hand, exhaustive
 |      |
 |      +-- TREE.20 two side-origin bodies                    OPEN
 |      +-- TREE.11 side + vertex                             OPEN
 |      +-- TREE.12 side + two vertices                       CLOSED hand: total capacity <=8
 |      +-- TREE.02 two vertices                              OPEN
 |      +-- TREE.03 three vertices                            OPEN
 |      +-- TREE.04 four vertices                             CLOSED hand: total capacity <=8
 |
 +-- CYCLIC selected component contains a cycle               OPEN global sharp cover
 |
G2.O3.3 exhaustive sharp cover of TREE + CYCLIC                OPEN
G2.O4 uniform bounds for every remaining completion           OPEN
G2.O5 / G2.X / G4 unrestricted optimal radius                  BLOCKED
G5 every unrestricted equality packing                       OPEN/BLOCKED
G6 independent whole-manuscript audit                         NOT COMPLETED
G7 Lean standard-kernel / Palomar replay                      NOT STARTED
G8 public integration and final review                        NOT STARTED
```

**Explicit radius-window dependency:** TREE.F1/F2 and the tree inventory assume 79/40<=R<=sqrt(Q). The existing n=8 lower bound can provide this after deleting a square, but its current proof has computational dependencies. That is a **declared prior theorem dependency**, not a new standalone table-free n=9 lower-window proof. A strictly independent hand proof must discharge **G0.W** below.

**Do not combine distinct graphs silently:** the <=19-term planar translational body stress and the <=27-atom physical force/torque incidence stress are different certificates. Planarity of the incidence graph does not imply planarity of the positive body-pair graph. A bridge below means a bridge of the selected positive body-pair graph, not an arbitrary touching pair.

---

## G0 — Physical semantics, attainment and controls [CLOSED hand except stated window audit]

### G0.1 Exact geometry
- [x] **G0.1.1** Square center c and orthonormal side vectors u,v determine its four corners c+(epsilon*u+eta*v)/2.
- [x] **G0.1.2** Full disk containment is equivalent to the four corner bounds, with maximum squared norm |c|^2+1/2+|c.u|+|c.v|.
- [x] **G0.1.3** Physical nonoverlap is the finite true separating-axis disjunction from either square's edge normals, with equality and multiple owners permitted.
- [x] **G0.1.4** Disjoint open unit-square interiors imply center distance >=1 through their inscribed open half-radius disks. No common-coordinate implication is assumed.

### G0.2 Attainment and negative tests
- [x] Exact Q construction: HAND_PROOF.md.
- [x] Independent nonanchor rotations and no global separating frame: NONRIGID_WITNESS.md, NO_GLOBAL_ORTHOGONAL_FRAME.md.
- [x] Real residual two-stack equality and perpendicular signed 4+3 chains: TWO_STACK_SHARP_EQUALITY_WITNESS.md.
- [x] Even nine parallel squares can be nonstratifiable in every frame: NONSTRATIFIED_PARALLEL_NINE.md.
- [x] Center-radius/L-infinity relaxation alone is insufficient: CENTER_RELAXATION_COUNTEREXAMPLE.md.
- [x] Eight physical squares can have crossed perpendicular four-chains below Q: CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md. The ninth square is essential.
- [x] The cap manuscript supplies a q=Q packing with no triple sharp cap in any direction. Universal cap extraction is a false equality normalization.
- [x] New physical negative controls: TREE_FINITE_VALIDATION.md. Nonaligned and branching positive trees at 17/4 really exist with fewer than nine bodies. Three extra squares can occupy one side of a staggered four-chain. Neither false exclusion may be used downstream.

### G0.W Lower-radius window [EXPLICIT IMPORT OR OPEN INDEPENDENT HAND SUBGATE]
- **W.1** For a proof depending on the established n=8 theorem, state the deletion argument and its exact source/theorem assumptions.
- **W.2 OPEN for a completely independent hand proof:** establish the coarse bound R>=79/40 for nine physical unit squares without importing the current n=8 computational proof.
- No tree manuscript is advertised without its lower-window premise. A proof of all six tree capacities alone does not erase this dependency.

---

## G1 — Sharp terminal tools [CLOSED hand, conditional]

### G1.T1 Signed 4+3 / four-anchor stress
- [x] Long/short endpoint spans, matched perpendicular gaps with independent signs, exact weights 23 and 9, and all-angle square orientation penalties imply q>=Q.
- [x] Equality pins the stressed outer squares; intermediate chain widths then force the seven-chain alignment.
- Sources: FOUR_ANCHOR_STRESS.md, PAIRED_FOUR_ANCHOR_STRESS.md, SIGNED_MATCHED_CHAIN_STRESS.md.
- **Scope:** no theorem here forces arbitrary unrestricted packs to have those endpoints or separators.

### G1.T2 Grid / projection cap / fixed-owner dual
- [x] Arbitrarily rotated projection-separated cap-row theorem: ORIENTATION_STABLE_SEVEN_ANCHOR.md.
- [x] Four-corner grid spans force q>=9/2>Q: GRID_FOUR_CORNER_STRESS.md.
- [x] Exact convex center-eliminating weak dual after actual separator owners and orientations are fixed: SEPARATOR_GRAPH_CONVEX_DUAL.md. At a minimizer, stress existence gives attainment at its **unknown** value q0, not q0>=Q by itself.

### G1.T3 Oblique-safe cap and full solid-row completion [hand manuscripts; independent audit pending]
- [x] **CAP.1** Clipped section length >=1 (strict if tilted) for a unit square in D_Q above y=7/16, on [-3/2,3/2] at y=5/4.
- [x] **CAP.2** Three physically disjoint squares there force q=Q, aligned outer centers (+/-1,15/16), and one sliding central square. Four cannot fit that cap.
- [x] **CAP.3** Every hypothetical q<Q nine-square pack has >=5 squares meeting |y|<7/16 in **every** direction. This is an unrestricted necessary condition, not a final contradiction.
- [ ] **CAP.4** Combine that every-direction condition with contact/packing geometry into a sharp obstruction, or provide an exhaustive alternative to cap extraction. Antichains of projection intervals need not be coordinate-separated physical rows.
- [x] **ROW.1–2** Every physical five-square completion of a **solid** 4x1 row forces q=Q; arbitrary rotations and oblique free/free separators allowed.
- [x] **ROW.3** Four projection-separated squares opposite three unrestricted squares across a common seam force q=Q.
- [ ] **ROW.4** Derive one of these hypotheses from arbitrary minimizers or use a different terminal. Staggered chains are not solid rows.
- Sources: UNRESTRICTED_THREE_SQUARE_CAP.md, SOLID_FOUR_ROW_UNRESTRICTED_NINE.md.

---

## G2.C — Common-coordinate-separable class [CLOSED hand]

This complete branch assumes one orthonormal frame separates **every pair** in at least one coordinate projection; individual square orientations remain arbitrary. It is strictly weaker in scope than unrestricted Packing.

- [x] **C0** Longest x/y chain ranks inject the nine squares into a product; absence of four-chains forces a 3x3 grid stress, while five-chains cannot fit. ORTHOGONAL_RANK_DICHOTOMY.md.
- [x] **C1** Four-chain shadow and inner-pair domination. FOUR_CHAIN_SHADOW_BARRIER.md and INNER_PAIR_SHADOW_DOMINATION.md.
- [x] **C2** The complete large-zigzag branch is excluded. ZIGZAG_BRANCH_CLOSED.md. No residual 4x3 zigzag case remains open.
- [x] **C3.a** Disjoint 4+3 chains close via the signed stress; the five-square complement without a triple partitions into two vertical rank stacks, (4,1) or (3,2).
- [x] **C3.b** The entire (4,1) class is excluded by the crossed-four-chains-plus-ninth central cover. FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md.
- [x] **C3.c** The (3,2) class switches frame via a five-element matching and singleton split, yielding perpendicular signed 4+3 chains.
- [x] **C4** Complete sharp lower bound and equality skeleton necessity within this class. COORDINATE_SEPARABLE_NINE_COMPLETE.md.

**Do not reopen C** for tiny constant or angle refinements. The exact oblique equality witness proves that C cannot be promoted globally by assuming a common frame.

---

## G2.O3.0–O3.1 — Unrestricted minimizing physical stress [CLOSED hand reductions]

### O3.0.2 Compact minimizer and exact stress
- [x] Normalize disk center; compact center/frame bounds and a finite union of closed SAT conditions give a global minimizer q0<Q from any subcritical packing.
- [x] Strictly separate physically noncontacting pairs; positive chosen multipliers then belong only to true contacts.
- [x] The dilation direction supplies constraint regularity and a normalized nonnegative active stress; no abnormal multiplier or optimizer is assumed.
- [x] In fixed-frame center/radius variables, <=19 positive terms suffice and the weak dual attains q0 exactly. Every component has circle load on >=2 bodies; a connected component can be retained and normalized.
- Source: SPARSE_MINIMIZER_STRESS.md.

### O3.1a–e Planar translational support and separate angular balance
- [x] Four-way junction geometry, compatible diagonal selection and stress uncrossing yield a planar outer-loaded **translational** support, re-sparsifiable to <=19 terms.
- [x] Unloaded degree-two paths have <=2 internal bodies at q<=Q.
- [x] A separate smooth-support/angle conic argument gives <=27 atoms and exact angular equations without differentiating absolute values at cusps.
- Sources: PLANAR_STRESS_CORE.md and ROTATION_STATIONARY_STRESS.md.
- **Nonclaim:** the two certificates are not silently the same, and planarization is not asserted to preserve angular balance.

### O3.1f Actual force points and joint force/torque incidence
- [x] Vertex/edge, point-only vertex/vertex and common-side contacts have genuine physical application-point constraints and normalized equilibrium.
- [x] The <=27-atom certificate has force and torque balance and a planar **contact-point incidence network** with loaded bodies on the exterior face.
- [x] Unloaded two-force bodies transmit across opposite sides or opposite vertices. Square-ended path reserves are 0,1,sqrt(2),2 at q<=Q.
- Source: PHYSICAL_CONTACT_STRESS.md.
- **Limit:** neither the body-pair graph nor the <=19 translational support acquires all these properties automatically.

### O3.1g Radial bridges and loaded geometry
- [x] Cut moments make every positive body-pair bridge radial. Nonbridge edges need not be radial.
- [x] At most four central, geometrically circle-clear bodies cover the bridge set; not all contacts or all positive edges.
- [x] A suitable normal choice makes off-origin point-only vertex/vertex positive contacts cyclic, never bridges.
- [x] A loaded graph leaf is exact side-normal S or diagonal D type, with contact radii A=sqrt(R^2-1/4)-1 or B=R-sqrt(2).
- Source: RADIAL_BRIDGE_AND_LEAF_REDUCTION.md; existing commit 028a63b is credited as a prior input.

### O3.1h–j Prior cap / star / two-loaded-tree results
- The cap and solid-row outputs are recorded under G1.T3.
- SMALL_TREE_STRESS_CORES.md excludes stars in the explicit window and classifies two-loaded trees as a four-square side path at q0=17/4, allowing two inner sliders.
- The new TREE.F1/F2 below **strengthens** this from selected small trees to **every positive tree**, and replaces the previous unspecified nonstar-tree inventory with six exhaustive incidence cases.

---

## G2.O3.2 — Finite, completion-aware tree/cycle split [PARTIAL]

For the chosen physical certificate there are two logically exhaustive alternatives:

- **TREE:** at least one positive component is a tree. Retain one such component, but keep **all nine physical squares** for completion capacity; other stress components and zero-stress bodies remain obstacles.
- **CYCLIC:** every positive component contains a cycle. This branch remains open and is not counted as one of the six tree cases.

### TREE.F1 — Localization of every positive tree body [CLOSED hand; audit pending]

Source: [TREE_BODY_LOCALIZATION.md](TREE_BODY_LOCALIZATION.md), commit 4f8144d.

- [x] **F1.1** Every unloaded tree body meets the central D_delta and there are at most four. An unloaded noncentral outer body would have only parallel same-sign contact forces and could not balance.
- [x] **F1.2** Every loaded tree body, even of degree two, has radial S/D geometry: all its incident force points coincide with its unique nearest point. D degree=1; S degree<=2.
- [x] **F1.3** A radial outward support point of any square avoiding zero has radius >1.
- [x] **F1.4** An unloaded tree body avoiding zero exists only if A>1. It is a single side-normal transmitter with center (A-1/2)e+bJe, |b|<=1/2, incoming point (A-1)e and outgoing point Ae. Its incoming neighbors contain zero, and its one outgoing neighbor is the S terminal at (A+1/2)e. No arbitrarily long off-origin tree arms remain.
- [x] **F1.5** At least one unloaded body contains zero. If unique, it is the root of a subdivided star with arm length one or two.
- The force-balance necessity of both incoming and outgoing edges is made explicit in TREE_FINITE_VALIDATION.md, Section 6.

### TREE.F2 — Radius quantization and exhaustive incidence cover [CLOSED hand; audit pending]

Source: [TREE_RADIUS_QUANTIZATION.md](TREE_RADIUS_QUANTIZATION.md), commit 4007bfc.

- [x] **F2.D** A diagonal loaded terminal requires an origin-INTERIOR unloaded neighbor.
- [x] **F2.I** No such origin-interior body occurs: ordinary stars are previously excluded; a subdivided star is ruled out by the exact side-interior/vertex alternatives for its short radial arm contact. This covers every short-arm angle, not sampled intervals.
- [x] **F2.V** If zero is a vertex of an unloaded square, its allowed nonzero radial support points have radii 1 or sqrt(2), forcing A=1.
- [x] **F2.S** If zero lies inside a side, the five exact radial support-point types force A=1; A<1 and A>1 each give an uncancellable horizontal contact force.
- [x] **F2.R** Therefore **EVERY positive tree component in the window has q0=17/4**. All unloaded bodies contain zero on their boundaries, and all loaded bodies are S terminals at centers (3/2)e, contact points e.
- [x] **F2.C** Let s count side-interior-origin unloaded bodies, v count vertex-origin unloaded bodies. Disjoint tangent cones give 2s+v<=4; at least two unloaded bodies give s+v>=2. The exact six integer profiles below are exhaustive.

### TREE.F3 — Six disjoint full completion cases [2 CLOSED, 4 OPEN]

Each row includes all its continuous parameters, all loaded bodies and **every additional unstressed square**. It is not a test of a representative drawing.

| Case | (s,v) | Entire geometric family | Gate state |
|---|---|---|---|
| **TREE.20** | (2,0) | Two opposed side-origin bodies; four-square path with inner offsets strictly in (-1/2,1/2) | [ ] OPEN; flat row alone excluded |
| **TREE.11** | (1,1) | Side-origin plus vertex-origin body; arbitrary compatible angle/offset and loaded terminals | [ ] OPEN; nonaligned five-body stress witness retained |
| **TREE.12** | (1,2) | Side body and two vertex bodies fill all origin angles | [x] CLOSED hand: all four cardinal loaded squares forced; total capacity <=8 |
| **TREE.02** | (0,2) | Two origin-vertex bodies with arbitrary nonoverlapping right-angle cones | [ ] OPEN |
| **TREE.03** | (0,3) | Three origin-vertex bodies with all compatible angular gaps and loads | [ ] OPEN |
| **TREE.04** | (0,4) | Four origin-vertex bodies tile a central 2x2 square | [x] CLOSED hand: central-block completion capacity <=8 |

**Boundary coverage:** when an inner path slider reaches +/-1/2, the square's incidence changes from side interior to vertex and is counted by the corresponding vertex row. No endpoint is discarded. Cases are profiles of the selected component, not counts of every central unstressed physical body.

#### TREE.CAGE — Four cardinal S terminals [CLOSED hand]
- [x] **CAGE.1** At q0=17/4 every square center has norm <=3/2.
- [x] **CAGE.2** Avoiding the four cardinal outer squares via inscribed disks leaves only the central center box [-1/2,1/2]^2 and four diagonal center regions |x|,|y|>=1.
- [x] **CAGE.3** Actual square support, not merely center disks, excludes every diagonal region. Two exact all-angle factorizations give the strict outer-corner contradiction.
- [x] **CAGE.4** Each sign quadrant of the central box has diameter <1, so at most four additional centers exist. The entire physical packing has <=8 squares, arbitrary extra orientations allowed.

#### TREE.BLOCK — Central solid 2x2 block [CLOSED hand]
- [x] **BLOCK.1** An extra half-radius inscribed disk must be >=1/2 from [-1,1]^2 while its center norm is <=3/2.
- [x] **BLOCK.2** Only the four cardinal centers survive; exact corner equality forces their frames axis-aligned. At most four additional squares exist.

#### TREE.12 closure [CLOSED hand]
- [x] The origin tangent cones force a common frame for its three central bodies.
- [x] The side-origin body requires an upward S load; component force balance requires downward load.
- [x] Exactly two loaded bodies would force exactly two unloaded bodies by the prior two-loaded-tree theorem, contradicting this profile. Hence horizontal loads occur and force their opposites: all four cardinal terminals are present.
- [x] Apply CAGE to all remaining physical squares. No ninth square fits.

#### TREE.04 closure [CLOSED hand]
- [x] Four origin quadrants force the exact central [-1,1]^2 block.
- [x] Apply BLOCK. No ninth square fits.

Source for both full cases and both capacity theorems: [TREE_FINITE_COMPLETIONS.md](TREE_FINITE_COMPLETIONS.md), commit 5acabe7.

#### Remaining four tree rows [OPEN, explicit contracts]
- **TREE.20.a:** bound every physical five-square completion of the entire staggered two-slider four-square path at q0=17/4. Do not assert <=2 squares on either side separately: an exact three-above staggered-row counterexample is retained.
- **TREE.11.a:** include the genuine nonaligned five-body Y-like tree stress from TREE_FINITE_VALIDATION.md; the missing theorem is its entire nine-square completion capacity, not that this core is impossible.
- **TREE.02.a / TREE.03.a:** retain arbitrary relative cone angles, shared loaded S terminals where allowed, zero-weight physical contacts and every unstressed body. Prove one whole-class capacity or sharp-support inequality per row, or one common lemma covering several rows.
- **TREE.ALL exit:** all six rows checked and their finite-cover/radius lemmas audited. Two checked rows are not an all-tree theorem or a fraction of global proof completion.

### CYCLIC — Selected positive components with cycles [OPEN]

- **CY.1** Prove a human-sized exhaustive geometric inventory of positive components containing cycles, retaining bridges, loaded nodes, actual junction incidence and all physical completions. The tree radial law cannot be applied to nonbridge edges.
- **CY.2** Keep actual circle loads and all nine physical squares; a small stressed component can exist below Q and is not itself a nine-square counterexample.
- **CY.3** Obtain orientation-uniform sharp stresses/capacity inequalities for every surviving inventory leaf, or a universal inequality covering all cycles at once.
- **CY.4** Preserve the known q=Q oblique and nonstratified examples. A raw finite count of all SAT graphs is not a useful finite hand proof.
- **Exit:** every nine-square minimizing pack whose selected positive graph has no tree component obeys q0>=Q. Not proved.

### O3.3 / O4 — Exhaustiveness and uniform sharpness [OPEN globally]

- **O3.3.a CLOSED for TREE only:** TREE.F2 proves six exhaustive geometric profiles, not six sampled configurations.
- **O3.3.b OPEN globally:** finish all tree rows and CYCLIC, with radius-window dependencies and original physical hypotheses explicit.
- **O4.a CLOSED existentially:** exact stress multipliers at a minimizer attain q0; this does not show q0>=Q.
- **O4.b OPEN:** derive the uniform desired inequalities for every unsolved full completion class, or use CAP.3 with a global contact-capacity invariant to bypass graph enumeration.
- **O4.c:** characterize all equality slacks without forcing unstressed bodies into a common frame.
- **No completion by gate proliferation:** do not introduce a new infinity of tilt/height leaves. New subcases must be a proved finite partition of a whole parent, with complete continuous parameter domains.

---

## G2.X / G4 — Unrestricted lower bound [BLOCKED]

- [x] **X.1** Any q<Q packing has an unrestricted global minimizer with a physical stress certificate.
- [ ] **X.2** Supply the explicit lower-window input, TREE.ALL and CYCLIC (or a universal sharp invariant) to exclude every such minimizer.
- [ ] **X.3** Remove all graph/frame/row hypotheses except those proved from original Packing. A conditional branch must not be promoted silently.
- [x] **G4.1** Exact construction attains Q.
- [ ] **G4.2–3** Assemble sharp lower bound, take the nonnegative square root and match the public Optimum/Packing statements.

The optional origin-incidence or every-direction strip route can replace this proof architecture if it yields a complete sharp theorem. It is not a third independent mandatory program.

## G5 — All equality configurations [PARTIAL]

- [x] **G5.0.1** STRATIFIED_EQUALITY_FAMILY.md gives necessity/sufficiency within stratification.
- [x] **G5.0.2** SIGNED_MATCHED_EQUALITY_FAMILY.md gives the full conditional signed 4+3 domain: four pinned endpoints, three slider heights, two freely oriented extra squares and 15 actual SAT pair tests.
- [x] **G5.0.3** Every common-coordinate equality packing has such a signed skeleton after a frame choice.
- [x] **G5.0.4** Cap/solid-row terminals pin their stated conditional anchors; the capless equality witness rejects universal triple-cap extraction.
- [ ] **G5.1** Once optimality is proved, apply minimizing-stress necessity to EACH original q=Q packing, not only a replacement minimizer.
- [ ] **G5.2** Prove which tree/cyclic equality terminals survive, and list complete necessary-and-sufficient free-parameter domains.
- [ ] **G5.3** Quotient by the repository's actual rotations/relabelings, treating reflections correctly. Do not claim isolated uniqueness in a continuous family.

## G6 — Independent audit and exact execution [NOT COMPLETED]

- **G6.1** Independent review of general minimizer regularity, physical shared-point torque, graph representation distinctions and all finite-cover implications.
- **G6.2** Independently check new TREE.F1/F2 localization, origin-interior root exclusion, all-tree radius quantization, CAGE's diagonal-center strictness and boundary cases, and TREE.12 load-count inference.
- **G6.3** Audit exact cap section/solid-row arguments and their equality and lower-window dependencies.
- **G6.4 CLOSED finite regression only:** check_finite_tree_cases.py at commit 8a6eea1 was matched by Git blob and SHA-256 and actually executed. FINITE_TREE_EXACT_CHECK.json records 909 rational checks, six integer profiles, seven exact physical force/torque tree witnesses, cage attainment and failed-shortcut controls. This is **not** universal optimality or independent audit.
- **G6.5** Keep the nonaligned TREE.11 core, seven-body TREE.12 core and below-window star as negative controls against overstrong exclusions; keep the staggered-row three-above witness.
- **G6.6** Prior sparse/physical-stress regressions and the older local cap report retain their original limited scope; never relabel them as a general proof replay.
- **G6.7** Record each finished work item, commit time, exact quantified scope and remaining blocker in PROGRESS_LEDGER.md and FINITE_TREE_CASE_LEDGER.md.

## G7 — Lean standard-kernel / Palomar formalization [NOT STARTED]

1. Formalize exact geometry and radius construction with original unrestricted semantics.
2. Formalize compactness, finite active-gradient/conic argument and actual physical force/torque constraints without oracles.
3. Formalize the actual complete tree/cyclic/global sharp proof once mathematically closed, not a stronger assumed normal form.
4. Formalize equality necessity and parameter-domain sufficiency.
5. Compile, inspect axioms/import dependencies and perform independent standard-kernel replay. No native-kernel bypass, admitted theorem, undisclosed external certificate or unvalidated giant table.

## G8 — Integration [NOT STARTED]

Integrate n=9 into Optimum/radius/packing registries and Challenge mirror, update proof documentation and equality models, check n=1–8 regressions, retain source hashes/UTC provenance, and finalize PR only after the advertised proofs and verification are complete.

## Execution order and progress contract

1. The tree branch now has **six exhaustive cases**. Use their fixed IDs; tick a row only when its **entire nine-square completion family** is bounded.
2. TREE.12 and TREE.04 are closed by hand; TREE.20, TREE.11, TREE.02 and TREE.03 remain open. Do not reopen the solved coordinate or star cases for minor improvements.
3. Keep CYCLIC explicitly open. A finite tree inventory is not global graph coverage.
4. Commit meaningful proofs and their scope promptly. Log UTC provenance, theorem hypotheses, validation results and unchanged global blockers after each substantive batch.
5. No fake progress percentages: two of six tree rows closed does not mean one third of the unrestricted theorem is complete.
6. New hand arguments remain audit-pending until independently reviewed; no Lean/CI claim before execution.
