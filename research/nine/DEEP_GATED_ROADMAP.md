# n=9: deep gated roadmap — two remaining tree completion families and CYCLIC

**Branch:** `research/nine-tablefree-hand`; **PR:** #11, draft.
**Checkpoint:** 2026-10-23 origin-pocket continuation after head `901678d`.

**Unrestricted optimality and global equality remain OPEN.** The full common-coordinate-separable theorem is hand-proved. The physical stress program has six exhaustive tree-incidence profiles: **TREE.12, TREE.03 and TREE.04 are excluded in full**, and **TREE.02.P (point-only central contact) is excluded in full**. Every surviving tree configuration is now reduced to exactly two explicit master completion families **P** and **Y**, with all continuous parameters and all unstressed squares retained. Their capacity bounds and the separate **CYCLIC** branch are not proved.

All new general results are written analytic hand arguments pending independent audit. No Lean compilation, CI, global theorem or proof-completion percentage is claimed. Previous roadmap versions and exact timestamps remain in Git history.

## Source and progress records

- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): six original profiles, contact-type split, checked cases and P/Y frontier.
- [ORIGIN_POCKET_PROGRESS.md](ORIGIN_POCKET_PROGRESS.md): this continuation's UTC commits, exact theorem scopes, actual execution and unchanged blockers.
- [PROGRESS_LEDGER.md](PROGRESS_LEDGER.md): preceding append-only checkpoints.
- [G2_SUBGATES.md](G2_SUBGATES.md), [ROADMAP.md](ROADMAP.md), [README.md](README.md): live branch status and handoff.
- [ORIGIN_POCKET_EXACT_CHECK.json](ORIGIN_POCKET_EXACT_CHECK.json): pinned finite regression run, source hashes and non-strict-normal control. This is not an all-angle proof.

## 0. Exact target, conventions and dependency map

Q=1105/256 and R*=sqrt(1105)/16. An exact construction attains Q. The missing theorem is:

> **T9:** for every nine independently oriented closed unit squares with pairwise disjoint open interiors contained in a disk of radius R, R^2>=Q.

All disk centers, tangencies and independent square frames are permitted. Equality necessity and sufficiency must use the repository's actual rotation/relabeling/reflection convention and preserve continuous degrees of freedom.

```text
G0 physical model, attainment and negative controls           CLOSED hand
G1 signed/grid/cap/row/radial-pocket terminals                 CLOSED hand, conditional
G2.C entire common-coordinate-separable class                 CLOSED hand
 |
G2.O3.0 compact minimizer -> actual-contact stress             CLOSED hand reduction
G2.O3.1 physical force/torque and radial bridge structure      CLOSED hand reduction
 |
 +-- TREE.F1 all tree bodies localized                        CLOSED hand
 +-- TREE.F2 all tree radii equal 17/4 in explicit window      CLOSED hand
 +-- TREE.F2.C exactly six origin-incidence profiles           CLOSED hand, exhaustive
 |      |
 |      +-- TREE.12, TREE.03, TREE.04 full completions         CLOSED hand
 |      +-- TREE.02.P point-only central contact               CLOSED hand
 |      +-- TREE.02.E shared edge -> endpoint path             CLOSED reduction; capacity OPEN
 |      +-- TREE.11 exact side/vertex fan or path endpoints    CLOSED reduction; capacity OPEN
 |      |
 |      +-- P.ALL entire staggered path + FIVE extra squares  OPEN
 |      +-- Y.ALL entire side/vertex fan + FOUR extra squares OPEN
 |
 +-- CYCLIC all positive components contain cycles            OPEN sharp global cover
 |
G2.O3.3 / O4 all full physical completions sharply covered     OPEN
G2.O5 / G2.X / G4 unrestricted radius                         BLOCKED
G5 every unrestricted equality packing                       OPEN/BLOCKED
G6 independent full audit                                    NOT COMPLETED
G7 Lean standard-kernel / Palomar replay                      NOT STARTED
G8 public theorem and registry integration                   NOT STARTED
```

**Explicit window:** the tree reduction assumes 79/40<=R<=sqrt(Q). The established n=8 lower bound can supply the first inequality after deleting a square, with its existing proof dependencies. An independent table-free proof must establish this coarse window separately. Capacity theorems stated directly at q=17/4 do not need that dependency, but their universal tree application does.

**Graph/certificate distinction:** the <=19-term planar translational body stress, separate angular witness, and <=27-atom physical force/torque incidence certificate are not automatically the same. Planarity of the contact-point incidence graph does not imply a planar positive body-pair graph. Tree/bridge statements refer to the selected positive body-pair graph. Zero-stress physical contacts remain obstacles.

**Strict-normal convention:** at every point-only vertex/vertex contact, PHYSICAL_CONTACT_STRESS.md chooses a normal strictly exposing the common point in both squares. The new TREE.02.P theorem uses this selected certificate. Arbitrary non-strict physical equilibria are not excluded by that theorem; the opposite-slider path is an explicit regression control.

## G0 — Physical semantics, upper bound and falsification [CLOSED hand; window import explicit]

### G0.1 Exact physical model
- [x] Four vertices c+(epsilon*u+eta*v)/2 with orthonormal u,v.
- [x] Circle containment is equivalent to the four corner bounds; maximum squared norm is |c|^2+1/2+|c.u|+|c.v|.
- [x] Pairwise physical nonoverlap is the exact separating-axis disjunction from either square, with equality and multiple owners permitted.
- [x] Centers are at Euclidean distance >=1 via disjoint open inscribed half-radius disks. This alone does not imply coordinate separation or solve nine-square capacity.

### G0.2 Exact attainment and mandatory negative controls
- [x] HAND_PROOF.md gives the exact Q construction.
- [x] NONRIGID_WITNESS.md and NO_GLOBAL_ORTHOGONAL_FRAME.md retain true independently rotated and oblique-only equality examples.
- [x] TWO_STACK_SHARP_EQUALITY_WITNESS.md and NONSTRATIFIED_PARALLEL_NINE.md reject blanket residual-class exclusion and universal row stratification.
- [x] CENTER_RELAXATION_COUNTEREXAMPLE.md and CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md show the need for actual square geometry and all nine bodies.
- [x] UNRESTRICTED_THREE_SQUARE_CAP.md includes a capless Q witness, so universal sharp-cap extraction is false at equality.
- [x] TREE_FINITE_VALIDATION.md retains nonaligned/branching positive tree cores below Q and three extra squares on one side of a staggered row. Completion, not core impossibility, is required.
- [x] check_origin_pockets.py retains a non-strict-normal opposite-slider equilibrium: the strict-normal point-contact argument must not be applied to every possible stress certificate.

### G0.W Lower-radius input
- **W.1 EXPLICIT IMPORT:** cite the established n=8 theorem and its deletion implication when using the tree window.
- **W.2 OPEN for an independent all-hand proof:** establish R>=79/40 for nine squares without that imported proof dependency.
- No tree reduction erases this prerequisite.

## G1 — Analytic terminal inequalities [CLOSED hand at stated hypotheses]

### G1.T1 Signed 4+3 and four-anchor stresses
- [x] Long/short spans, matched perpendicular gaps of either sign, all-angle orientation penalty and exact weights 23/9 give q>=Q.
- [x] Equality pins four stressed endpoints and forces the seven chain frames to align; free squares may rotate.
- Sources: FOUR_ANCHOR_STRESS.md, PAIRED_FOUR_ANCHOR_STRESS.md, SIGNED_MATCHED_CHAIN_STRESS.md.
- **Scope:** no universal extraction of those chains or endpoint gaps is assumed.

### G1.T2 Grid, projection-cap and fixed-owner dual
- [x] Rotated projection-separated cap row: ORIENTATION_STABLE_SEVEN_ANCHOR.md.
- [x] Four-corner grid spans force q>=9/2: GRID_FOUR_CORNER_STRESS.md.
- [x] Fixed true-owner center elimination: SEPARATOR_GRAPH_CONVEX_DUAL.md. Exact attainment at a minimizer certifies its unknown q0, not q0>=Q by itself.

### G1.T3 Physical cap, every-direction strip, solid row
- [x] **CAP.1–2:** all-angle clipped-section estimate and sharp three-square cap with outer centers (+/-1,15/16), no coordinate-separation premise.
- [x] **CAP.3:** every q<Q nine-square packing has >=5 squares meeting |y|<7/16 in every direction.
- [ ] **CAP.4:** turn this global necessary condition into a sharp contact/completion inequality or exhaustive alternative. Projection antichains are not automatically physical rows.
- [x] **ROW.1–2:** every five-square physical completion of a SOLID 4x1 row forces q=Q.
- [x] **ROW.3:** mixed four-versus-three seam terminal without ordering assumptions on the three.
- [ ] **ROW.4:** derive these hypotheses or another sharp terminal from unrestricted Packing; a staggered path is not solid.
- Sources: UNRESTRICTED_THREE_SQUARE_CAP.md and SOLID_FOUR_ROW_UNRESTRICTED_NINE.md.

### G1.T4 New origin/quadrant and radial-pocket capacities [CLOSED hand; audit pending]

Sources: THREE_VERTEX_ORIGIN_CAPACITY.md and RADIAL_SECTOR_POCKET_CAPACITY.md.

- [x] **V.1:** an origin-vertex quadrant excludes any other center inside it except the two outer axial points at radius 3/2, in D_(17/4).
- [x] **V.2:** three vertex-origin squares confine all extra center directions to gaps totaling pi/2 and their radii to [1/sqrt(2),3/2]. Consecutive directions require >pi/6. At most five extra squares fit: TREE.03 closed.
- [x] **P1:** a radial terminal S(e) screens every other square strictly from e.x>=2. Together with a central side [0,e], its entire positive ray is a physical barrier.
- [x] **P2:** a right-angle wedge bounded by two radial terminals holds only the origin-vertex unit square filling the wedge.
- [x] **P3:** an acute screened wedge holds no square. Widening comparison to a right angle is justified pointwise; no packing deformation is assumed.
- [x] **P4:** a screened wedge with angle pi/2 through 2 arctan(2) holds at most two squares, via exact square support and two center boxes of diameter <1.
- [x] **P5:** distinct radial terminals require angular separation >=2 arctan(1/2).
- **Limit:** a center direction in a gap is not enough by itself. The actual ray barrier must prove that the entire added square stays in the wedge.

## G2.C — Entire common-coordinate-separable class [CLOSED hand]

- [x] **C0:** rank-product injection, 3x3 grid stress and no-five-chain bound force a four-chain.
- [x] **C1:** four-chain shadow and inner-pair overlap.
- [x] **C2:** every large-zigzag branch excluded; no old 4x3 zigzag gate remains open.
- [x] **C3:** signed 4+3 terminal; residual complement has vertical rank stacks (4,1) or (3,2).
- [x] **C3.b:** FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md closes (4,1).
- [x] **C3.c:** a five-element matching and singleton split turn (3,2) into perpendicular signed 4+3 chains.
- [x] **C4:** COORDINATE_SEPARABLE_NINE_COMPLETE.md assembles sharp radius and necessary equality skeleton within this explicit common-frame class.

Do not reopen solved C cases for small-constant improvements. The global-frame counterexample prevents treating C as unrestricted Packing.

## G2.O3.0–O3.1 — Unrestricted physical stress [CLOSED hand necessary reductions]

### O3.0.2 Minimize, select physical contacts, obtain exact stress
- [x] Compact center/frame sublevel sets and finite closed SAT conditions give a global minimizer from any q<Q packing.
- [x] Strictly separate physically noncontacting pairs; active positive terms belong to true physical contacts.
- [x] Dilation supplies regularity and normalized nonnegative conic multipliers; no abnormal multiplier or optimizer premise.
- [x] <=19 fixed-frame terms suffice and the center dual attains q0. Components have >=2 circle-loaded bodies and can be normalized individually.
- Source: SPARSE_MINIMIZER_STRESS.md.

### O3.1a–g Physical, planar and radial structure
- [x] PLANAR_STRESS_CORE.md planarizes the translational support with loaded bodies externally incident and bounded degree-two paths.
- [x] ROTATION_STATIONARY_STRESS.md gives a separate smooth angular certificate; no absolute-value cusp differentiation.
- [x] PHYSICAL_CONTACT_STRESS.md gives genuine shared application points, joint force/torque and a planar contact-point incidence representation, <=27 atoms.
- [x] Unloaded two-force square-ended transmitter reserves are 0,1,sqrt(2),2 at q<=Q.
- [x] RADIAL_BRIDGE_AND_LEAF_REDUCTION.md makes every positive bridge radial, covers bridges by <=4 central circle-clear bodies, and gives S/D loaded-leaf formulas.
- [x] At off-origin point-only vertex contacts choose a strict normal not radial, so such positive contacts cannot be bridges. At origin, the chosen normal is still strictly exposing, but radiality is automatic.
- **Limit:** nonbridge forces need not be radial; incidence planarity is not body-graph planarity.

## G2.O3.2 — Exhaustive tree/cyclic split [PARTIAL]

Either some selected positive component is a tree, or every positive component contains a cycle. Retaining one component never discards the other physical squares; all nine remain in every capacity theorem.

### TREE.F1 Every tree body localized [CLOSED hand]
Source: TREE_BODY_LOCALIZATION.md.

- [x] All unloaded tree bodies are central; at most four occur.
- [x] Every loaded tree body has a single radial contact point and S/D geometry, even at degree two.
- [x] A radial outward support point of a body avoiding zero has norm >1.
- [x] Every origin-avoiding unloaded body is one side-normal transmitter to a single S terminal, with incoming origin-containing neighbor(s).
- [x] At least one unloaded body contains zero; a unique such root gives a subdivided star.

### TREE.F2 Radius quantization and six-case cover [CLOSED hand]
Source: TREE_RADIUS_QUANTIZATION.md.

- [x] **F2.I:** no origin-interior unloaded root in the window; exhaustive short-arm side/vertex analysis, with the prior star theorem.
- [x] **F2.S/V:** side-interior or vertex incidence forces A=sqrt(R^2-1/4)-1=1.
- [x] **F2.R:** all positive tree components therefore have R^2=17/4, all unloaded bodies boundary-origin, all loaded bodies S(e).
- [x] **F2.C:** tangent cones and star exclusion give 2s+v<=4 and s+v>=2, hence exactly six original incidence profiles. Continuous parameters and boundary sliders are not dropped.

### TREE.F3 Six original completion cases, updated

| Case | (s,v) | Exact current disposition |
|---|---|---|
| TREE.20 | (2,0) | OPEN capacity; entirely included in P.ALL |
| TREE.11 | (1,1) | CLOSED normal-form reduction to Y.ALL or aligned P endpoints; capacity OPEN |
| TREE.12 | (1,2) | CLOSED hand whole completion: cardinal cage <=8 |
| TREE.02 | (0,2) | Point-only subtype .P CLOSED; shared-edge subtype .E maps to P.ALL |
| TREE.03 | (0,3) | NEW CLOSED hand whole completion: angular annulus <=8 |
| TREE.04 | (0,4) | CLOSED hand whole completion: central 2x2 block <=8 |

Sources: TREE_FINITE_COMPLETIONS.md, THREE_VERTEX_ORIGIN_CAPACITY.md, TREE02_POINT_CONTACT_COMPLETION.md, REMAINING_TREE_TWO_FAMILY_REDUCTION.md.

#### TREE.12 and TREE.04 [CLOSED]
- [x] The cardinal cage at centers (+/-3/2,0),(0,+/-3/2) leaves <=4 extra arbitrary squares; actual square support excludes diagonal-center pockets.
- [x] A central [-1,1]^2 block leaves only four cardinal extra centers with forced frames.
- [x] TREE.12 forces the cage via origin cones and load balance; TREE.04 forces the block. Both count every unstressed square.

#### TREE.03 [NEW CLOSED]
- [x] Three right-angle cones leave <=3 gaps totaling pi/2.
- [x] Every other center lies in those gaps, with radius in [1/sqrt(2),3/2].
- [x] Center distance >=1 forces angular separation >pi/6 inside a gap. Six extras would need more angle than exists.
- **Exit:** at most eight TOTAL physical squares, independent of all extra orientations or contact graphs.

#### TREE.02.P point-only contact [NEW CLOSED]
- [x] Strict common normal at zero forces two positive S loads at each root; four distinct terminal rays occur.
- [x] Whole-square radial screens trap every added square in one of the two complementary gaps.
- [x] Terminal separation gives the smaller gap >=2 arctan(1/2); the larger is <=2 arctan(2).
- [x] Acute gap is empty; moderately obtuse gap has <=2 squares; the right/right endpoint has <=1 each. Six core bodies plus <=2 extra gives <=8 total.
- **Premise control:** non-strict origin-normal arbitrary equilibrium is not the selected strict-normal certificate. Preserve the exact negative control.

#### TREE.02.E shared-edge contact [CLOSED reduction; capacity OPEN]
- [x] The roots are [-1,0]x[0,1] and [0,1]x[0,1], up to isometry.
- [x] Possible loaded directions are E,N,W. Circle-force balance forbids positive N, leaving equal opposing E/W terminals.
- [x] This is exactly P with tau_1=tau_2=1/2 (or reflection). A zero-weight physical N square may still appear in the completion.

### TREE.F4 Exactly two remaining master families [CLOSED exhaustive reduction; capacities OPEN]

Source: REMAINING_TREE_TWO_FAMILY_REDUCTION.md. No new graph types are being added as smaller angular windows. Every survivor of the six-case inventory is included in P or Y with all parameters retained.

#### P.ALL — staggered four-square path plus FIVE arbitrary squares [OPEN]

Four fixed axis-aligned centers:

    (-3/2,0), (-1/2,tau_1), (1/2,tau_2), (3/2,0),
    tau_1,tau_2 in [-1/2,1/2].

- [x] **P.0 coverage:** TREE.20, TREE.02.E and aligned TREE.11 endpoint configurations belong here. Allowing other endpoint profiles only enlarges the capacity target safely.
- [x] **P.flat:** tau_1=tau_2=0 is closed by the solid-row theorem.
- [ ] **P.1 full capacity:** prove no five other arbitrarily oriented, physically disjoint unit squares fit D_(17/4) with any member of this entire parameter square.
- [ ] **P.2 whole-family proof:** retain true oblique SAT axes and actual square supports; derive a global capacity or a finite exhaustive structural argument, not a sequence of offset bins.
- **Negative control:** three extras can fit on one side of a staggered row. Independent two-per-side bounds are false.

#### Y.ALL — side/vertex fan plus FOUR arbitrary squares [OPEN]

Parameters 0<alpha<1, 0<theta<pi/2; e=(0,1), u=(cos(theta),-sin(theta)), v=(-sin(theta),-cos(theta)). The five-square skeleton is

    H=[-alpha,1-alpha] x [0,1],
    K={a u+b v:0<=a,b<=1},
    S(e), S(u), S(v),  with center(S(d))=(3/2)d.

- [x] **Y.0 exact TREE.11 normal form:** H's only radius-one radial support is e, K's are u,v. Connectivity forces the origin H--K edge. Equilibrium gives terminal force ratios sin(theta), cos(theta). No other positive TREE.11 topology is omitted.
- [x] **Y.boundary:** theta=0 or pi/2 removes one positive load and yields a member of P; do not lose these side-contact boundaries.
- [ ] **Y.1 full capacity:** prove no four additional physical unit squares fit the disk with any admissible alpha,theta skeleton.
- [ ] **Y.2 whole-family sharpness:** include all actual corner, wedge and zero-weight-contact restrictions. A real nonaligned five-body core exists, so the core alone cannot be excluded.

**TREE.ALL exit:** P.ALL and Y.ALL both closed, together with the six-case/strict-normal/window prerequisites. This has not been achieved.

### CYCLIC — every selected component has a cycle [OPEN]

- [ ] **CY.1 exhaustive cover:** geometrically classify all cyclic physical positive components with bridges, loaded bodies, actual junctions and unstressed completions, or bypass classification by a universal inequality.
- [ ] **CY.2 sharp bound:** prove q0>=Q for every full nine-square realization. The existence of sparse multipliers only certifies q0, not the desired lower bound.
- [ ] **CY.3 equality/limits:** retain zero weights, multiple circle contacts, nonstratified and oblique-only known Q examples.
- **Nonclaim:** no tree theorem is imported onto a nonbridge cycle edge. A finite labelled graph syntax is not a sharp global proof.

### O3.3 / O4 — global exhaustiveness and sharpness [OPEN]
- [x] Finite tree cover and P/Y survivor reduction are complete as necessary implications.
- [ ] Sharp capacities P.ALL and Y.ALL and the complete CYCLIC branch remain missing.
- [ ] A universal every-direction cap/strip/contact-capacity inequality is an alternative that could close several branches together; no such implication is currently proved.
- [ ] Equality zero sets must be derived rather than assumed; free squares may have oblique separators.

## G2.X / G4 — Assemble unrestricted optimality [BLOCKED]

- [x] Any q<Q packing yields a compact unrestricted minimizer with a selected physical stress.
- [ ] Include the declared lower-window input and prove TREE.ALL plus CYCLIC, or a universal sharp alternative.
- [ ] Remove all graph/row/frame hypotheses except those genuinely derived from original Packing.
- [x] The exact construction attains Q.
- [ ] Transfer the completed lower bound to R*=sqrt(Q) and the public Optimum/Packing statements.

## G5 — All equality packings [PARTIAL]

- [x] Conditional stratified and signed 4+3 necessity/converse domains are in STRATIFIED_EQUALITY_FAMILY.md and SIGNED_MATCHED_EQUALITY_FAMILY.md.
- [x] Every common-coordinate equality packing enters a signed skeleton after frame choice.
- [x] Cap/solid-row conditional equality anchors are known; the capless example rejects a global cap-only normal form.
- [ ] Once unrestricted optimality is proved, apply stress necessity to EACH original Q packing, not merely a replacement minimizer.
- [ ] Derive every surviving cyclic equality skeleton, free-parameter domain and converse; use the actual congruence convention and preserve continuous freedoms.

## G6 — Independent audit and exact executions [NOT COMPLETED]

- [ ] Independently audit general stress regularity, genuine shared-point angular terms, strict-normal selection and the graph distinctions.
- [ ] Audit TREE.F1/F2 and earlier cardinal-cage/block proofs.
- [ ] Audit the new three-vertex annular argument, physical radial screens, acute-pocket widening, obtuse-pocket exact center box and strict-normal endpoint-load implication.
- [x] **Finite executed regression only:** check_origin_pockets.py at source 607d51b was matched to its Git blob and SHA-256 and run. ORIGIN_POCKET_EXACT_CHECK.json records 1,716 rational checks, sharp physical attainment, a strict-normal six-body core and shared-edge/non-strict-normal controls. It is not an all-angle proof or independent audit.
- [x] Earlier check_finite_tree_cases.py and its executed report remain reproducible with their original limited scope; they are not counted again as new results.
- [ ] Independently verify all source-to-theorem dependencies and preserve the n=8 window dependency.
- [x] Commit/log completed arguments with UTC provenance in ORIGIN_POCKET_PROGRESS.md and the finite ledger; do not count unproved numerical observations as gates.

## G7 — Standard-kernel Lean / Palomar proof [NOT STARTED]

Formalize original physical square semantics, exact construction, compactness/stress and the ACTUAL completed all-case sharp proof; then equality necessity/converse. Compile, inspect axioms/imports, and independently replay. No native-kernel bypass, admitted theorem, opaque external certificate or unvalidated generated table.

## G8 — Integration [NOT STARTED]

Integrate n=9 into public Optimum/radius/packing registries and Challenge mirror; update geometric documentation and equality domains; check n=1–8 regressions; retain source hashes and UTC provenance. Finalize PR only after the advertised full theorem and verification exist.

## Immediate execution contract

1. The unfinished tree target is now exactly **P.ALL or Y.ALL**, with full parameter ranges. Do not reclassify arbitrary tree topologies or reopen TREE.03/TREE.02.P for minor constants.
2. Prove a complete capacity inequality for one of those families, or one invariant for both; keep all five/four additional physical squares.
3. Keep **CYCLIC** explicitly open. No percentage of tree rows is a global proof percentage.
4. Keep strict versus non-strict point-contact certificates explicit and retain negative controls.
5. Commit each finished general argument promptly and log precise quantifiers, source/UTC provenance, executed evidence and the unchanged global blocker.
6. No independent audit, Lean or CI claim before it is actually performed. The unrestricted theorem is NOT complete at this checkpoint.
