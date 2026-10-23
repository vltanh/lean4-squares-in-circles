# n=9: deep ticked roadmap — P/Y completions and exhaustive coarse cyclic cells

**Branch:** `research/nine-tablefree-hand`; **PR:** #11, draft.
**Checkpoint:** 2026-10-23 quadrant/block continuation, starting from head `59d0c95092a01a575a3fc078ab5c6db54107d4fc`.

**The unrestricted lower bound and complete global equality classification are still OPEN.** The common-coordinate-separable theorem is hand-proved. The tree branch has an exhaustive six-profile origin-incidence classification; its survivors reduce to the two full completion families **P.ALL** and **Y.ALL**, neither capacity theorem yet proved. The cyclic branch now has an exhaustive **coarse block-size/bridge-count partition of 58 cells**. Exactly one cell, C1.3.b0, is excluded in the stated radius window; the other 57 sharp cell theorems remain open. Coarse enumeration is NOT a completed geometric classification or a guarantee of easy closure.

New results in this checkpoint are the all-angle **quadrant unavoidable-point/capacity-one theorem**, a loaded-endblock restriction, the finite cyclic block budget, and the loaded-clique/isolated-triangle exclusion. They do not close P.ALL or Y.ALL. All general arguments are hand manuscripts pending independent audit. No unrestricted theorem, Lean compilation, CI, or proof-completion percentage is claimed.

## Canonical sources and status vocabulary

- [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md): all 58 coarse cyclic cells individually ticked; complete physical hypotheses retained.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): original six tree cases and their P/Y disposition.
- [G2_SUBGATES.md](G2_SUBGATES.md): live mathematical ledger.
- [QUADRANT_BLOCK_PROGRESS.md](QUADRANT_BLOCK_PROGRESS.md): current UTC commits, exact scopes, executed regressions and unchanged blockers.
- [ORIGIN_POCKET_PROGRESS.md](ORIGIN_POCKET_PROGRESS.md), [PROGRESS_LEDGER.md](PROGRESS_LEDGER.md): preceding append-only provenance.
- [QUADRANT_BLOCK_EXACT_CHECK.json](QUADRANT_BLOCK_EXACT_CHECK.json): pinned finite exact execution; not a universal proof.

**[x] CLOSED hand** means the exact stated implication has a written analytic argument with its hypotheses and boundaries; independent audit and Lean verification are separate gates. **[ ] OPEN** means the general argument has not been established. **CLOSED reduction** is a necessary structural theorem, not automatically a sharp bound. **REJECTED** means an exact witness refutes a proposed shortcut. Historical versions remain in Git.

## 0. Target, quantifiers, graph distinctions and global map

Put Q=1105/256 and q0=17/4. The exact construction attains Q. The target is:

> **T9:** for every family of nine independently oriented closed unit squares with pairwise disjoint open interiors contained in a disk of radius R, one has R^2>=Q.

No common square frame, common pairwise separating axes, central square, row structure or prescribed stress graph belongs to the original hypothesis. All tangencies and equality degeneracies are retained. Every selected stressed component is studied **with all remaining physical squares**, including other components and zero-stress contacts.

```text
[x] G0 exact model / attainment / negative controls
[x] G1 short signed/grid/cap/row/pocket tools, conditional
[x] G2.C entire common-coordinate-separable class
[x] G2.O3.0 compact minimizer -> true physical stress
[x] G2.O3.1 physical force/torque and bridge reductions
 |
 +-- TREE.F1/F2 all trees: q0=17/4 and six incidence profiles [x]
 |      +-- TREE.12, TREE.03, TREE.04 full completions      [x]
 |      +-- TREE.02.P point-only completion                [x]
 |      +-- all remaining tree geometries -> P or Y        [x] reduction
 |      +-- P.ALL all staggered paths plus five squares    [ ] OPEN
 |      +-- Y.ALL all side/vertex fans plus four squares   [ ] OPEN
 |
 +-- CY.BLOCK exact 21 profiles / 58 coarse cells           [x] coverage only
 |      +-- CY.LOAD unloaded appendage and loaded clique   [x] necessary/exclusion
 |      +-- C1.3.b0 selected isolated triangle              [x] excluded in window
 |      +-- remaining 57 full physical cells               [ ] OPEN sharpness
 |
 +-- QCAP quarter-disk capacity one                        [x] all-angle tool
 |      +-- QCAP routing for P/Y/global completions         [ ] OPEN
 |
[ ] G2.O4/O5 all physical completions sharply bounded
[ ] G2.X/G4 unrestricted T9 and public radius statement
[ ] G5 global equality necessity and sufficiency
[ ] G6 independent full mathematical audit
[ ] G7 standard Lean kernel / Palomar replay
[ ] G8 public integration and final PR closure
```

### G0.W Explicit lower-radius window

Tree-radius quantization and the new loaded-clique exclusion assume **79/40<=R<=sqrt(Q)**. The established n=8 result can give the lower bound after deleting one square, with its existing proof dependencies. A standalone all-hand n=9 proof must establish that coarse window independently. Capacity theorems stated directly in D_(17/4), including QCAP, do not need the n=8 input themselves.

- [x] **W.1 declaration:** the radius-window premise is explicit in every dependent tree/clique theorem.
- [ ] **W.2 source-level assembly:** cite the actual existing n=8 lower-bound theorem and its exact deletion implication in the final dependency graph.
- [ ] **W.3 optional independent hand replacement:** prove R>=79/40 without that prior computational dependency if standalone table-freedom is required.

### Distinctions every proof must preserve

1. The <=19-term planar translational body support and <=27-atom physical torque-balanced contact-incidence certificate are different constructions. No unproved simultaneous 19-term planar-body/torque assertion is used.
2. The selected positive **body-pair graph** need not be planar; its contact-point incidence representation is planar. Block/cycle statements below concern the simple body-pair graph.
3. A positive bridge is not every physical contact. Tree radiality cannot be applied to a nonbridge cycle edge.
4. A finite block-size profile is not a full graph topology and is not a finite list of continuous square poses. Every unchecked cell still quantifies over all of those.
5. A stressed component may have fewer than nine vertices. Removing its other physical squares would destroy the n=9 quantifier.

---

## G0 — Exact geometry and falsification controls

### G0.1 Physical encoding [CLOSED hand]
- [x] **G0.1.a** A unit square has corners c+(epsilon*u+eta*v)/2 for orthonormal u,v.
- [x] **G0.1.b** Its maximum squared corner radius is |c|^2+1/2+|c.u|+|c.v|; corner containment gives whole-square containment by convexity.
- [x] **G0.1.c** Physical nonoverlap is the exact finite own-axis separating-axis disjunction from either square, equality allowed.
- [x] **G0.1.d** Disjoint open half-radius inscribed disks imply center distances >=1. This is necessary, not sufficient for full-square packing.

### G0.2 Attainment [CLOSED hand]
- [x] **G0.2.a** HAND_PROOF.md gives an exact Q packing.
- [x] **G0.2.b** The nonrigid and oblique-pair witnesses retain genuine independent rotation at Q.
- [x] **G0.2.c** TWO_STACK_SHARP_EQUALITY_WITNESS.md gives an equality packing in the residual coordinate two-stack class, with a perpendicular signed 4+3 terminal.

### G0.3 Mandatory negative tests [CLOSED negative]
- [x] Global common-coordinate separation is false: NO_GLOBAL_ORTHOGONAL_FRAME.md.
- [x] Global stratification is false even for all-parallel equality packs: NONSTRATIFIED_PARALLEL_NINE.md.
- [x] A central open square is not universal; retain boundary-origin configurations.
- [x] Center-radius/L-infinity separation alone is insufficient: CENTER_RELAXATION_COUNTEREXAMPLE.md.
- [x] Eight physical squares can have perpendicular disjoint four-chains below Q: CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md. The ninth body is essential.
- [x] Some Q packings have no sharp triple cap in any direction: UNRESTRICTED_THREE_SQUARE_CAP.md. Do not impose cap extraction at equality.
- [x] Nonaligned and branching positive trees at q0 exist with fewer than nine bodies: TREE_FINITE_VALIDATION.md. The needed theorem is completion capacity, not false core infeasibility.
- [x] Three squares can occupy one side of a staggered P path. Independent two-per-side capacity is false.
- [x] A non-strict-normal opposite-slider equilibrium must not be covered by a theorem using the selected strictly exposing point-contact normal.
- [x] **NEW:** even center-radius plus exact inscribed-disk clearance from P's four physical obstacles plus pairwise unit center distances admits five extra centers. The exact witness is in QUADRANT_BLOCK_PROGRESS.md and the committed regression report. These centers are NOT a full square packing.
- [x] **NEW:** a universal 45-degree angular separation of extra square centers is false: aligned centers (5/4,+/-1/2) fit q=65/16 and have angle cosine 21/29>1/sqrt(2).

---

## G1 — Terminal inequalities and physical capacity tools

### G1.T1 Signed 4+3 and four-anchor stress [CLOSED hand, conditional]
- [x] Endpoint long/short spans and true perpendicular gaps of either sign give q>=Q through exact weights 23/9 and an all-angle square penalty.
- [x] Equality pins the four stressed outer squares; seven-chain width saturation forces their common frame.
- Sources: FOUR_ANCHOR_STRESS.md, PAIRED_FOUR_ANCHOR_STRESS.md, SIGNED_MATCHED_CHAIN_STRESS.md.
- [ ] **T1.EXTRACT:** unrestricted minimizers need not yet be known to supply those hypotheses.

### G1.T2 Grid, projection cap and center dual [CLOSED hand, conditional]
- [x] Four-corner grid spans force q>=9/2: GRID_FOUR_CORNER_STRESS.md.
- [x] Rotated projection-disjoint cap rows: ORIENTATION_STABLE_SEVEN_ANCHOR.md.
- [x] Exact center elimination after true separator owners/orientations are fixed: SEPARATOR_GRAPH_CONVEX_DUAL.md.
- Exact dual attainment at a minimizer certifies its unknown q0; it is not the desired inequality q0>=Q by itself.

### G1.T3 Oblique-safe cap, central strip and solid row [CLOSED hand at scope]
- [x] **CAP.1–2** All-angle clipped-section theorem and exact three-square cap rigidity in D_Q above y=7/16, without coordinate-separation hypotheses.
- [x] **CAP.3** Every q<Q nine-square packing has >=5 squares meeting the central strip |y|<7/16 in every direction.
- [ ] **CAP.4** Convert this necessary condition into a universal sharp contradiction or complete alternative. Projection antichains do not automatically give physical rows.
- [x] **ROW.1–2** Every completion of a SOLID 4x1 row by five physical squares forces q=Q; other squares may rotate.
- [x] **ROW.3** Mixed four-versus-three seam terminal without horizontal ordering among the three.
- [ ] **ROW.4** Derive the seam/solid-row hypothesis or another terminal from a general minimizer. Staggered P is not a solid row.

### G1.T4 Origin and screened-sector capacities [CLOSED hand]
- [x] **V.1** A vertex-origin quadrant excludes every other center in that quadrant except its two radius-3/2 outer axis endpoints at q0.
- [x] **V.2** Three vertex-origin squares leave annular center gaps totaling pi/2. Required separation >pi/6 excludes six extras: total<=8. THREE_VERTEX_ORIGIN_CAPACITY.md.
- [x] **POCKET.1** Radial terminal S(e) screens other squares from e.x>=2; a central side [0,e] plus that terminal blocks the entire positive ray physically.
- [x] **POCKET.2** A right-angle screened pocket has its unique origin-vertex square; an acute screened pocket has none.
- [x] **POCKET.3** A screened wedge of opening pi/2 through 2 arctan(2) holds at most two arbitrary squares.
- [x] **POCKET.4** Distinct S terminals have minor angular separation >=2 arctan(1/2).
- Source: RADIAL_SECTOR_POCKET_CAPACITY.md.
- [ ] **POCKET.ROUTING** In every application, prove the WHOLE extra square lies in the screened wedge; its center direction alone is insufficient.

### G1.T5 NEW unrestricted quadrant unavoidable point [CLOSED hand, audit pending]

Source: [QUADRANT_UNAVOIDABLE_POINT.md](QUADRANT_UNAVOIDABLE_POINT.md), commit c02fa61.

- [x] **QCAP.1.a** In quadrant-adapted square axes u=(a,b),v=(-b,a), a>=b>=0, set w=a+b,d=a-b,t=c.u,z=c.v. Physical quadrant containment and exact corner radius imply w-1/2<=t<w+1/2 and d-1/2<=z<d+1/2.
- [x] **QCAP.1.b** All four bounds are strict for a non-axis-aligned square, so it contains (1,1) in its open interior. In the aligned case (1,1)-epsilon*(1,1) lies in the open interior for sufficiently small epsilon>0.
- [x] **QCAP.2** Two unit squares cannot both lie wholly in one origin-centered closed quadrant of D_(17/4), no terminal obstacles or common pairwise separator assumption needed.
- [x] **QCAP.3** Any nine-square packing in that disk has, in every perpendicular frame, at least five squares whose open interiors meet at least one coordinate line. Otherwise at least five squares lie wholly in four quadrants.
- [ ] **QCAP.P** Show how this theorem controls every added square of every P completion, INCLUDING squares crossing quadrant boundaries. Not proved.
- [ ] **QCAP.Y** Give the corresponding full-family routing/capacity implication for Y. Not proved.
- [ ] **QCAP.GLOBAL** Combine the unavoidable-point and all-direction conditions into a sharp unrestricted invariant. Not proved.

**Do not claim:** QCAP has closed P.ALL or Y.ALL. Their added squares need not individually be contained in the selected quadrants.

---

## G2.C — Whole common-coordinate-separable class [CLOSED hand]

- [x] **C0** Rank-product injection, no five-chain, and strict 3x3 grid bound force a four-chain.
- [x] **C1** Four-chain shadow and inner-pair overlap.
- [x] **C2** Entire large-zigzag branch excluded; no residual old 4x3 zigzag case remains.
- [x] **C3.a** Signed matched 4+3 chains give the sharp bound.
- [x] **C3.b** A five-square complement without a horizontal triple has exactly two vertical rank stacks, (4,1) or (3,2).
- [x] **C3.c** The crossed-four-chains-plus-ninth theorem excludes (4,1).
- [x] **C3.d** Elementary five-element matching and a finite singleton split turn (3,2) into perpendicular signed 4+3 chains.
- [x] **C4** COORDINATE_SEPARABLE_NINE_COMPLETE.md assembles the whole-class theorem and necessary equality skeleton.

The nine square frames can differ in C; the pairwise separating frame is common. Its absence in some equality packs means C is not unrestricted Packing. Do not reopen solved C subcases for minor numerical improvements.

---

## G2.O3.0–O3.1 — Unrestricted physical stress [CLOSED hand necessary reductions]

### O3.0.2 Minimizer and exact stress
- [x] Normalize center, use compact frames/centers and finite closed SAT alternatives to obtain a global minimizer from any q<Q packing.
- [x] Strictly separate noncontacting physical pairs so positive active edges are genuine contacts.
- [x] An explicit dilation direction gives active-constraint regularity and nonnegative normalized conic multipliers without an optimizer premise.
- [x] Fixed-frame center/radius stress has <=19 positive terms and exactly attained center dual; every positive component has >=2 loaded bodies and may be normalized separately.
- Source: SPARSE_MINIMIZER_STRESS.md.

### O3.1a–g Planarity, physical torque and radial bridges
- [x] PLANAR_STRESS_CORE.md gives planarized translational support, externally incident loaded bodies and short unloaded transmission paths.
- [x] ROTATION_STATIONARY_STRESS.md supplies a separate smooth angular certificate; no absolute-value cusp differentiation.
- [x] PHYSICAL_CONTACT_STRESS.md puts force/torque at actual shared points with <=27 physical atoms and a planar contact-point incidence network.
- [x] Unloaded two-force square transmitters use opposite sides or vertices, with square-ended reserves 0,1,sqrt(2),2 at q<=Q.
- [x] RADIAL_BRIDGE_AND_LEAF_REDUCTION.md gives radial bridge cuts, <=4 central circle-clear bridge-cover bodies and exact S/D loaded leaves.
- [x] Strict point-only vertex/vertex contact normals are selected; off-origin ones may be chosen nonradial and then cannot be positive bridges. At origin the strictly exposing convention still matters.
- [ ] These necessary reductions do not provide the uniform q>=Q inequality for every full physical completion.

---

## G2.O3.2.TREE — Exhaustive surviving families P and Y [PARTIAL sharpness]

### TREE.F1–F2 Universal tree reduction in the explicit window [CLOSED hand]
- [x] Every unloaded tree body is central; there are at most four.
- [x] Loaded bodies have one radial application point and S/D form, even when not leaves.
- [x] An origin-avoiding unloaded body is a single side transmitter to one S terminal, with origin-containing incoming neighbors.
- [x] Origin-interior roots are excluded by the prior star theorem and exhaustive short-arm vertex/side analysis.
- [x] Every side/vertex origin-boundary incidence forces A=sqrt(R^2-1/4)-1=1; hence EVERY tree component has q0=17/4.
- [x] All unloaded bodies then contain origin on their boundaries, all loaded bodies are S(e), and 2s+v<=4 with s+v>=2 yields the six exhaustive incidence profiles.
- Sources: TREE_BODY_LOCALIZATION.md and TREE_RADIUS_QUANTIZATION.md.

### TREE.F3 Original six-profile disposition

| Case | Profile (s,v) | Scope now covered | State |
|---|---|---|---|
| TREE.20 | (2,0) | Full staggered path | [ ] Capacity OPEN in P.ALL |
| TREE.11 | (1,1) | Exact side/vertex fan or aligned endpoint path | [x] normal form; [ ] capacity in Y.ALL/P.ALL |
| TREE.12 | (1,2) | Entire full completion | [x] total capacity <=8 via cardinal cage |
| TREE.02.P | (0,2), point-only central contact | Entire strict-normal selected-contact subtype | [x] capacity <=8 via radial pockets |
| TREE.02.E | (0,2), shared edge | Exact endpoint path | [x] reduction; [ ] capacity in P.ALL |
| TREE.03 | (0,3) | Entire full completion | [x] total capacity <=8 via angular annulus |
| TREE.04 | (0,4) | Entire full completion | [x] total capacity <=8 via central 2x2 block |

Strict-normal point contacts and shared-side boundary contacts are distinct; no endpoint or non-strict witness is silently removed.

### TREE.P — Whole staggered path plus FIVE physical squares [OPEN]

Exact parameter space:

    c1=(-3/2,0), c2=(-1/2,tau1), c3=(1/2,tau2), c4=(3/2,0),
    -1/2<=tau1,tau2<=1/2; all four squares axis-aligned; disk q0=17/4.

- [x] **P.0** Every TREE.20 configuration and shared-edge TREE.02.E, plus aligned TREE.11 endpoints, is included, with all boundary slider values.
- [x] **P.FLAT** tau1=tau2=0 is excluded by the solid-row completion theorem.
- [x] **P.N1 negative** Three added squares can fit on one side of a staggered row. A two-per-side capacity premise is false.
- [x] **P.N2 NEW negative** The center-radius/inscribed-disk/pair-distance relaxation admits FIVE extra centers, even with positive exact clearance from the four root rectangles. Thus that relaxation cannot close P.ALL.
- [ ] **P.1 actual-square routing** Prove a structural property for every additional square, using its exact corners and true SAT axes, not just its center. QCAP is available only after whole-square quadrant containment is established.
- [ ] **P.2 coupled capacity** Show all complementary regions together contain at most four added squares for the entire two-slider range. Any subpartition must be finite and cover all continuous parameters with equality/tangency.
- [ ] **P.3 endpoint reconciliation** Include |tau_i|=1/2 and both same-sign and opposite-sign endpoint contacts; their graph conventions must not alter physical capacity.
- [ ] **P.ALL** No FIVE physical unit squares can complete any such path in D_(17/4).

### TREE.Y — Whole nonaligned fan plus FOUR physical squares [OPEN]

Exact parameter space:

    0<alpha<1, 0<theta<pi/2,
    H=[-alpha,1-alpha] x [0,1],
    u=(cos(theta),-sin(theta)), v=(-sin(theta),-cos(theta)),
    K={a*u+b*v:0<=a,b<=1},
    radial terminal squares S((0,1)), S(u), S(v).

- [x] **Y.0 exact normal form** Every remaining nonaligned TREE.11 component is this five-body fan; its two downward force magnitudes are mu*sin(theta) and mu*cos(theta). At theta=0 or pi/2 it becomes P.
- [x] **Y.N negative** A genuine nonaligned five-body physical tree exists; exclude only completion to nine, not the core itself.
- [ ] **Y.1 complete pocket routing** Describe every added physical square's possible region without assuming a common separating frame. Derive ray/quadrant barriers when needed rather than using only center angles.
- [ ] **Y.2 uniform capacity** Show at most three added squares for every alpha,theta in the full domain, or derive another sharp obstruction for the same whole family.
- [ ] **Y.3 boundary accounting** Reconcile limiting shared-edge cases with P without discarding them or inferring strict-normal assertions for a different contact type.
- [ ] **Y.ALL** No FOUR additional physical unit squares complete any such fan in D_(17/4).

**TREE.ALL exit:** P.ALL and Y.ALL plus the completed cases and declared lower-window input exclude every selected tree component of a hypothetical subcritical nine-square minimizer. Neither P.ALL nor Y.ALL is proved in this checkpoint.

---

## G2.O3.2.CY — Finite coarse cyclic partition [COVER CLOSED; SHARPNESS OPEN]

Sources: [CYCLIC_BLOCK_INVENTORY.md](CYCLIC_BLOCK_INVENTORY.md), [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md).

### CY.BLOCK Exact combinatorial coverage [CLOSED hand]
- [x] **CY.B1** Decompose a selected connected cyclic positive simple body-pair graph into maximal vertex-biconnected cyclic blocks and bridge blocks. The block/articulation incidence graph is a tree.
- [x] **CY.B2** If cyclic block sizes are k_i>=3 and there are b bridges, then n=1+b+sum(k_i-1)<=9.
- [x] **CY.B3** Sorting the k_i yields exactly 21 size profiles and, after fixing b, 58 disjoint cells for the selected component. The counts by number of cyclic blocks are 28,22,7,1.
- [x] **CY.B4** Every cell records n and 9-n physical completion squares; multiple stress components do not license deletion of those other bodies.
- [ ] **CY.B5 missing geometric content** Within each profile, different block adjacencies, contact/load allocations and continuous angles remain. The block table is NOT the missing small sharp geometric classification.

### CY.LOAD Global necessary force restrictions [CLOSED hand]
- [x] **CY.L1 unloaded appendage** A nonempty unloaded positive subgraph whose only external neighbor is one body cannot balance. Sum force equations dotted with c_i-c_b; every internal/boundary positive edge contributes a strictly negative support gap.
- [x] **CY.L2 endblock load** Every endblock has a loaded body other than its articulation. This does not assert a private loaded body in each intermediate block.
- [x] **CY.L3 loaded nonclique** If all loaded bodies pairwise physically touch, their centers have pairwise distance <=sqrt(2). Their centroid and normalized circle-force balance give R^2<=625/162<(79/40)^2. Therefore the loaded subset is not pairwise touching in the declared window.
- [x] **CY.C1.3.b0** One triangle block with no bridges has only three component bodies, all touching; its loaded subset violates CY.L3. The entire cell is excluded, irrespective of the six other physical squares.
- [ ] Triangle blocks WITH bridge attachments, and nonclique larger components, are not closed by that argument.

### CY.CELLS All 58 cells, tracked individually

Every cell is listed with its own checkbox in CYCLIC_CELL_LEDGER.md. The summary below is not a claim that its distinct continuous geometries are solved:

| Cyclic block count | Sorted block-size profiles | Number of bridge-count cells | Sharp status |
|---|---|---:|---|
| 1 | (3),(4),(5),(6),(7),(8),(9) | 28 | C1.3.b0 [x]; other 27 [ ] |
| 2 | (3,3),(3,4),(3,5),(3,6),(3,7),(4,4),(4,5),(4,6),(5,5) | 22 | all [ ] |
| 3 | (3,3,3),(3,3,4),(3,3,5),(3,4,4) | 7 | all [ ] |
| 4 | (3,3,3,3) | 1 | [ ] |

**57 OPEN cells.** A theorem may close multiple cells at once; there is no instruction to launch 57 independent orientation-grid searches. The number is a bookkeeping bound, not a completion percentage or an estimate of remaining difficulty.

### CY.C — Uniform subsubgate contract for EACH open cell

For a cell C=(k_1,...,k_m;b), n=1+b+sum(k_i-1):

- [ ] **C.1 GRAPH** retain every maximal block adjacency and block-cut attachment compatible with C; prove any extra simplification rather than selecting a convenient drawing.
- [ ] **C.2 LOAD** impose true nonnegative circle loads, CY.L1/L2/L3, physical contact points, and force/torque at every body. A nonbridge contact need not be radial.
- [ ] **C.3 GEOMETRY** characterize all actual square orientations/positions satisfying those constraints, or prove an inequality directly over that full set. Avoid splitting into endlessly narrower angle windows.
- [ ] **C.4 COMPLETION** retain all 9-n other squares and every zero-weight physical contact. A small component alone may fit below Q.
- [ ] **C.5 SHARPNESS** prove q>=Q for every full nine-square realization in C, or exclude all such selected components in the radius window.
- [ ] **C.6 EQUALITY** preserve and classify all q=Q realizations, including zero-weight limits and independent free-square rotations, if the final equality theorem needs this cell.

### CY.ALL Parent exit [OPEN]

Finish all open cells' whole-family sharp theorem, or prove one universal inequality handling them without case-by-case geometry. Coarse exhaustive coverage is already established; **sharp coverage is not**. The known exact Q cyclic/oblique examples must survive at equality. A sampled infeasible graph or merely finite SAT syntax does not close the parent.

---

## G2.O3.3 / G2.O4 / G2.O5 — Global coverage and sharp assembly [OPEN]

- [x] **O3.3.T coverage** The tree branch is completely routed to closed cases, P.ALL or Y.ALL.
- [x] **O3.3.C coarse coverage** A selected cyclic component belongs to one of the 58 exact block/bridge cells.
- [ ] **O3.3.SHARP** Supply the missing actual geometric/capacity implications for P.ALL, Y.ALL and all 57 open cyclic cells. This is the substantive missing theorem, not resolved by enumerating their names.
- [ ] **O4.1** Produce exact stresses/support or capacity inequalities valid over whole families and all allowed orientations.
- [ ] **O4.2** Retain all physical completion constraints and equality/degenerate boundaries.
- [ ] **O4.3 alternative route** A global all-direction CAP/QCAP/contact invariant can replace the family inventory if it yields the desired sharp theorem for every minimizer.
- [ ] **O5** Combine sharp coverage with minimizer attainment and the explicit lower-window input. Remove every extra frame/contact/row assumption except those derived from original Packing.

## G2.X / G4 — Unrestricted optimal radius [BLOCKED]

- [x] **X.1** A hypothetical q<Q packing has an unrestricted global minimizer with a selected physical stress.
- [x] **X.2 bookkeeping** Either a tree component exists or every positive component contains a cycle; all physical squares remain in both routes.
- [ ] **X.3 sharp contradiction** Finish TREE.ALL and CY.ALL or a uniform replacement; include G0.W.
- [x] **G4.1 attainment** The exact construction gives R9<=sqrt(Q).
- [ ] **G4.2 lower bound** Establish R9>=sqrt(Q) without a hidden normalization.
- [ ] **G4.3 formal statement match** Transfer to the existing Packing/Optimum and nonnegative-radius conventions.

## G5 — Every equality packing [PARTIAL]

- [x] **G5.0.a** STRATIFIED_EQUALITY_FAMILY.md is necessary and sufficient within stratification.
- [x] **G5.0.b** SIGNED_MATCHED_EQUALITY_FAMILY.md gives the conditional signed 4+3 domain, including three sliders and two independently oriented free squares with true SAT tests.
- [x] **G5.0.c** The full common-coordinate class has that skeleton after a frame choice.
- [x] **G5.0.d** Cap/solid-row terminals pin only their stated anchors; capless and nonstratified Q witnesses remain mandatory controls.
- [ ] **G5.1** After optimality is proved, each original equality packing is a minimizer; apply the actual necessary reductions to it, not just a replacement configuration.
- [ ] **G5.2** Determine every equality branch of the uniform cyclic/P/Y proof, including zero multipliers, multiple circle atoms, variable frames and boundary contacts.
- [ ] **G5.3** Give exact necessary-and-sufficient parameter domains, not a restatement of nine unknown-square Packing.
- [ ] **G5.4** Apply the actual rotation/relabeling/reflection convention; avoid isolated uniqueness claims in continuous families.

## G6 — Audit and evidence [NOT COMPLETED]

- [ ] **G6.1** Independent end-to-end review of minimizer regularity, shared physical force/torque points, certificate distinctions and finite-cover logic.
- [ ] **G6.2** Audit cap/row/tree/pocket universal arguments, equality and lower-window inputs.
- [ ] **G6.3 NEW** Independently check QCAP's four own-coordinate inequalities, strict tilted case and aligned boundary perturbation; no interior/boundary shortcut.
- [ ] **G6.4 NEW** Audit the block-cut proof, unloaded one-body appendage force identity and loaded-clique centroid contradiction, with selected-component and actual-contact hypotheses.
- [x] **G6.R1 finite execution only** check_quadrant_blocks.py at commit fed5a888 was matched by Git blob and SHA-256 and executed under Python 3.13.5 at 2026-10-23 16:27:18–16:27:19 UTC, exit 0. The committed report records 104 identity checks, 2,254 rational quadrant squares, 1,772 finite graph tests exercising every coarse cell, and exact negative controls.
- [x] **G6.R2 evidence boundary** Finite samples are regression evidence, NOT the universal geometry/block theorem, physical feasibility of abstract graphs, independent audit, Lean proof or CI.
- [ ] **G6.5** Consolidate the eventual full unrestricted manuscript and versioned dependencies only after the missing sharp parents close. Ticked conditional tools must not be presented as completed T9.

## G7 — Standard-kernel Lean / Palomar verification [NOT STARTED]

- [ ] **G7.1** Exact model, attainment and negative-control predicates, without altering unrestricted Packing.
- [ ] **G7.2** Compactness, finite conic argument, actual contact stress and graph reductions using standard axioms and proved lemmas.
- [ ] **G7.3** Short terminal inequalities, finite coverage and the ACTUAL sharp whole-family proof, not an assumed stronger normal form.
- [ ] **G7.4** Full equality necessity and sufficiency.
- [ ] **G7.5** Compile, inspect axiom/import dependencies and independently replay with the standard kernel; no native-kernel bypass, admitted theorem or external oracle.

## G8 — Public integration [NOT STARTED]

- [ ] **G8.1** Integrate n=9 into Optimum, radius/packing registries and Challenge mirror.
- [ ] **G8.2** Update proof textbook and equality model documentation with exact verification status.
- [ ] **G8.3** Check n=1–8 regressions and source/progress provenance.
- [ ] **G8.4** Finalize PR only after the advertised unrestricted result and validation are complete.

## Current execution contract

1. **Do not claim P.ALL or Y.ALL closed.** The new quadrant theorem has explicit whole-square cone hypotheses; routing crossing squares remains a real obligation.
2. **Use the 58-cell ledger honestly.** It is a complete coarse partition, with one exact exclusion and 57 open sharp problems. Do not mistake abstract graph enumeration for physical geometry or multiply subgates merely to count progress.
3. Prefer a single full-family capacity/support inequality for P or Y, or a cyclic load/block theorem closing many cells, over isolated angle/offset refinements.
4. Preserve the exact P center-relaxation witness: any successful P proof must use more than those necessary disk/center constraints.
5. Commit finished general arguments promptly, then log UTC commit, theorem quantifiers, evidence scope and the unchanged global blocker. Tick only the stated whole class.
6. If a proposed normalization is false, keep its exact witness and reformulate. If the finite cells become a graph-enumeration rabbit hole, pivot to a genuinely global physical invariant rather than a finer mesh.
7. **Status truth:** T9 remains open; the current continuation adds tools and finite coarse coverage, not proof completion. Independent full audit, Lean and CI remain outstanding.
