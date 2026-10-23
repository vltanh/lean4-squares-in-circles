# n=9: deep ticked roadmap — two-load rigidity, P/Y completions and 56 open cyclic cells

**Branch:** `research/nine-tablefree-hand`; **PR:** #11, draft.
**Checkpoint:** 2026-10-23 two-load reciprocal continuation, read base `a89802cd834aef3a96d9622bd4829a2c49df17fd`.

**The unrestricted lower bound and complete global equality classification remain OPEN.** New hand arguments prove that every physical positive component with exactly two circle-loaded bodies has parallel contact forces. In the explicit radius window it has squared radius 17/4 and at most six aligned bodies. This closes the residual diamond and hence the **whole four-body cyclic cell C1.4.b0**. Two of the 58 coarse cyclic cells are now closed; 56 remain open. P.ALL, Y.ALL and completion capacities for larger two-loaded components remain unproved. Independent full audit and Lean/CI verification are not claimed.

This revision consolidates the previous deep plan; its proof sources and historical timestamps remain in Git. Checkboxes describe exact theorem scope, not a proof-completion percentage.

## Canonical sources and proof-status vocabulary

- [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md): every one of the 58 cells individually recorded, now two [x] and 56 [ ].
- [TWO_LOAD_PROGRESS.md](TWO_LOAD_PROGRESS.md): current UTC proof commits, exact pinned execution, corrected report provenance and still-open parents.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): original six tree profiles and their P/Y survivor cover.
- [G2_SUBGATES.md](G2_SUBGATES.md): live mathematical status.
- [QUADRANT_BLOCK_PROGRESS.md](QUADRANT_BLOCK_PROGRESS.md), [ORIGIN_POCKET_PROGRESS.md](ORIGIN_POCKET_PROGRESS.md), [PROGRESS_LEDGER.md](PROGRESS_LEDGER.md): earlier append-only histories.

**[x] CLOSED hand** means a complete analytic implication is written with its stated hypotheses and boundary cases. Independent audit and Lean verification are separate. **[ ] OPEN** means the universal implication has not been proved. **CLOSED reduction** is a necessary structure theorem, not automatically q>=Q. **REJECTED** is a false normalization with an exact counterexample.

## 0. Target, global dependency map and indispensable distinctions

Put Q=1105/256 and q0=17/4. Construction gives R9<=sqrt(Q). The missing target is:

> **T9:** every nine independently oriented closed unit squares with disjoint open interiors inside a disk of radius R satisfy R^2>=Q.

No common separating frame, row, central square or prescribed stress graph is an original hypothesis. Every stressed component is studied **with all the other physical squares**, including zero-weight contacts and other stress components.

```text
[x] G0 exact model / attainment / negative controls
[x] G1 signed/grid/cap/row/pocket/quadrant tools, conditional
[x] G2.C entire common-coordinate-separable theorem
[x] G2.O3.0 minimizer -> true physical stress
[x] G2.O3.1 physical force/torque incidence and radial bridges
 |
 +-- TREE.F1/F2 q0=17/4 and six origin-incidence profiles     [x] reduction
 |     +-- TREE.12, .03, .04 and point-only .02.P            [x] completions
 |     +-- all surviving tree configurations -> P or Y      [x] reduction
 |     +-- P.ALL staggered paths + five other squares       [ ] OPEN
 |     +-- Y.ALL side/vertex fans + four other squares      [ ] OPEN
 |
 +-- CY.BLOCK 21 profiles / 58 coarse cells                 [x] coverage only
 |     +-- CY.ACUTE loaded NONCONTACT graph connected       [x] necessary
 |     +-- CY.CHANNEL all simple four-cycles excluded       [x] prior theorem
 |     +-- CY.TWOLOAD all two-loaded pair forces parallel   [x] NEW hand
 |     |     +-- radius 17/4 and 4–6 aligned bodies         [x] reduction
 |     |     +-- five/six-body physical completions         [ ] OPEN
 |     +-- C1.3.b0 isolated selected triangle               [x] excluded
 |     +-- C1.4.b0 all C4 / diamond / K4 cases               [x] NEW excluded
 |     +-- remaining 56 coarse sharp cell theorems          [ ] OPEN
 |
 +-- CAP/QCAP every-direction necessary constraints        [x] tools
 |     +-- full physical routing/global contradiction      [ ] OPEN
 |
[ ] G2.O4/O5 all complete physical realizations sharply bounded
[ ] G2.X/G4 unrestricted radius theorem
[ ] G5 every equality packing, necessity and sufficiency
[ ] G6 independent whole-manuscript audit
[ ] G7 standard Lean kernel / Palomar replay
[ ] G8 public integration and final PR closure
```

### G0.W Explicit radius-window prerequisite

Tree quantization, channel/loaded-graph exclusions and new two-load high-radius quantization use **79/40<=R<=sqrt(Q)**. The existing n=8 lower bound can provide this by deletion, with its current proof dependencies. A standalone table-free n=9 proof must replace that import with an independent coarse hand bound. The parallel-force theorem itself only assumes q>9/4; geometric capacity statements directly in D_(17/4) do not need the lower-window input.

- [x] **W.1** All window-dependent manuscript hypotheses are explicit.
- [ ] **W.2** Final dependency assembly must cite the actual established n=8 theorem and its exact deletion implication, not merely an informal reference.
- [ ] **W.3** Supply an independent hand R>=79/40 argument if standalone table-freedom is required.

### Representation and scope rules

1. The <=19-term planar translational support and <=27-atom physical torque-balanced contact-incidence certificate are distinct. No unproved 19-term planar-body torque theorem is imported.
2. The physical **incidence** graph is planar; the selected positive **body-pair** graph need not be. Block sizes, bridges and triangles below concern the body-pair graph.
3. A positive bridge is not every physical contact; nonbridge forces need not be radial.
4. Loaded **noncontact** means closed squares are physically disjoint, not just that no positive edge was chosen. Zero-weight touching counts as contact.
5. A coarse cell is not a single topology or a finite pose list. It retains all block graphs, loads, normals, positions and 9-n additional physical squares.
6. A two-loaded cyclic layered core can have inner heights outside [-1/2,1/2]. It is not automatically the older family P.

---

## G0 — Exact physical semantics, attainment and negative tests

### G0.1 Geometry [CLOSED hand]
- [x] **G0.1.a** Corners c+(epsilon*u+eta*v)/2 for orthonormal side vectors.
- [x] **G0.1.b** Maximum squared corner radius |c|^2+1/2+|c.u|+|c.v|; full containment follows by convexity.
- [x] **G0.1.c** Exact own-axis SAT disjunction for physical nonoverlap, with tangencies and multiple owners allowed.
- [x] **G0.1.d** Disjoint inscribed half-radius disks imply center distance >=1. This is necessary, not sufficient square geometry.

### G0.2 Exact constructions [CLOSED hand]
- [x] **G0.2.a** HAND_PROOF.md attains Q.
- [x] **G0.2.b** NONRIGID_WITNESS.md and NO_GLOBAL_ORTHOGONAL_FRAME.md retain independent rotations and genuine oblique separators at equality.
- [x] **G0.2.c** TWO_STACK_SHARP_EQUALITY_WITNESS.md attains Q in the old residual two-stack class and supplies perpendicular signed 4+3 chains.

### G0.3 Required falsification controls [CLOSED negative]
- [x] No universal common separating frame or global horizontal stratification; even an all-parallel equality packing can lack stratification in every frame.
- [x] A central open square is not mandatory; keep boundary-origin states.
- [x] Center-radius/L-infinity relaxations and crossed-four-chain arguments without the ninth body are insufficient.
- [x] Some equality packs have no sharp triple cap in any direction.
- [x] Nonaligned/branching tree cores really exist with fewer than nine bodies; completion, not core existence, is the missing capacity.
- [x] Three squares fit on one side of a staggered P path; independent two-per-side capacity is false.
- [x] The exact five-center P relaxation passes center-radius, inscribed-disk obstacle clearance and mutual unit separation, but does not realize full squares. Actual square supports are essential.
- [x] The universal 45-degree center-angle rule is false; retain centers (5/4,+/-1/2), q=65/16.
- [x] **NEW TL.N1:** a physical six-cycle with inner centers (+/-1/2,+/-3/5) has parallel two-load stress but contains no inner square in the P slider range.
- [x] **NEW TL.N2:** a physical six-body theta graph with seven positive contacts has two loads and parallel normals; two-loaded does not mean simple cycle.
- [x] **NEW TL.N3:** a nonparallel three-loaded physical Y core has nonzero reciprocal area. The two-loaded premise is essential.
- [x] **NEW TL.N4:** an abstract balanced planar vector system with two exterior edges can have opposite signed finite areas if cyclic direction order is dropped. Balance alone is not the new theorem.
- Sources: the earlier negative-control manuscripts and TWO_LOAD_PROGRESS.md / TWO_LOAD_RECIPROCAL_EXACT_CHECK.json.

---

## G1 — Short terminal stresses and physical capacity tools

### G1.T1 Signed 4+3 / long-short endpoints [CLOSED hand, conditional]
- [x] Exact endpoint spans, true perpendicular gaps with independent signs, weights 23/9 and the all-angle square penalty imply q>=Q.
- [x] Equality pins the stressed endpoints and forces seven-chain width/alignment saturation.
- Sources: FOUR_ANCHOR_STRESS.md, PAIRED_FOUR_ANCHOR_STRESS.md, SIGNED_MATCHED_CHAIN_STRESS.md.
- [ ] **T1.EXTRACT:** a general unrestricted pack has not been shown to supply those hypotheses.

### G1.T2 Grid, projection cap, weak dual [CLOSED hand, conditional]
- [x] Four-corner grid spans give q>=9/2; GRID_FOUR_CORNER_STRESS.md.
- [x] Rotated projection-disjoint cap-row theorem; ORIENTATION_STABLE_SEVEN_ANCHOR.md.
- [x] Exact center elimination for fixed genuine owners/orientations; SEPARATOR_GRAPH_CONVEX_DUAL.md.
- Exact stress attainment gives the unknown q0, not q0>=Q by itself.

### G1.T3 Oblique-safe cap / strip / solid row
- [x] **CAP.1–2** All-angle clipped-section proof and three-square cap rigidity above y=7/16 in D_Q.
- [x] **CAP.3** Every q<Q nine-square pack has >=5 squares meeting |y|<7/16 in every direction.
- [ ] **CAP.4** Derive a universal contradiction or complete alternatives; interval antichains are not automatically coordinate-separable physical rows.
- [x] **ROW.1–2** All five-square completions of a SOLID 4x1 row force q=Q, other squares freely rotated.
- [x] **ROW.3** Mixed four-versus-three seam without ordering the three squares.
- [ ] **ROW.4** Prove the geometric premise or use another whole-family terminal; staggered P is not solid.

### G1.T4 Origin gaps and screened pockets
- [x] **V.1–2** Three vertex-origin bodies in D_(17/4) give angular gaps totaling pi/2 and annular spacing >pi/6; at most five extras. THREE_VERTEX_ORIGIN_CAPACITY.md.
- [x] **POCKET.1** A radial S terminal plus a root side physically screens the full positive ray.
- [x] **POCKET.2–3** Acute screened pockets are empty, right pockets have one unique square, and screened moderately obtuse pockets hold at most two.
- [x] **POCKET.4** Distinct radial terminals have angular separation >=2 arctan(1/2).
- [ ] **POCKET.ROUTING** Every use must derive whole-square wedge containment, not merely center-angle membership.
- Source: RADIAL_SECTOR_POCKET_CAPACITY.md.

### G1.T5 Unavoidable-point quadrant theorem
- [x] **QCAP.1.a** Exact own-frame inequalities put (1,1) in every square wholly in the first quadrant of D_(17/4).
- [x] **QCAP.1.b** Tilted squares contain that point in their open interior; aligned boundary squares share a sufficiently small southwest perturbation.
- [x] **QCAP.2** Each origin-centered quadrant has capacity at most one, without terminal obstacles or common separating axes.
- [x] **QCAP.3** Every hypothetical nine-square pack in D_(17/4) has >=5 squares whose open interiors meet at least one axis, in every perpendicular frame.
- [ ] **QCAP.P / QCAP.Y / QCAP.GLOBAL** Whole-family routing/capacity for crossing squares remains open. The quadrant theorem does not by itself close P or Y.
- Source: QUADRANT_UNAVOIDABLE_POINT.md.

---

## G2.C — Entire common-coordinate-separable class [CLOSED hand]

- [x] **C0** Rank-product injection, no five-chain and strict 3x3 grid obstruction force a four-chain.
- [x] **C1** Four-chain shadow and inner-pair overlap.
- [x] **C2** Entire large-zigzag branch is excluded; no old 4x3 zigzag residue remains open.
- [x] **C3.a** Disjoint signed 4+3 chains close directly.
- [x] **C3.b** A five-square complement without a horizontal triple has canonical vertical stacks (4,1) or (3,2).
- [x] **C3.c** Crossed-four-chains-plus-ninth exclusion closes (4,1).
- [x] **C3.d** Five-element matching and a finite singleton split give perpendicular signed 4+3 chains in (3,2).
- [x] **C4** COORDINATE_SEPARABLE_NINE_COMPLETE.md proves the whole class and necessary equality skeleton.

Individual square frames can differ; pairwise separating axes are common. That latter hypothesis is false globally. Do not reopen this finished branch for minor parameter refinements.

---

## G2.O3.0–O3.1 — Unrestricted physical stress [CLOSED hand necessary reductions]

### O3.0.2 Minimizer and exact stress
- [x] Compact center/frame/SAT sublevels yield a global minimizer from a subcritical packing.
- [x] Strict selection at noncontact pairs leaves positive multipliers only on true contacts.
- [x] Explicit dilation gives regularity and normalized nonnegative active forces, not a numerical optimization premise.
- [x] <=19 fixed-frame terms and exact center-dual attainment; every positive component has >=2 loaded bodies and can be normalized separately.
- Source: SPARSE_MINIMIZER_STRESS.md.

### O3.1a–g Physical graphs, torque and bridges
- [x] PLANAR_STRESS_CORE.md gives sparse planar outer-loaded translational support.
- [x] ROTATION_STATIONARY_STRESS.md gives separate angular stationarity without invalid absolute-value differentiation.
- [x] PHYSICAL_CONTACT_STRESS.md gives actual shared force points, joint force/torque and a planar incidence representation, <=27 physical atoms.
- [x] Unloaded two-force body widths are 1 or sqrt(2); square-ended paths have reserve 0,1,sqrt(2),2 at q<=Q.
- [x] RADIAL_BRIDGE_AND_LEAF_REDUCTION.md proves radial bridge cuts, <=4 circle-clear central bridge-cover bodies and exact radial S/D loaded leaves.
- These are necessary reductions; none alone proves the sharp radius for nine physical bodies.

---

## G2.O3.2.TREE — Exhaustive remaining tree families [COVER CLOSED, CAPACITIES OPEN]

### TREE.F1/F2 Global tree reduction
- [x] Every unloaded tree body is central; every loaded body has radial S/D geometry; an origin-avoiding unloaded body is only a one-step side transmitter.
- [x] Origin-interior roots are excluded by a complete short-arm side/vertex split.
- [x] Origin-side and origin-vertex alternatives force R^2=17/4 in the stated window.
- [x] Every unloaded body contains zero on its boundary; all loaded bodies are radial S terminals.
- [x] Incidence counts 2s+v<=4 and s+v>=2 yield exactly six complete profiles, with continuous parameters and all physical completions retained.
- Sources: TREE_BODY_LOCALIZATION.md, TREE_RADIUS_QUANTIZATION.md.

### Six original tree profiles

| Profile | Complete case status |
|---|---|
| TREE.20 (2,0) | [ ] OPEN capacity, included in P.ALL |
| TREE.11 (1,1) | [x] Exact P/Y normal form; [ ] full capacity |
| TREE.12 (1,2) | [x] CLOSED: cardinal cage gives <=8 total squares |
| TREE.02 (0,2) | [x] Point-only strict-normal .P completion; [ ] shared-edge .E is a P boundary |
| TREE.03 (0,3) | [x] CLOSED: origin angular/annulus capacity gives <=8 total |
| TREE.04 (0,4) | [x] CLOSED: central 2x2 block gives <=8 total |

- [x] TREE_FINITE_COMPLETIONS.md supplies the arbitrary-extra-orientation CAGE/BLOCK capacities.
- [x] TREE02_POINT_CONTACT_COMPLETION.md preserves its strictly exposing central normal premise and routes the shared-edge boundary rather than deleting it.
- [x] REMAINING_TREE_TWO_FAMILY_REDUCTION.md covers EVERY remaining tree geometry by P or Y.
- No tree lemma makes a nonbridge cyclic edge radial.

### TREE.P — All staggered four-square paths plus FIVE other squares [OPEN]

Exact fixed centers:

    (-3/2,0), (-1/2,tau1), (1/2,tau2), (3/2,0),
    -1/2 <= tau1,tau2 <= 1/2,

with FIVE additional independently oriented squares inside D_(17/4).

- [x] **P.0** All TREE.20, shared-edge TREE.02.E and aligned TREE.11 endpoints are retained, including slider boundaries.
- [x] **P.FLAT** tau1=tau2=0 is excluded by solid-row completion.
- [x] **P.N1** Three squares can fit on one side of a staggered row; separate two-per-side capacities are false.
- [x] **P.N2** Five candidate centers pass center-radius, inscribed-disk obstacle clearance and mutual distances; actual square supports must be used.
- [ ] **P.1 ROUTING** A property for every added square, with its corners and true SAT axes, including quadrant-crossing cases.
- [ ] **P.2 COUPLED CAPACITY** At most four extras over the entire two-slider parameter square; every subpartition must be finite and cover all continuous values.
- [ ] **P.3 ENDPOINTS** Reconcile both signs and |tau_i|=1/2 without strengthening physical nonoverlap to an inapplicable strict-normal contact premise.
- [ ] **P.ALL** No five-square physical completion of any member.

### TREE.Y — Whole side/vertex fan plus FOUR other squares [OPEN]

Exact domain:

    0<alpha<1, 0<theta<pi/2,
    H=[-alpha,1-alpha] x [0,1],
    u=(cos(theta),-sin(theta)), v=(-sin(theta),-cos(theta)),
    K=[0,u]+[0,v], with radial terminals S(north), S(u), S(v).

- [x] **Y.0** Every nonaligned residual TREE.11 has this five-body form; force ratios are sin(theta),cos(theta). Angular endpoints reduce to P.
- [x] **Y.N** Nonaligned physical cores exist; their completion, not core existence, is the missing theorem.
- [ ] **Y.1 ROUTING** Whole-square regions without a common separator assumption; derive screen hypotheses rather than assigning by center angle.
- [ ] **Y.2 CAPACITY** At most three additional arbitrary squares for every alpha/theta in the whole domain.
- [ ] **Y.3 BOUNDARY** Include limiting shared-side configurations consistently with P.
- [ ] **Y.ALL** No four-square completion.

**TREE.ALL exit:** P.ALL + Y.ALL + closed cases + explicit lower-window input. Not achieved.

---

## G2.O3.2.CY — Cyclic inventory and new global two-load invariant

### CY.BLOCK Exact coarse coverage [CLOSED hand]

Sources: CYCLIC_BLOCK_INVENTORY.md, CYCLIC_CELL_LEDGER.md.

- [x] **CY.B1** The maximal cyclic blocks and bridges have a block/articulation tree.
- [x] **CY.B2** n=1+b+sum(k_i-1)<=9 for sorted cyclic sizes k_i>=3.
- [x] **CY.B3** Exactly 21 sorted size profiles / 58 bridge-count cells, split 28+22+7+1 by cyclic-block count.
- [x] **CY.B4** Every cell includes all 9-n remaining physical squares.
- [ ] **CY.B5 GEOMETRY** Internal adjacencies, actual contacts, loads and continuous orientations remain; a block-size list is not a solved sharp geometric classification.

### CY.LOAD / CY.ACUTE Necessary load restrictions [CLOSED hand]

- [x] **CY.L1** No unloaded positive appendage with only one external attachment body, by the summed support-gap force identity.
- [x] **CY.L2** Every endblock has a loaded nonarticulation body; intermediate blocks need not have private loads.
- [x] **CY.L3** A touching loaded clique is impossible in the window by the circle-force centroid bound.
- [x] **CY.A1** A circle-loaded square in q>2+sqrt(3) lies strictly inside the 45-degree cone of each of its circle corners.
- [x] **CY.A2** Physically touching loaded bodies have strictly positive pairwise circle-load-vector dot products.
- [x] **CY.A3** Summed circle force zero makes the physical loaded-NONCONTACT graph connected. No loaded body touches every other loaded body, nor is there a complete touching join across any nontrivial load partition.
- Source: ACUTE_LOADED_CONTACT_GRAPH.md, prior commit 690f245.

### CY.CHANNEL Normal paths [CLOSED hand at scope]

- [x] **CH.1** An unloaded degree-two path attains the unique closest displacement vector between its endpoint convex squares.
- [x] **CH.2** Two such paths between the same endpoints have equal normal and reserve; direct contact cannot coexist with a positive-length channel.
- [x] **CH.3** An unloaded degree-two square cannot have physically touching neighbors; every degree-two vertex of a positive triangle is loaded.
- [x] **CH.4** A simple cycle with exactly two loads is a six-square aligned S cycle at q=17/4 in the window.
- [x] **CH.C4** All simple four-cycle load patterns are excluded.
- Source: PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md, prior commit a89802c. The six-body completion was NOT closed there.

### CY.TWOLOAD — NEW reciprocal-area theorem for EVERY two-loaded component [CLOSED hand; audit pending]

Source: TWO_LOAD_RECIPROCAL_RIGIDITY.md, initial commit 248202d, clarified 9fad28e. Unlike CH.4 it assumes neither a tree nor a simple cycle.

#### TL.R: exact abstract planar lemma
- [x] **TL.R1** For a connected embedded vector-equilibrium graph, edge increments Jf integrate to face potentials; vertex divergence gives path independence on the sphere.
- [x] **TL.R2** Counterclockwise force-direction order at each finite vertex makes its reciprocal polygon weakly convex, with nonnegative signed area; noncollinear forces imply positive area.
- [x] **TL.R3** The signed areas sum to zero because every dual edge occurs in opposite directions at its two primal endpoints, even with repeated face occurrences.
- [x] **TL.R4** With a two-edge exterior vertex its polygon area is zero; all finite areas vanish, and connectedness forces a common force line.
- [x] **TL.R.N negative control** Abstract equilibrium without the direction-order premise can have finite areas +1 and -1. It is not the physical lemma.

#### TL.P: every physical hypothesis supplied
- [x] **TL.P1** Keep shared application points as junction nodes; positive outward body normals aggregate to a nonzero normal-cone vector.
- [x] **TL.P2** Square boundary normals follow boundary cyclic order. At contact junctions their negatives lie in disjoint right-angle/half-plane tangent sectors, giving the junction direction order.
- [x] **TL.P3** Each loaded square has one or two adjacent positive circle corners. The intervening outer chord cap is too thin for another unit square and supplies an exterior port.
- [x] **TL.P4** Aggregating those consecutive circle atoms preserves force direction order; two loaded bodies give a balanced two-edge exterior vertex. No planar body-graph assumption is made.
- [x] **TL.P5** At multiple junctions, repeated-sign aggregate forces lie on tangent/normal extreme rays; positivity then recovers parallelism of EVERY original pair force, not just sums.
- [x] **TL.P.ALL** For q>9/4, every physical positive component with exactly two circle-loaded bodies has all contact normals parallel.

#### TL.G: exact high-radius geometry and its limits
- [x] **TL.G1** Directed true contacts strictly increase the common projection; unloaded balance makes every body lie on a path from one loaded source to the other loaded sink.
- [x] **TL.G2** Endpoint parallel forces/torque imply radial S/D geometry. Aggregating opposite faces at any unloaded body gives width exactly 1 or sqrt(2).
- [x] **TL.G3** Candidate-window path reserves and endpoint-gap comparisons leave only side-normal endpoints with q=17/4, and exactly two internal side-normal bodies per directed path.
- [x] **TL.G4** Every component body is aligned, with loaded centers (+/-3/2,0) and unloaded centers in x=+/-1/2 layers.
- [x] **TL.G5** With the selected strictly exposing point-only normals, each layer height is in (-1,1) and each layer has at most two bodies. Total component size is 4,5 or 6.
- [x] **TL.G6** Positive triangles and all two-loaded components with 7–9 bodies are excluded. Other load cardinalities in those cells remain open.
- [x] **TL.G.N negative controls** A six-cycle can have all inner heights +/-3/5; a six-body theta graph with seven contacts also exists. Do not identify arbitrary channels with P or declare all two-loaded graphs simple cycles.
- [ ] **TL.COMPLETE5** Entire physical four-square completion of the five-body layered cores.
- [ ] **TL.COMPLETE6** Entire physical three-square completion of the six-body layered cores, including theta/contact-degenerate variants.
- [ ] The four-body survivor is exactly P, whose whole completion remains P.ALL.

### C1.4.b0 — NEW full coarse-cell closure [CLOSED hand; audit pending]

Source: FOUR_BODY_CYCLIC_CELL_CLOSED.md, commit 05e15a0.

- [x] **C1.4.GRAPH** Every biconnected simple four-body graph is C4, diamond K4-e or K4, by minimum degree two and edge counts 4/5/6.
- [x] **C1.4.C4** All load patterns excluded by prior CH.C4.
- [x] **C1.4.K4** All load patterns excluded by loaded noncontact connectedness.
- [x] **C1.4.D1** For the diamond, only its nonadjacent degree-two tips can be loaded.
- [x] **C1.4.D2** TL.P.ALL makes every pair force parallel; the diamond's positive triangle contradicts pairwise touching disjoint positive-length projection intervals.
- [x] **C1.4.ALL** Every load/angle/contact realization of the entire selected component is excluded, independently of the other five physical squares.

### CY.CELLS Current complete inventory count

| Cyclic block count | Profiles | Cell count | Sharp status |
|---|---|---:|---|
| 1 | (3),(4),(5),(6),(7),(8),(9) | 28 | C1.3.b0 and C1.4.b0 [x]; other 26 [ ] |
| 2 | (3,3),(3,4),(3,5),(3,6),(3,7),(4,4),(4,5),(4,6),(5,5) | 22 | all [ ] |
| 3 | (3,3,3),(3,3,4),(3,3,5),(3,4,4) | 7 | all [ ] |
| 4 | (3,3,3,3) | 1 | [ ] |

**56 cells OPEN.** The two-load theorem restricts many subfamilies but does not tick a larger cell when its >=3-loaded physical realizations remain. One invariant closing multiple cells is preferable to 56 separate angle-grid searches.

### Uniform subsubgate contract for every unchecked cell C

- [ ] **C.1 GRAPH** Cover every internal block adjacency and articulation assignment in its size/bridge data.
- [ ] **C.2 LOAD** Impose actual nonnegative circle/contact forces, physical application points, torque, loaded endblocks, connected loaded noncontact, and TL where applicable.
- [ ] **C.3 GEOMETRY** Prove a uniform inequality over every admissible orientation/pose; do not select a canonical drawing without a reduction theorem.
- [ ] **C.4 COMPLETION** Include all 9-n other physical squares, zero-weight contacts and multiple stress components.
- [ ] **C.5 SHARPNESS** Establish q>=Q for every complete nine-square realization, or exclude the entire component cell in the declared window.
- [ ] **C.6 EQUALITY** Retain all q=Q limits and free-square frames if the cell survives in global equality.

**CY.ALL remains OPEN:** finite coarse coverage and a strong two-load invariant are not a universal sharp capacity theorem.

---

## G2.O3.3 / O4 / O5 — Global sharp coverage [OPEN]

- [x] **O3.3.T** Every remaining tree realization is in P or Y after the closed origin cases.
- [x] **O3.3.C** Every selected cyclic component belongs to exactly one of the 58 coarse cells.
- [x] **O3.3.L2** Every two-loaded physical component has the new exact parallel/layered geometry, across the whole graph inventory.
- [ ] **O3.3.SHARP** Finish actual completion capacities for P, Y, larger two-loaded layers and every remaining cyclic cell with >=3-loaded possibilities.
- [ ] **O4.1** Obtain exact orientation-uniform stress/support/capacity inequalities, not numerical dual values at selected poses.
- [ ] **O4.2** Preserve tangencies, zero weights and all physical completion constraints.
- [ ] **O4.3 alternative** A global CAP/QCAP/contact-area invariant can replace the inventory if it yields the unrestricted sharp theorem.
- [ ] **O5** Combine sharp coverage with compact attainment and G0.W; remove every unproved extra frame/row/contact hypothesis.

## G2.X / G4 — Unrestricted radius [BLOCKED]

- [x] **X.1** A subcritical packing has an unrestricted minimizing stress.
- [x] **X.2** Tree-present versus all-components-cyclic is a complete outer split, with all physical bodies retained.
- [ ] **X.3** Supply the missing sharp contradiction for every branch, plus the declared lower-window input.
- [x] **G4.1** Exact construction gives the upper bound.
- [ ] **G4.2** Establish R9>=sqrt(Q) from original Packing only.
- [ ] **G4.3** Match the existing nonnegative-radius/Optimum interface.

## G5 — Every equality packing [PARTIAL]

- [x] **G5.0.a–c** Stratified and signed matched-chain families are necessary/sufficient within their hypotheses; common-coordinate equality has a signed skeleton after a frame choice.
- [x] **G5.0.d** Cap/solid-row terminals pin only their specified anchors. Capless, oblique and nonstratified Q examples remain required controls.
- [x] **G5.0.e necessary restriction** At q=Q, which is not 17/4, a selected two-loaded component cannot occur if all premises of TL.G apply. This is not a complete classification of the >=3-loaded equality cores.
- [ ] **G5.1** After optimality is proved, apply the necessary reductions to EACH original Q packing, not just a replacement minimizer.
- [ ] **G5.2** Characterize every surviving sharp cyclic/equality branch and its zero-weight limits.
- [ ] **G5.3** Provide concise exact necessary-and-sufficient domains for all free centers/angles.
- [ ] **G5.4** Use the actual rotation/relabeling/reflection convention; do not claim a rigid isolated pose when continuous freedoms exist.

## G6 — Independent audit and exact evidence [NOT COMPLETED]

- [ ] **G6.1** Audit global compactness/regularity and actual physical contact gradients, normal choices and representation distinctions.
- [ ] **G6.2** Audit cap/row/tree/pocket all-angle arguments, finite tree cover and lower-window prerequisite.
- [ ] **G6.3** Audit QCAP boundary-versus-interior handling and cyclic block/load reductions.
- [ ] **G6.TL1 NEW** Independently verify direction order at every square and common-point junction, including aggregation on normal-cone boundaries.
- [ ] **G6.TL2 NEW** Verify empty outer circle-chord caps, exterior-port replacement and the sphere embedding; no forces are assumed along topological drawn spokes.
- [ ] **G6.TL3 NEW** Verify dual face-potential integration, signed-area cancellation with repeated face occurrences, convexity/zero-area implication and recovery of original pair normals.
- [ ] **G6.TL4 NEW** Verify layered endpoint quantization, strict-contact height bounds and separation from the narrower P domain.
- [x] **G6.R1 finite execution only** Earlier cap/tree/origin/quadrant checks retain their recorded finite scope.
- [x] **G6.R2 NEW finite execution only** check_two_load_reciprocals.py, source 0d4c958, matched Git blob/SHA-256 and ran on 2026-10-23 19:32:40 UTC, Python 3.13.5, exit 0. It checks 12 radius comparisons, all 64 labelled four-body graphs/load subsets, and five physical planar reciprocal examples with exact corners, SAT, force/torque, face integration, convexity and signed-area cancellation.
- [x] **G6.R3 evidence controls** Three-loaded Y has nonzero reciprocal area; an abstract wrong-order vector graph has cancelling positive/negative areas; five/six-body two-load survivors show why component completion remains necessary.
- [ ] **G6.4** Independent full manuscript audit is not replaced by those finite executions. Correct report transcription is pinned at commit 4843058; its data are not a general certificate.
- [ ] **G6.5** Consolidate the final unrestricted dependency proof only once sharp parent gates close.

## G7 — Standard Lean kernel / Palomar proof [NOT STARTED]

- [ ] **G7.1** Exact original geometry, construction and equality types, without stronger Packing semantics.
- [ ] **G7.2** Compactness, active-gradient/conic arguments, physical stress and planar vector-flow lemmas using proved standard dependencies.
- [ ] **G7.3** Formalize the actual exhaustive sharp physical completion proof, not assumed normal forms or finite sampled cases.
- [ ] **G7.4** Equality necessity and sufficiency.
- [ ] **G7.5** Compile, inspect axioms/dependencies and independently replay in the standard kernel. No native-kernel bypass, admission or undisclosed oracle.

## G8 — Integration [NOT STARTED]

- [ ] **G8.1** Add n=9 to Optimum/radius/packing registries and Challenge mirror.
- [ ] **G8.2** Update proof/equality documentation with exact audit and verification status.
- [ ] **G8.3** Check n=1–8 regression and source provenance.
- [ ] **G8.4** Finalize the draft PR only after the advertised unrestricted proof and required verification are actually complete.

## Current execution contract

1. Keep P.ALL/Y.ALL and larger layered-core completions OPEN until their full physical capacities are proved.
2. The 58 coarse cells now have **two whole-cell exclusions and 56 open rows**. Do not confuse subfamily restrictions with parent closure.
3. Use the reciprocal invariant to attack complete load/geometric families; do not create finer angle boxes merely to increase checked-gate counts.
4. Preserve exact physical negative controls and every unstressed completion body.
5. Commit finished arguments promptly and log UTC provenance, exact quantifiers, finite evidence and unchanged global blockers in TWO_LOAD_PROGRESS.md or a subsequent append-only checkpoint.
6. If a proposed reduction fails, retain the exact witness and revise it; do not defend a false stronger normalization by shrinking the domain indefinitely.
7. T9 remains open. All newly checked general results are hand manuscripts pending independent audit; no Lean or CI success is claimed.