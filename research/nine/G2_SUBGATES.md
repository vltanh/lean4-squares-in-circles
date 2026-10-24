# n=9 — live G2 ledger: all trees and two-load completions closed

**Checkpoint:** 2026-10-24 complete P/Y continuation. **The unrestricted lower bound and complete equality classification remain OPEN.** P_ALL_COMPLETION.md and Y_ALL_COMPLETION.md now close the full P and Y families. Together with the exhaustive tree reduction, every selected positive tree component is excluded from a nine-square packing in the declared radius window. P also completes the five-/six-body reduction, excluding every selected positive component with exactly two circle-loaded bodies, including cyclic components. Every surviving component is cyclic and has 3–7 noncollinear circle resultants. The remaining geometric obligations are the general boundary-only C7 completion and mixed components containing a circle-clear body. Two coarse cells remain closed and 56 open. No Lean compilation or CI has been run.

The reciprocal theorem applies to every physical positive component with exactly two loaded bodies, forcing parallel forces and 4–6 aligned bodies at q=17/4 in the declared window. The completion theorems now remove the six-body case and reduce the five-body case to a genuine P skeleton, whose full capacity is proved in P_ALL_COMPLETION.md. Global physical geometry limits any other selected component to 3–7 loaded bodies with noncollinear resultants; it does not close that metric completion problem.

**Verification level:** written hand arguments pending independent full audit and Lean verification. Finite exact regressions are not a universal proof. Historical ledger versions remain in Git. The current canonical contracts are DEEP_GATED_ROADMAP.md and CYCLIC_CELL_LEDGER.md; current progress/evidence is TWO_LOAD_PROGRESS.md.

## New simple-cycle body bound

[SIMPLE_POSITIVE_CYCLE_BODY_BOUND.md](SIMPLE_POSITIVE_CYCLE_BODY_BOUND.md) proves that a selected positive component whose body-pair graph is a simple cycle has at most **eight bodies**. The proof first excludes crossing opposite-pair edges at a four-square junction, derives a Jordan cycle with the physical circle-touching bodies in circular center order, then charges more than 40 degrees to each cycle body through exact transmission-channel bounds. It retains circle-touching bodies with zero circle weight and arbitrary square orientations.

This closes the nine-body **simple-cycle** subfamily. It does not close the entire C1.9.b0 coarse cell, which also includes branching biconnected graphs, or completion of smaller cycles. The whole-cell count remains two closed and 56 open. The manuscript has received two separate hand audits; the complete prerequisite chain and Lean verification remain open.

## 1. Ticked parent ledger

| Gate | Complete scope | State |
|---|---|---|
| G2.C | All common-coordinate-separable nine-square packings | [x] CLOSED hand |
| O3.0.2 / O3.1 | Compact minimizer; true physical force/torque, incidence and bridge reductions | [x] CLOSED necessary reductions |
| TREE.F1/F2 | Every positive tree in the declared window has q=17/4 and six origin-incidence profiles | [x] CLOSED exhaustive reduction |
| TREE.12 / .03 / .04 / .02.P | Full completion exclusions, with .02.P's strict-normal contact premise | [x] CLOSED hand |
| TREE.REMAINDER | Every surviving tree configuration is P or Y | [x] CLOSED normal form |
| **P.ALL / Y.ALL** | Full arbitrary-square completions of both families | [x] CLOSED hand |
| **TREE.ALL / TL.COMPLETE** | Every positive tree and every two-load component in the declared window | [x] CLOSED hand |
| CAP / QCAP | All-angle cap/quadrant tools and every-direction necessary counts | [x] CLOSED at stated scope |
| CY.BLOCK | 21 profiles, 58 block-size/bridge-count cells, all physical extras retained | [x] CLOSED coarse coverage |
| CY.ACUTE | Loaded physical noncontact graph connected | [x] CLOSED necessary theorem |
| CY.CHANNEL | Normal-channel uniqueness; entire simple C4 component excluded | [x] CLOSED hand |
| **CY.TWOLOAD** | Exactly two loaded bodies force parallel pair normals in any physical component | [x] NEW CLOSED hand |
| **TL.LAYER / TL.COUNT** | In window, q=17/4; 4–6 bodies in aligned endpoint/internal layers | [x] NEW CLOSED reduction |
| **C1.4.b0** | Every C4, diamond or K4 selected four-body component | [x] NEW CLOSED whole cell |
| C1.3.b0 | Isolated selected triangle | [x] Previously CLOSED |
| Other 56 cyclic cells | All graphs, >=3-loaded possibilities and remaining physical squares | [ ] OPEN sharpness |
| TL.COMPLETE6 | Full physical completion of six-body parallel survivors | [x] CLOSED: at most two extras |
| TL.REDUCE5 / TL.ALL_TO_P | Five-body reduction and the whole two-load class | [x] CLOSED reduction to P.ALL |
| CY.ARC / CY.INCIDENCE / CY.DIRECTIONS | Physical circle-contact budget, junctions and load directions | [x] CLOSED necessary restrictions |
| G2.X / G4 / G5.U | Unrestricted lower bound and all equality packings | [ ] OPEN/BLOCKED |
| G6–G8 | Independent audit, standard-kernel Lean and integration | [ ] NOT COMPLETED |

**Radius premise:** high-radius graph exclusions assume 79/40<=R<=sqrt(Q). LOWER_WINDOW_FROM_EIGHT.md assembles the exact existing n=8 import and deletion implication, retaining its arithmetic-table dependencies; a standalone table-free proof needs a separate coarse bound. The new parallel-force theorem alone only needs q>9/4.

**Graph premise:** the <=19 planar translational support and <=27 physical force/torque incidence certificate are distinct. The body-pair graph is not assumed planar. Zero-stress physical contacts constrain geometry even though absent from that graph.

## 2. Finished coordinate and physical-stress reductions

The entire coordinate-separable branch is proved in COORDINATE_SEPARABLE_NINE_COMPLETE.md: rank/grid forces a four-chain, the large-zigzag branch is excluded, and the residual five-square complement closes through the (4,1) central cover or (3,2) five-element matching/frame switch. Do not reopen those branches to tighten small constants. A common separating frame is false globally.

SPARSE_MINIMIZER_STRESS.md supplies compact attainment, true-contact selection, explicit regularity and exact normalized stress. PLANAR_STRESS_CORE.md and ROTATION_STATIONARY_STRESS.md give separate planar and angular constructions. PHYSICAL_CONTACT_STRESS.md supplies joint force/torque at actual shared points with a planar contact-point incidence representation. RADIAL_BRIDGE_AND_LEAF_REDUCTION.md gives radial bridges, <=4 central circle-clear bridge-cover bodies and exact S/D loaded-leaf geometry.

These are universal necessary conditions on minimizers, not q0>=Q by themselves. The all-nine-square quantifier requires every unstressed completion square to remain.

## 3. Original finite tree cases and exact survivors

The six (s,v) origin-incidence profiles are exhaustive in the declared window; all tree radii there equal 17/4. Sources: TREE_BODY_LOCALIZATION.md and TREE_RADIUS_QUANTIZATION.md.

| Profile | Current status |
|---|---|
| TREE.20 (2,0) | CLOSED by full P.ALL capacity |
| TREE.11 (1,1) | CLOSED by full Y.ALL and P boundary capacities |
| TREE.12 (1,2) | CLOSED, cardinal-cage capacity <=8 |
| TREE.02 (0,2) | CLOSED: point-only strict-normal .P and shared-edge P boundary |
| TREE.03 (0,3) | CLOSED, annular angular capacity <=8 |
| TREE.04 (0,4) | CLOSED, central 2x2 block capacity <=8 |

### P.ALL — CLOSED whole-family capacity

Fixed aligned centers are (-3/2,0),(-1/2,tau1),(1/2,tau2),(3/2,0), with both tau in [-1/2,1/2]. P_ALL_COMPLETION.md proves that no FIVE other arbitrary physical unit squares fit D_(17/4).

- [x] Exact survivor reduction, including slider endpoints.
- [x] Flat solid row excluded.
- [x] Negative controls: one side can hold three squares; five extra centers can pass center/inscribed-disk relaxations without yielding physical squares.
- [x] Whole-square routing and coupled capacity over the full closed two-slider parameter square. The upper section theorem, open north-disk intersection, annular same-side pair exclusion and exact 19/120 cap force capacity at most one opposite any triple.
- [x] Both slider endpoints, arbitrary square frames, all separator owners and zero-coordinate/45-degree boundaries are retained.

### Y.ALL — CLOSED whole-family capacity

H=[-alpha,1-alpha]x[0,1], K=[0,u]+[0,v], u=(cos(theta),-sin(theta)), v=(-sin(theta),-cos(theta)), alpha in (0,1), theta in (0,pi/2), plus S(north),S(u),S(v). Y_ALL_COMPLETION.md proves that no FOUR other arbitrary squares fit D_(17/4).

- [x] Exact side/vertex normal form and force ratios sin(theta),cos(theta); angular endpoints reduce to P.
- [x] Genuine nonaligned core exists, so exclude completion, not the core.
- [x] WEDGE.2: complete capacity-one theorem for every screened pocket of aperture at most 135 degrees; WEDGE_135_CAPACITY_ONE.md.
- [x] HALF.3 classifies every upper E/W triple as the canonical aligned triple. Widening then proves capacity two in every strict terminal half-pocket.
- [x] Complete physical three-ray routing and the capacities one plus two exclude all four-extra completions. Angular limits reduce to the closed P family; zero-stress contacts remain physical obstacles.

Sources: REMAINING_TREE_TWO_FAMILY_REDUCTION.md, P_ALL_COMPLETION.md and Y_ALL_COMPLETION.md. The full P and Y capacities now close TREE.ALL; the P capacity also closes the entire exactly-two-load class through its earlier reduction. The radius-window condition remains explicit.

## 4. Cyclic necessary load and channel restrictions

Sources: CYCLIC_BLOCK_INVENTORY.md, ACUTE_LOADED_CONTACT_GRAPH.md, PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md.

- [x] **CY.L1–L2:** no unloaded positive appendage attached through one body; each endblock has a loaded nonarticulation body.
- [x] **CY.A1:** a circle-loaded square at q>2+sqrt(3) lies strictly in the 45-degree cone of each circle-contact corner.
- [x] **CY.A2:** physically touching loaded bodies have positive load-resultant dot product.
- [x] **CY.A3:** loaded physical NONCONTACT graph is connected, by total circle force zero. Actual zero-stress touching counts as contact.
- [x] **CH.1–2:** unloaded degree-two paths are normal minimum-distance channels; parallel graph paths between the same endpoints have the same direction/reserve.
- [x] **CH.3:** a degree-two unloaded body's neighbors cannot physically touch.
- [x] **CH.4:** two-loaded simple cycles in the window have six aligned bodies and q=17/4. Their completion to nine is now excluded by SIX_BODY_TWO_LOAD_COMPLETION.md.
- [x] **CH.C4:** all simple four-cycle load cardinalities are impossible.

## 5. NEW CY.TWOLOAD: entire two-loaded cardinality class

Source: TWO_LOAD_RECIPROCAL_RIGIDITY.md, initial 248202d and clarified 9fad28e. This is not restricted to trees or simple cycles.

### TL.R — planar force polygons [CLOSED hand]
- [x] **TL.R1:** antisymmetric edge vectors with zero vertex sum integrate to dual face potentials on a sphere embedding.
- [x] **TL.R2:** physical cyclic direction order makes each finite vertex's reciprocal polygon weakly convex with nonnegative signed area.
- [x] **TL.R3:** the signed areas sum to zero by opposite appearances of every dual edge; repeated face occurrences are retained.
- [x] **TL.R4:** a degree-two exterior vertex contributes zero area, so all finite areas vanish and connectedness forces parallel edge vectors.

### TL.P — physical applicability [CLOSED hand]
- [x] Square outward-normal order matches boundary incidence order. At shared contact junctions inward force aggregates lie in disjoint square tangent cones, preserving cyclic order.
- [x] One/two adjacent circle atoms aggregate into one exterior port; an empty outer chord cap justifies the embedding and direction order.
- [x] With exactly two loaded bodies the exterior vertex has two opposite balanced ports. No body-graph planarity is assumed.
- [x] Extreme-ray positivity at multiple contact points recovers parallelism of every ORIGINAL body-pair force from aggregate incidence forces.
- [x] **TL.P.ALL:** every physical two-loaded component at q>9/4 has one common pair-force direction.

### TL.G — radius, layers and cardinality [CLOSED hand necessary geometry]
- [x] Directed contacts increase the common projection. Every unloaded body has incoming/outgoing flux, so every body lies on a path from the unique loaded source to the unique loaded sink.
- [x] Endpoint parallel forces give radial S/D forms. Unloaded opposite-face force/torque balance gives width 1 or sqrt(2).
- [x] Comparing exact path reserves with endpoint support gaps in the radius window gives **q=17/4**, both loaded centers at (+/-3/2,0), every internal body aligned in x=+/-1/2, and exactly two internal bodies per directed path.
- [x] Strictly exposing point-only normal selection gives layer heights in (-1,1), at most two bodies per layer and total size **4,5 or 6**.
- [x] Positive triangles and all two-loaded 7–9-body components are excluded.
- [x] **TL.COMPLETE6:** SIX_BODY_TWO_LOAD_COMPLETION.md proves at most two arbitrary extras for the entire six-body layer family.
- [x] **TL.REDUCE5:** FIVE_BODY_TWO_LOAD_REDUCTION.md proves actual P containment or at most three extras across the full five-body domain.
- [x] **TL.ALL_TO_P:** every two-loaded nine-square completion in the window contains an actual P skeleton.
- [x] **P.ALL / TL.COMPLETE5 / TL.COMPLETE:** the full P capacity closes every exactly-two-load completion, including all five-body cores and cyclic cases.

**Exact controls:** a six-cycle has heights +/-3/5; a six-body theta graph has seven positive contacts; a five-body bridge-plus-cycle exists. A three-loaded nonaligned Y has nonzero reciprocal area and nonparallel forces. The six-body cores remain feasible, but their completion to nine is excluded; five-body cores reduce as above. The separate three-loaded Y completion is now excluded by Y_ALL_COMPLETION.md.

## 6. Whole coarse cell C1.4.b0 CLOSED

Source: FOUR_BODY_CYCLIC_CELL_CLOSED.md, commit 05e15a0.

- [x] **GRAPH:** exactly C4, diamond K4-e or K4 exhaust all biconnected simple four-body graphs.
- [x] **C4:** prior channel + loaded noncontact argument excludes every load cardinality.
- [x] **K4:** touching loaded clique is impossible.
- [x] **DIAMOND.LOAD:** the only surviving assignment has exactly the two nonadjacent tips loaded.
- [x] **DIAMOND.GEOM:** TL.P.ALL makes its pair forces parallel; its positive triangles would be three pairwise touching, pairwise interior-disjoint positive-length projection intervals, impossible.
- [x] **ALL:** all orientations, contacts, load choices and five remaining physical completion squares are covered.

This changes the coarse ledger from one excluded/57 open to **two excluded/56 open**. It does not close triangle blocks with attachments or larger cells whose loaded subsets can have three or more bodies.

## 6B. Entire boundary-only component reduction

[CIRCLE_CONTACT_ANGULAR_ORDER.md](CIRCLE_CONTACT_ANGULAR_ORDER.md) proves that the graph of all physical circle-touching squares consists of paths, or is one seven-cycle. The proof combines center angular separation >36 degrees, contact span <72 degrees, and complete square shadows <60 degrees. It includes circle-touching squares with zero circle multiplier and contacts with zero pair multiplier.

- [x] **CY.BOUNDARY.ORDER / SHADOW:** full all-angle geometric implications.
- [x] **CY.BOUNDARY.C7:** a positive component whose every body touches the circle is exactly C7 and contains every physical circle-touching square; nonradial contact torque excludes leaves.
- [ ] **CY.C7.COMPLETE:** two arbitrary circle-clear completion squares still must be excluded for the full family.
- [ ] **CY.MIXED.COMPLETE:** components with a circle-clear body still need a uniform capacity argument.

The exact regular ring below Q has only one completion slot, but does not prove regularity or capacity for all rings. The independent-square nonnegative measure method is also excluded by ADDITIVE_MEASURE_OBSTRUCTION.md. No additional coarse row is checked.

## 7. Remaining cyclic/global contracts

CYCLIC_CELL_LEDGER.md retains all 58 individual rows and their complete physical hypotheses. For each unchecked cell:

- [ ] Cover every block adjacency/articulation structure, not a canonical drawing.
- [ ] Impose actual contacts, force/torque, connected loaded noncontact and the new TL restrictions where applicable.
- [ ] Retain all 9-n other physical squares and zero-weight contacts.
- [ ] Prove a uniform sharp inequality or whole selected-component exclusion over all continuous positions/angles.
- [ ] Preserve all q=Q equality/zero-weight limits needed by the eventual theorem.

**O3.3.SHARP / O4 / O5 remain OPEN:** P.ALL, Y.ALL, TREE.ALL and all two-loaded completions are closed at their stated scopes. The general boundary-only C7 and mixed 3–7-loaded noncollinear cyclic configurations still require full physical capacity inequalities. A uniform global argument is preferable to 56 separate angle-grid searches.

**G2.X/G4:** the lower-window prerequisite is now explicitly assembled, but complete sharp cyclic coverage is still required before minimizer attainment can exclude q<Q. **G5.U:** all unrestricted equality packings still need necessity/converse. **G6–G8:** independent full audit, standard-kernel Lean and integration are not done.

## 8. Actual exact execution and audit priorities

The source check_two_load_reciprocals.py at commit 0d4c958 was matched to its Git blob/SHA-256 and actually run at **2026-10-23 19:32:40 UTC**, Python 3.13.5, exit 0. TWO_LOAD_RECIPROCAL_EXACT_CHECK.json records 12 radius inequalities, all 64 labelled four-body graph/load cases and five physical stress/reciprocal examples. An identical source rerun passed at **19:44:32 UTC**.

The checks include every physical corner, every SAT pair, true force point, center/torque balance, planar rotation system, dual integration and signed-area cancellation. These finite checks are supplementary: the general analytic proof must still be independently audited.

Critical audit items: junction direction order; exterior-port aggregation and cap emptiness; face-potential existence with repeated faces; convex polygon area implication; recovery of constituent pair normals; and strict-normal height limits. The corrected report preserves the three-loaded Y areas +4/3 and -4/3, not zero.

**Progress logging:** finished implications and honest residuals are recorded in TWO_LOAD_PROGRESS.md, continuing the earlier logs. Tick only whole quantified gates; no completion percentages and no unsupported Lean/CI claims.
