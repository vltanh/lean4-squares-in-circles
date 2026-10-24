# n=9: deep ticked roadmap and ordered proof execution

**Branch:** `research/nine-tablefree-hand`; **PR:** #11, draft.  
**Reconciled source:** `7059d00eff82bf4b9b15288e371097bb31e4cb38`.  
**Checkpoint:** October 23, 2026, America/Chicago; the append-only evidence log retains explicit UTC provenance.

**T9 and unrestricted equality remain OPEN.** The complete P/Y arguments exclude all selected positive trees and all exactly-two-loaded components from a nine-square packing in the declared radius window. A physical certificate can be selected with **one planar positive component**, all physically circle-touching vertices on its exterior face, and at most 27 positive scalar atoms. The remaining component is cyclic, has 5–9 bodies, and has 3–7 noncollinear circle-loaded resultants. Every other physical square has zero stress and remains in the problem.

The remaining lower-bound split is exhaustive: **G3.B**, a boundary-only C7 with two completion squares; or **G3.M**, a mixed cyclic component containing a circle-clear body, with all 9-m completion squares retained. The 58-cell coarse inventory has three whole cells closed and 55 open. Subgate counts are not completion percentages.

## Ordered execution and gate-closing rule

| Order | Gate | Exact deliverable | Current state |
| --- | --- | --- | --- |
| 1 | G3.M4.0 | Every four-body triangle-plus-leaf core, complete S/D articulation cover and two-region routing | CLOSED hand; TRIANGLE_LEAF_CORE_REDUCTION.md |
| 2a | G3.M4.D.PARALLEL | Both articulation reactions horizontal, all application means and loaded-neighbor poses | CLOSED hand; full branch excluded |
| 2b | G3.M4.D.OBLIQUE | Both articulation corners lie inside loaded-neighbor sides, all B/C contact types | CLOSED hand; full branch excluded |
| 3 | G3.M4.S | All side-normal-leaf cores: aligned shared-side sliders plus both tilted-vertex branches | CLOSED hand; the entire core is impossible |
| 4 | G3.M4.ALL | Combine D/S and their degeneracies; close the entire C1.3.b1 cell | CLOSED hand; independent assembly audit passed |
| Parallel whole branch | G3.B.CAP | Exclude two arbitrary completion squares for every selected positive boundary C7 | OPEN; entire free-normal branch CLOSED; all-owned geometry active |
| 5a | G3.M5 | Four complete five-body cells, all four extras retained | OPEN; full chain and same-articulation layouts closed, C4 hole empty, biconnected graph/load cover complete |
| 5b | G3.M6–M9 | Process the larger mixed cells by component size and the finite semantic cover below | OPEN |
| 6 | G4 | Assemble the unrestricted sharp lower bound with the exact lower-window import | BLOCKED by G3 |
| 7 | G5 | Necessity and converse for every equality packing, including free centers and rotations | OPEN |
| 8 | G6–G8 | Full dependency audit, subsequent standard-kernel formalization and integration | NOT COMPLETE |

A gate closes only when its stated universal implication is written, all boundary states are retained, its prerequisites are identified, and the proof is checked. A reduction closes only its own structure statement. A proof of one contact-owner pattern does not close its parent until the other patterns are covered. Alternative proof routes are joined by **OR**, not counted as cumulative obligations or as separate mathematical cases.

The finite cover keeps continuous radii, centers, orientations, contact coordinates and weights as universally quantified variables. It does not turn those domains into angle boxes. A failed proposed normalization is removed from the execution path and recorded as a control.

## Current proved inputs feeding the open gates

| Input | Exact scope | Source |
| --- | --- | --- |
| Lower window | Delete one body and import the actual n=8 theorem to obtain R>=79/40; imported table dependencies explicit | LOWER_WINDOW_FROM_EIGHT.md |
| Physical certificate | Actual shared force points, force and torque balance, strict selected point normals, <=27 atoms | PHYSICAL_CONTACT_STRESS.md |
| Planar selection and uniqueness | One planar positive body component; all physical circle contacts on the exterior face | PHYSICAL_BODY_GRAPH_UNCROSSING.md; UNIQUE_POSITIVE_COMPONENT.md |
| Trees and two loads | Every such nine-square completion excluded in the window | TREE_AND_TWO_LOAD_COMPLETION.md |
| Boundary geometry | At most7 circle-touching bodies; >40-degree center gaps; touching pairs consecutive; all-boundary positive graph=C7 | CYCLIC_GLOBAL_CONTINUATION.md; CENTERED_INNER_ARC.md; CIRCLE_CONTACT_ANGULAR_ORDER.md |
| Simple cycles | At most8 bodies in a selected simple positive cycle | SIMPLE_POSITIVE_CYCLE_BODY_BOUND.md |
| C7 localization | Convex force-concurrence polygon containing0; all completion squares lie inside it | C7_FORCE_POLYGON.md; C7_COMPLETION_LOCALIZATION.md |
| Contact-hole capacity | For k=3,4,5,6, free area <=(k/4)cot(pi/k), hence interior capacities 0,1,1,2 | CONTACT_RING_HOLE_AREA.md |
| Boundary-pair exterior pocket | Every touching pair of circle-touching squares has an empty exterior pocket in the window | CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md |
| Triangle-plus-leaf reduction | Complete S/D articulation cover, three-load cone and exact routing into two residual regions | TRIANGLE_LEAF_CORE_REDUCTION.md |
| Entire S-leaf branch | No positive triangle-plus-leaf core with a radial S leaf in the window | S_LEAF_TRIANGLE_EXCLUSION.md |
| Boundary C7 center diameter | Every pair of centers is at distance<3, with arbitrary frames and no stress premise | BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md |
| D reaction localization | Both triangle reactions act left; exact parallel/opposite-corner alternatives and height formula | D_LEAF_ARTICULATION_CONTACT_LOCALIZATION.md |
| D generic selection | No point-only vertex/vertex articulation edge in the selected D star; planarity, thinning and uniqueness retained | D_LEAF_GENERIC_CONTACT_SELECTION.md |
| Entire oblique D branch | No selected nonparallel D articulation, all BC owners and circle masks, full height domain | D_LEAF_NONPARALLEL_OWNER_EXCLUSION.md |
| Entire parallel D branch | No horizontal-reaction D core, including shared-side means, arbitrary neighbor frames and all circle masks | D_LEAF_PARALLEL_LEFT_EXCLUSION.md |
| Complete four-body mixed cell | No selected C1.3.b1 core; positive cyclic component has at least five bodies | TRIANGLE_LEAF_CELL_CLOSED.md |
| No positive K4 subgraph | A small physical embedding has no triangle enclosing another body center; K4 is impossible throughout the selected inventory | NO_POSITIVE_K4_SUBGRAPH.md |
| Boundary common-neighbor obstruction | No two selected vertices have three common positive circle-touching neighbors | NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md |
| Five-body biconnected graph/load cover | All ten abstract types reduced to C5, house and four-path fan, with all necessary positive-load masks | FIVE_BODY_BICONNECTED_REDUCTION.md |
| General fixed-point tip selection | Every unique-circle-corner degree-two star with distinct fixed applications has no free vertex edge, even with two clear neighbors; coincident radial-D exception retained | GENERAL_FIXED_TIP_NORMAL_SELECTION.md |
| Distinct-articulation domain and port order | Exactly three loads; no D/D, zero moment or R<=sqrt(17)/2; positive radial concurrence at nonparallel articulations | TRIANGLE_DISTINCT_LEAVES_DOMAIN.md; TRIANGLE_DISTINCT_LEAVES_PORT_ORIENTATION.md |
| Entire distinct D/S branch | Owner-independent near-origin support and unit-square directional span exclude the whole core, with all four extras retained | TRIANGLE_DISTINCT_MIXED_LEAVES_EXCLUSION.md |
| Distinct S/S physical mask and positive control | C has exactly one physical circle corner; an exact positive five-body core below Q disproves universal core exclusion | DISTINCT_S_LEAF_CORE_AND_CORNER_MASK.md |
| High-center C7 contact types | Complete high-center local contact cover; every positively loaded two-owned body has center radius below23/16 and turn90 degrees | C7_HIGH_CENTER_CONTACT_TYPES.md |
| Entire same-articulation two-leaf layout | S/S, D/S and D/D excluded, with every actual side mean, corner owner, leaf weight and radius transition | TRIANGLE_TWO_LEAVES_SAME_ARTICULATION_CLOSED.md; TWO_D_LEAVES_ONE_TRIANGLE_ARTICULATION.md |
| Entire adjacent-load C4 leaf branch | A central normal channel cannot return through any boundary neighbor; all leaf/articulation types retained | FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md |
| Complete C7 free-normal exclusion | Every residual positive C7 has actual side-axis owners on all edges, with all owner transitions retained | C7_RADIAL_VERTEX_EDGE_EXCLUSION.md; C7_MIRROR_VERTEX_EDGE_EXCLUSION.md |
| Entire two-free-edge C7 branch | Both 2+2+3 and 2+2+2-plus-singleton cores excluded, retaining both remaining contact owners | C7_TWO_FREE_EDGES_EXCLUSION.md |
| S-leaf connected boundary neighbors | No connected physical graph of boundary neighbors of its articulation can contain every other load | S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md |
| Unit bypass of a normal channel | Exactly one side-normal transmitter; transverse bypass/transmitter separation, with arbitrary actual means, every bypass orientation and no radius premise | UNIT_BYPASS_NORMAL_CHANNEL.md |
| C7 free-edge graph and block profiles | At most two free edges; explicit length2–5 pinned profiles and two surviving local vertex-contact types | C7_PINNED_VERTEX_CONTACT_TYPES.md |
| Entire two-edge triangle arm | All leaf/transmitter types, articulation frames and circle/contact masks excluded | TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md |
| C4-plus-leaf inner capacity | Zero inner capacity for every load assignment and contact degeneracy; four extras exterior | FOUR_CYCLE_LEAF_HOLE_EMPTY.md |
| C7 fixed-point selection | One-circle-corner fixed-application stars cannot retain free vertex normals | C7_FIXED_APPLICATION_GENERIC_SELECTION.md |
| C7 radial geometry | Radial runs at most two, at most four radial bodies, no parallel radial pair | C7_TWO_CIRCLE_CORNER_BLOCKS.md |
| C7 shared-side block selection | Every free-vertex-incident block has a unique doubly loaded radial endpoint, including variable application means | C7_SHARED_SIDE_BLOCK_GENERIC_SELECTION.md |
| Two-contact span | End centers of two boundary contacts are less than 3sqrt(3)/2 apart in the high-radius range | BOUNDARY_TWO_CONTACT_SPAN.md |
| Strict center-cover piercing | Every unit enclosed by a ring whose centers lie in an open radius3/2 disk contains its center in its open interior | CENTER_COVER_PIERCING.md |

These hand manuscripts have different audit histories. The newly reviewed local arguments do not replace G6's full-chain audit. No Lean compilation or CI has been run.

## Canonical sources and proof-status vocabulary

- [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md): every one of the 58 cells individually recorded, now three [x] and 55 [ ].
- [TWO_LOAD_PROGRESS.md](TWO_LOAD_PROGRESS.md): current UTC proof commits, exact pinned execution, corrected report provenance and still-open parents.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): all six tree profiles and their complete P/Y capacities.
- [G2_SUBGATES.md](G2_SUBGATES.md): live mathematical status.
- [QUADRANT_BLOCK_PROGRESS.md](QUADRANT_BLOCK_PROGRESS.md), [ORIGIN_POCKET_PROGRESS.md](ORIGIN_POCKET_PROGRESS.md), [PROGRESS_LEDGER.md](PROGRESS_LEDGER.md): earlier append-only histories.

**[x] CLOSED hand** means a complete analytic implication is written with its stated hypotheses and boundary cases. Independent audit and Lean verification are separate. **[ ] OPEN** means the universal implication has not been proved. **CLOSED reduction** is a necessary structure theorem, not automatically q>=Q. **REJECTED** is a false normalization with an exact counterexample.

## 0. Target, global dependency map and indispensable distinctions

Put Q=1105/256 and q0=17/4. Construction gives R9<=sqrt(Q). The missing target is:

> **T9:** every nine independently oriented closed unit squares with disjoint open interiors inside a disk of radius R satisfy R^2>=Q.

No common separating frame, row, central square or prescribed stress graph is an original hypothesis. The selected unique positive component is studied **with all the other physical squares**, including every zero-stress body and every zero-weight physical contact.

| Proof route | Complete reduction or theorem | Remaining obligation |
|---|---|---|
| Model and minimizer | Exact squares, attainment, true physical force/torque certificate | Assemble the unrestricted sharp theorem |
| Common-coordinate class | Entire class proved, including conditional equality skeleton | A common frame is not available globally |
| Positive trees | Six profiles, full P/Y capacities, all completions excluded; lower window imported explicitly | No remaining geometry in this component class |
| Exactly two loaded bodies | Parallel forces, q=17/4, 4–6 aligned bodies; every completion excluded | No remaining geometry in this load class |
| Components whose bodies all touch the circle | Exactly one physical C7; includes all circle-touching squares | Exclude TWO arbitrary circle-clear completion squares |
| Components with a circle-clear body | 3–7 noncollinear resultants; circle-touching induced graph is paths or C7 | Uniform sharp physical completion inequality |
| Cyclic inventory | 21 profiles and 58 coarse cells; C1.3.b0, C1.4.b0 and C1.3.b1 excluded | 55 full geometric cells, or a uniform replacement |
| Cap, row, pocket and quadrant tools | Complete local hand implications at stated hypotheses | Apply full-square routing without assumed normalizations |
| Final assembly | Construction and explicit dependency contracts | G4 radius, G5 equality, G6 full audit, G7 Lean, G8 integration |

### G0.W Explicit radius-window prerequisite

Tree quantization, channel/loaded-graph exclusions and new two-load high-radius quantization use **79/40<=R<=sqrt(Q)**. LOWER_WINDOW_FROM_EIGHT.md supplies this by deleting one square and applying the actual existing n=8 declarations, with their current proof dependencies. A standalone table-free n=9 proof must replace that import with an independent coarse hand bound. The parallel-force theorem itself only assumes q>9/4; geometric capacity statements directly in D_(17/4) do not need the lower-window input.

- [x] **W.1** All window-dependent manuscript hypotheses are explicit.
- [x] **W.2** LOWER_WINDOW_FROM_EIGHT.md pins optimal_radius, selected_stationary.q_lower, the radius definitions, and the exact physical deletion implication. The n=8 arithmetic-table dependencies are explicit.
- [ ] **W.3** Supply an independent hand R>=79/40 argument if standalone table-freedom is required.

### Representation and scope rules

1. The <=19-term planar translational support and <=27-atom physical torque-balanced contact-incidence certificate are distinct. No unproved 19-term planar-body torque theorem is imported.
2. The physical **incidence** graph is planar. PHYSICAL_BODY_GRAPH_UNCROSSING.md now also permits selection of a planar positive **body-pair** graph, and UNIQUE_POSITIVE_COMPONENT.md proves that this selected certificate has just one positive component. These are existence statements about the selected stress. Block sizes, bridges and triangles below concern its body-pair graph.
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
- [x] **QCAP.P / QCAP.Y** Full-square routing and coupled P/Y capacities are proved in P_ALL_COMPLETION.md and Y_ALL_COMPLETION.md.
- [ ] **QCAP.GLOBAL** The quadrant theorem does not by itself give unrestricted sharpness.
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

## G2.O3.2.TREE — All positive tree completions [CLOSED hand in the declared window]

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
| TREE.20 (2,0) | [x] CLOSED by full P.ALL capacity |
| TREE.11 (1,1) | [x] CLOSED by full Y.ALL and P endpoint capacities |
| TREE.12 (1,2) | [x] CLOSED: cardinal cage gives <=8 total squares |
| TREE.02 (0,2) | [x] CLOSED: point-only strict-normal .P and shared-edge P boundary |
| TREE.03 (0,3) | [x] CLOSED: origin angular/annulus capacity gives <=8 total |
| TREE.04 (0,4) | [x] CLOSED: central 2x2 block gives <=8 total |

- [x] TREE_FINITE_COMPLETIONS.md supplies the arbitrary-extra-orientation CAGE/BLOCK capacities.
- [x] TREE02_POINT_CONTACT_COMPLETION.md preserves its strictly exposing central normal premise and routes the shared-edge boundary rather than deleting it.
- [x] REMAINING_TREE_TWO_FAMILY_REDUCTION.md covers EVERY remaining tree geometry by P or Y.
- No tree lemma makes a nonbridge cyclic edge radial.

### TREE.P — All staggered four-square paths plus FIVE other squares [CLOSED hand]

Exact fixed centers:

    (-3/2,0), (-1/2,tau1), (1/2,tau2), (3/2,0),
    -1/2 <= tau1,tau2 <= 1/2,

with FIVE additional independently oriented squares inside D_(17/4).

- [x] **P.0** All TREE.20, shared-edge TREE.02.E and aligned TREE.11 endpoints are retained, including slider boundaries.
- [x] **P.FLAT** tau1=tau2=0 is excluded by solid-row completion.
- [x] **P.N1** Three squares can fit on one side of a staggered row; separate two-per-side capacities are false.
- [x] **P.N2** Five candidate centers pass center-radius, inscribed-disk obstacle clearance and mutual distances; actual square supports must be used.
- [x] **P.1 ROUTING** The fixed path screens the full horizontal axis; each extra lies wholly in an upper or lower half-pocket.
- [x] **P.2 COUPLED CAPACITY** The complete section theorem gives capacity three per side. Every upper triple forces lower capacity at most one, so five extras are impossible over the entire two-slider parameter square.
- [x] **P.3 ENDPOINTS** Both signs, x_A=0, 45-degree axes, and all |tau_i|=1/2 boundaries are included using only physical nonoverlap.
- [x] **P.HIGH** Every square with center height above 3/sqrt(5) contains (0,sqrt(5)/2) strictly; the threshold is sharp. HIGH_CENTER_COMMON_POINT.md.
- [x] **P.CAP** Complete quantitative terminal-cap exclusion at section threshold 19/120, all actual separating axes retained. TERMINAL_CAP_SECTION_EXCLUSION.md.
- [x] **P.DISK** LOW_OUTER_SQUARE_MEETS_N_DISK.md and HIGH_OUTER_SQUARE_MEETS_N_DISK.md prove strict intersection with the open north disk.
- [x] **P.ANNULAR** ANNULAR_SAME_SIDE_PAIR_EXCLUSION.md excludes every annular same-side pair with horizontal gap greater than 1/2.
- [x] **P.SECTION** P_HALF_POCKET_SECTION_PROOF.md proves the complete y=1 section theorem and upper capacity three.
- [x] **P.ALL** P_ALL_COMPLETION.md excludes five extras for every member. The quantitative proof is independent of the stronger HALF.3 classification.

### TREE.Y — Whole side/vertex fan plus FOUR other squares [CLOSED hand]

Exact domain:

    0<alpha<1, 0<theta<pi/2,
    H=[-alpha,1-alpha] x [0,1],
    u=(cos(theta),-sin(theta)), v=(-sin(theta),-cos(theta)),
    K=[0,u]+[0,v], with radial terminals S(north), S(u), S(v).

- [x] **Y.0** Every nonaligned residual TREE.11 has this five-body form; force ratios are sin(theta),cos(theta). Angular endpoints reduce to P.
- [x] **Y.N** Nonaligned physical cores exist; their completion, not core existence, is the missing theorem.
- [x] **Y.1 ROUTING** The actual H/K/terminal union screens three entire rays, so every whole extra square lies in a single pocket. The K quadrant has no extra slot.
- [x] **Y.WEDGE.2** Every screened origin pocket of aperture at most 135 degrees has capacity one, with arbitrary square orientations. WEDGE_135_CAPACITY_ONE.md.
- [x] **Y.CAP** All orientations and owners in the positive terminal-cap inequality, plus right-owned downward separation, are covered analytically. No parameter table or interval cover is used.
- [x] **HALF.3** HALF_POCKET_TRIPLE_RIGIDITY.md proves the unique canonical upper E/W triple using exact one-sided tilt coupling.
- [x] **Y.STRICT** Widening to a half-plane and canonical equality give capacity two for every screened pocket of aperture strictly below 180 degrees.
- [x] **Y.2 CAPACITY** The two possible pockets have apertures summing to 270 degrees; capacities one plus two give at most three extras throughout the whole alpha/theta domain.
- [x] **Y.3 BOUNDARY** The theta=0 and pi/2 limits are P members, already covered by its closed slider domain.
- [x] **Y.ALL** Y_ALL_COMPLETION.md excludes every four-square completion.

**TREE.ALL [x] CLOSED hand conditional on the declared window:** P.ALL + Y.ALL + the four previously closed branches exclude every selected positive tree component in a nine-square packing. TREE_AND_TWO_LOAD_COMPLETION.md gives the exact assembly. G0.W.2 now supplies the explicit n=8 lower-window import; G0.W.3 remains the optional replacement for a standalone table-free derivation.

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
- [x] **TL.COMPLETE6** SIX_BODY_TWO_LOAD_COMPLETION.md excludes the entire three-extra completion, including theta/contact-degenerate variants, by proving at most two extras.
- [x] **TL.REDUCE5** FIVE_BODY_TWO_LOAD_REDUCTION.md proves actual P containment or at most three extras for every five-body core.
- [x] **TL.ALL_TO_P** Every two-loaded nine-square completion in the window contains a genuine P skeleton. Singleton heights are derived by torque; other heights are not assumed in the P interval.
- [x] **P.ALL / TL.COMPLETE5 / TL.COMPLETE** P_ALL_COMPLETION.md closes the last capacity. Every selected exactly-two-load component, including cyclic ones, is excluded from a nine-square packing in the declared window.

#### New completion tools and global load restrictions

- [x] **TL.CENTER** DIAGONAL_CENTER_EXCLUSION.md proves strict center x<1 when avoiding the right terminal, hence -1<x<1 when avoiding both.
- [x] **TL.CAP** HALF_CAP_CENTER_SEPARATION.md gives unavoidable interior points (+/-3/7,5/4), cap capacity two, and opposite center signs for a pair.
- [x] **TL.PAIR** HALF_DISK_CLOSE_CENTER_RIGIDITY.md classifies all half-disk pairs with horizontal center gap at most 1/2, including equality.
- [x] **CY.ARC** CYCLIC_GLOBAL_CONTINUATION.md limits physical circle-touching bodies to seven in the declared window.
- [x] **CY.INCIDENCE** No point belongs to three circle-touching squares when R>sqrt(2).
- [x] **CY.DIRECTIONS** Every loaded body's resultant direction pierces its own square on the radius-5/4 circle, so distinct loaded resultants have distinct directions and a balanced collinear family has exactly two bodies.
- [ ] **CY.MULTILOAD** The remaining 3–7-loaded noncollinear geometry, including all extra physical squares, is not sharply bounded by these necessary restrictions.

#### CY.BOUNDARY: angular order, shadow, and the remaining seven-cycle

Source: [CIRCLE_CONTACT_ANGULAR_ORDER.md](CIRCLE_CONTACT_ANGULAR_ORDER.md), commit 6f1d22e.

- [x] **CY.B1 ANNULUS** Every circle-touching center has radius strictly between 5/4 and 61/40.
- [x] **CY.B2 SEPARATION** CENTERED_INNER_ARC.md strengthens the separation to more than 2pi/9: every circle-touching square contains the entire closed centered 40-degree arc on the radius-5/4 circle in its open interior. A touching pair still differs by less than 2pi/5, so a physical contact cannot skip another circle-touching center.
- [x] **CY.B3 SHADOW** Every circle-touching square has angular shadow shorter than pi/3, by the full two-case corner calculation.
- [x] **CY.B4 GRAPH** The entire physical circle-touching graph is a disjoint union of paths, or is one C7. A six-cycle would cover all directions using six shadows of total length less than 2pi.
- [x] **CY.B5 TORQUE** A genuine contact between two circle-touching squares has nonzero moment about the origin; loaded or unloaded degree-one vertices are impossible in a positive component whose bodies all touch the circle.
- [x] **CY.B6 REDUCTION** Every positive component with at least one positive circle multiplier and all bodies physically circle-touching is exactly C7, even if some body circle multipliers vanish. It contains every physical circle-touching square.
- [ ] **CY.C7.COMPLETE** Exclude two arbitrary circle-clear additional squares for every allowed seven-cycle. The exact regular example is settled, but no regularity reduction exists for the full family.
- [ ] **CY.MIXED.COMPLETE** Bound components that contain a circle-clear body, retaining all remaining physical squares and their actual contacts. The boundary graph restrictions alone do not close them.

**Rejected proof shortcuts:** SEVEN_LOADED_RING_COUNTEREXAMPLE.md supplies a physical, force-and-torque-balanced seven-cycle below Q, and proves that particular ring has capacity one for arbitrary extras. ADDITIVE_MEASURE_OBSTRUCTION.md rules out every single nonnegative additive point-measure certificate of total mass below nine, via an exact fractional packing of mass 181/20. Neither item is counted as a new coarse-cell closure. The ring contact-coordinate expansion was corrected at commit 411924d; its global contact formula and subsequent stress/capacity identities were unchanged.

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
| 1 | (3),(4),(5),(6),(7),(8),(9) | 28 | C1.3.b0, C1.4.b0 and C1.3.b1 [x]; other 25 [ ] |
| 2 | (3,3),(3,4),(3,5),(3,6),(3,7),(4,4),(4,5),(4,6),(5,5) | 22 | all [ ] |
| 3 | (3,3,3),(3,3,4),(3,3,5),(3,4,4) | 7 | all [ ] |
| 4 | (3,3,3,3) | 1 | [ ] |

**55 cells OPEN.** The full triangle-plus-leaf proof closes the third whole cell. Uniform restrictions still do not tick a larger cell when any physical realization or completion remains unresolved. Seek complete shared arguments across whole families, with continuous geometry retained.

### Uniform subsubgate contract for every unchecked cell C

- [ ] **C.1 GRAPH** Cover every internal block adjacency and articulation assignment in its size/bridge data.
- [ ] **C.2 LOAD** Impose actual nonnegative circle/contact forces, physical application points, torque, loaded endblocks, connected loaded noncontact, and TL where applicable.
- [ ] **C.3 GEOMETRY** Prove a uniform inequality over every admissible orientation/pose; do not select a canonical drawing without a reduction theorem.
- [ ] **C.4 COMPLETION** Include all 9-n other physical squares and zero-weight contacts. CY.UNIQUE now makes all these additional bodies zero-stress for the selected certificate.
- [ ] **C.5 SHARPNESS** Establish q>=Q for every complete nine-square realization, or exclude the entire component cell in the declared window.
- [ ] **C.6 EQUALITY** Retain all q=Q limits and free-square frames if the cell survives in global equality.

**CY.ALL remains OPEN:** finite coarse coverage and a strong two-load invariant are not a universal sharp capacity theorem.

---


## G3 — Deep finite execution tree for the remaining cyclic proof

The labels below refine the **remaining obligations**, not the numerical radius window. Let G be the selected positive body graph on m bodies, H the full physical touching graph on all nine bodies, B the set of physically circle-touching bodies, and L the positive circle-loaded subset. These are four different objects. Every case retains all nine actual squares.

### G3.0 Selected certificate and complete outer split

#### G3.0.P Physical selection [CLOSED hand]

- [x] **G3.0.P.1** Choose compatible strictly exposing normals at every point-only vertex/vertex contact before taking multipliers.
- [x] **G3.0.P.1.a** At a four-square junction choose opposite normals with matching positive absolute frame coefficients.
- [x] **G3.0.P.1.b** Avoid radial point normals away from 0; optional diagonal avoidance remains compatible.
- [x] **G3.0.P.1.c** BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md supplies a compatible finite determinant choice for every fixed-application unique-circle-corner degree-two star with at least one boundary neighbor. Shared-side means are explicitly outside that local lemma.
- [x] **G3.0.P.2** Obtain actual force-and-torque-balanced atoms from the physical feasible branch.
- [x] **G3.0.P.3.a** Replace both crossing opposite-pair forces by nonnegative shared-side endpoint forces at the same junction.
- [x] **G3.0.P.3.b** Preserve every body's total force and torque and the circle normalization.
- [x] **G3.0.P.3.c** Re-thin only surviving atom types to <=27; never restore an eliminated crossing.
- [x] **G3.0.P.4** Embed the selected body graph while retaining all physical circle-corner spokes.
- [x] **G3.0.P.5.a** Distinct positive components have nonalternating boundary ports.
- [x] **G3.0.P.5.b** Each balanced port set has all consecutive angular gaps <=pi.
- [x] **G3.0.P.5.c** A second balanced component cannot fit into one open gap, including the antipodal endpoint case.
- [x] **G3.0.P.5.d** The support-gap virial identity excludes contact-only components with no circle weight.
- [x] **G3.0.P.ALL** Exactly one positive component; all other bodies have zero stress.

#### G3.0.S Surviving graph split [CLOSED reduction]

- [x] **G3.0.S.1** Tree components are excluded by TREE.ALL.
- [x] **G3.0.S.2** Exactly two loaded bodies are excluded by TL.COMPLETE.
- [x] **G3.0.S.3** Every remaining component has 3–7 noncollinear loaded resultants.
- [x] **G3.0.S.4** If every positive-component body physically touches the circle, the component is C7 and includes all boundary-touching bodies: go to G3.B.
- [x] **G3.0.S.5** Otherwise a positive-component body is physically circle-clear: go to G3.M.
- [x] **G3.0.S.6** The triangle, all four-body biconnected components and the entire triangle-plus-leaf component are excluded. The selected unique cyclic component has at least five bodies; go next to G3.M5.
- [x] **G3.0.S.7** NO_POSITIVE_K4_SUBGRAPH.md excludes every K4 subgraph of the selected positive graph, including inside larger blocks. It does not make every graph outerplanar.
- [x] **G3.0.S.8** NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md excludes a K2,3 subgraph whose three-vertex part consists of physical boundary bodies: all those vertices would have to remain exterior after deletion, but a plane K2,3 has only two on its outside four-cycle.
- [x] **G3.0.TIP.FIXED** GENERAL_FIXED_TIP_NORMAL_SELECTION.md gives the full force/origin-moment determinant for any unique-physical-circle-corner degree-two star with two distinct fixed pair applications, including zero circle multiplier and two circle-clear neighbors.
- [x] **G3.0.TIP.NONRADIAL** If the other normal is not parallel to the circle corner, a vanishing free-normal coefficient forces a radial-D inner vertex and a second outward normal line through that vertex. Every distinct side/vertex possibility is impossible by the actual unit support geometry and R/sqrt(2)>R-1.
- [x] **G3.0.TIP.RADIAL** If the other normal is radial, translation balance forces the free normal to be radial too; finitely avoiding those directions closes this degeneracy without assuming a nonzero boundary-neighbor moment.
- [x] **G3.0.TIP.TWO_FREE** Distinct physical applications use independent junction parameters. The determinant is not identically zero on their product, so the full bad set has empty interior.
- [x] **G3.0.TIP.COINCIDENT** At coincident applications, torque forces either zero circle load, impossible in a pointed normal cone, or a radial-D inner vertex. This exact latter exception is retained rather than removed by a degenerate determinant.
- [x] **G3.0.TIP.PRESERVE** The finite physical prelist, matched junctions, zero-weight masks and surviving point normals remain valid under uncrossing/thinning. All choices precede multipliers and fit inside earlier open constraints. Genuinely variable shared-side means remain outside the fixed-point theorem.
- [ ] **G3.0.SHARP** Finish both G3.B and G3.M. The split itself supplies no sharp metric inequality.

### G3.B Boundary-only seven-cycle: complete two-square exclusion [OPEN]

#### G3.B.0 Full premise and closed routing

- [x] **G3.B.0.a** Seven actual circle-touching squares form the positive cycle, in circular order, with arbitrary individual frames.
- [x] **G3.B.0.b** Retain zero circle multipliers and one/two physical circle-corner states on each body.
- [x] **G3.B.0.c** At loaded vertices the two contact-force lines concur inside the actual square; clear two-force vertices use their transmission chords.
- [x] **G3.B.0.d** The concurrence polygon P is convex, contains 0, and follows actual positive contact-force lines.
- [x] **G3.B.0.e** Every extra square lies inside P and avoids all seven ring-square interiors.
- [x] **G3.B.0.f** Both remaining squares are physically circle-clear.

#### G3.B.N Simultaneous normal selection and radial endpoint blocks [CLOSED reduction]

Sources: C7_FIXED_APPLICATION_GENERIC_SELECTION.md, C7_TWO_CIRCLE_CORNER_BLOCKS.md and C7_SHARED_SIDE_BLOCK_GENERIC_SELECTION.md. All choices are made on the finite physical candidate list before multipliers, inside compatible strict normal intervals. This is a necessary selected-certificate reduction; none of the terminal capacity gates below is thereby closed.

- [x] **G3.B.N.FIXED.1** For a unique-circle-corner body with two fixed contact applications, derive the exact force/moment determinant for every positive-pair and nonnegative-circle-weight mask.
- [x] **G3.B.N.FIXED.2** Prove its coefficient in a free vertex normal is nonzero, including the diagonal inner-corner candidate and both fixed-force parallel/nonparallel alternatives.
- [x] **G3.B.N.FIXED.3** Avoid the finite bad directions simultaneously before KKT; retain the selected pair normals under actual junction uncrossing and conic thinning.
- [x] **G3.B.N.RADIAL.1** Classify the norms of every vertex of a one- or two-circle-corner body. A boundary vertex/vertex neighbor of a radial two-corner square is radial as well.
- [x] **G3.B.N.RADIAL.2** Classify every physical radial-pair contact and its complete common-normal cone. The center gap is gamma=2atan(1/(2d)), where d=sqrt(R^2-1/4)-1.
- [x] **G3.B.N.RADIAL.3** Choose an open strict normal interval near each predecessor's positive tangent. A three-radial run would force its middle circle resultant outside its nonnegative two-corner cone.
- [x] **G3.B.N.RADIAL.4** All runs have length at most two; the cyclic seven-body count gives at most four radial bodies and at least three unique-physical-circle-corner bodies.
- [x] **G3.B.N.RADIAL.5** Two parallel radial squares cannot occur in a physical C7. Their exact radius-5/4 arcs leave insufficient room for five other connected arcs, each longer than pi/4. This is a geometric theorem, not a stress specialization.
- [x] **G3.B.N.RADIAL.6** At a radial-pair endpoint, every fixed other contact violates the two-corner circle cone at the tangential limiting normal. The failure is strict and persists in an open interval.
- [x] **G3.B.N.RADIAL.7** Choose adaptively on each maximal physical radial run: keep the original choices for runs of length at least three, and choose the appropriate end of the common cone to exclude a two-run with either outside contact point-only. Distinct runs use distinct parameters.
- [x] **G3.B.N.RADIAL.8** Every surviving radial/radial edge therefore joins two nonsingleton pinned blocks; both other contacts are positive-length tangential shared sides. Radial singletons cannot meet free vertex edges.
- [x] **G3.B.N.BLOCK.1** Prelist every possible positive shared-side path, its two external point contacts, and every choice of one physical circle corner per body, including zero-load choices.
- [x] **G3.B.N.BLOCK.2** Build pure center velocities w_i=kappa_i Jz_i with nonzero kappa_i so all internal shared-side work vanishes, for every application mean on every shared segment.
- [x] **G3.B.N.BLOCK.3** Combine that virtual motion with rigid rotation about the origin to obtain the external two-contact determinant. Shared-side application coordinates are never fixed or discarded.
- [x] **G3.B.N.BLOCK.4** Every boundary/boundary contact point has norm strictly greater than R-sqrt(2). Use this to rule out radial collinearity of a vertex contact and any chosen circle corner, making the free-normal determinant nonzero.
- [x] **G3.B.N.BLOCK.5** Treat the single shared-side path closed by one point edge separately: the two external normals are coupled, but w_1 differs from w_k and the forbidden directions are still finite.
- [x] **G3.B.N.BLOCK.6** Avoid all bad directions inside the radial-run open intervals and all prior strict/matched-junction choices. Uncrossing only adds already-listed physical shared-side rows, and thinning only deletes rows.
- [x] **G3.B.N.BLOCK.7** A block incident to a surviving free vertex edge must contain a body with both circle-corner multipliers strictly positive; all at-most-one-active-corner masks have just been excluded.
- [x] **G3.B.N.BLOCK.8** Such a radial body cannot be internal to a shared-side path: the available tangential contact forces cannot balance its positive radial circle force. It is an endpoint or a singleton.
- [x] **G3.B.N.BLOCK.9** The no-parallel-radial theorem gives exactly one physical radial body in such a common-frame block, with both its corner weights positive.
- [x] **G3.B.N.COVER** The remaining exact contact-domain split is OWNED, where every positive edge has a genuine side-axis owner, or PINNED, where at least one free vertex edge survives and each incident shared-side block has the stated unique doubly loaded radial endpoint.

#### G3.B.N.OWNED Full side-axis-owned domain [OPEN; sole remaining high-radius C7 domain]

A side owner is an actual square feature, not a prescribed successor convention. A body may own zero, one or two incident contacts. An edge may have both owners when sides are parallel. Every such cyclic change must be included. The full free-normal exclusion below is complete and supplies no one-owner-per-body normalization.

- [x] **G3.B.N.OWNED.WORD_DOMAIN** On the ordered seven-cycle, label each edge by its preceding owner, succeeding owner or both owners. These3^7 formal labels cover every owned assignment; they are semantic labels, not physical pose samples. Invalid words may be removed only by proved implications.
- [x] **G3.B.N.OWNED.COUNT** Let v_j count bodies owning j incident edges, and let D count doubly owned edges. Counting owner incidences gives v_1+2v_2=7+D and v_0+v_1+v_2=7, hence v_2-v_0=D.
- [x] **G3.B.N.OWNED.ONE_WORD** If every body owns exactly one edge, D=0 and the cyclic arrows must point consistently around the whole cycle. Up to reflection this is one complete ownership pattern. This implication does not prove its hypothesis for arbitrary C7.
- [x] **G3.B.N.OWNED.HIGH.RANGE** C7_HIGH_CENTER_CONTACT_TYPES.md proves that |center|>=3/2 forces b<3/5 and a-b>27/20 in the circle-corner frame [a-1,a] times[b-1,b], a>=b>=1/2.
- [x] **G3.B.N.OWNED.HIGH.INNER_FACE** For a-b>1, any unit beyond the long-coordinate inner face has every corner strictly inside the disk. The proof includes all shared-side placements, while retaining differently owned contacts at the face endpoints.
- [x] **G3.B.N.OWNED.HIGH.OUTER_VERTEX** The outer adjacent vertex cannot be a neighbor-owned point contact when b<=1: its opposite-side translate is outside the disk, or at the endpoint would be a forbidden side-interior circle point.
- [x] **G3.B.N.OWNED.HIGH.COVER** Every high-center contact is a transverse owned side or a neighbor-owned inner vertex. Torque forces one upper and one lower contact; the explicit four-combination table retains every shared application interval and axis endpoint.
- [x] **G3.B.N.OWNED.HIGH.LOAD** Either strict neighbor-owned contact gives a positive radial circle component. A loaded high-center body owns zero or one normals. Two transverse owned contacts force zero total circle load, equal magnitudes and equal horizontal application means.
- [x] **G3.B.N.OWNED.TWO_OWNED** Every positively loaded two-owned body has a unique circle corner and uses both inward side axes. The inner-face lemma gives a-b<=1, hence center radius<23/16<3/2.
- [x] **G3.B.N.OWNED.TURNS** Every positively loaded two-owned body contributes a90-degree turn to the convex force polygon; every zero-load body has turn0. All physical circle masks and mean constraints remain. These local facts do not prove the global center cover.
- [ ] **G3.B.N.OWNED.HIGH.COUPLE** Combine the complete high-center contact table, low two-owner bodies and possible unloaded transmitters across every cyclic owner word; prove the full covering or two-square capacity implication without discarding transition words.
- [ ] **G3.B.N.OWNED.ONE.CHARTS** For that complete one-owner pattern, derive all physical contact equations, both signs of every body's relative frame, and all unique/two-corner and zero-weight endpoints.
- [ ] **G3.B.N.OWNED.ONE.RECURRENCE** Derive the exact stationary recurrence from real application points, force, torque and circle equations. Include nonconstant periodic solutions and every geometric range restriction.
- [ ] **G3.B.N.OWNED.ONE.BOUND** Prove the full center-cover, strict-piercing or actual capacity-one theorem for this entire ownership pattern.
- [ ] **G3.B.N.OWNED.TRANSITIONS.COVER** Cover every remaining owner word with a zero-/two-owner body or doubly owned edge, including all shared-side components and actual junction/side-feature limits.
- [ ] **G3.B.N.OWNED.TRANSITIONS.LOADS** Retain radial bodies with one or two positive corner weights, unique-corner bodies with positive or zero weight, and every shared-side mean over its full segment.
- [ ] **G3.B.N.OWNED.TRANSITIONS.GEOMETRY** Derive all physical shape and force/moment consequences at zero-owner and two-owner bodies; no owner transition is discarded because it fails a one-owner recurrence.
- [ ] **G3.B.N.OWNED.TRANSITIONS.BOUND** Prove the full capacity or covering theorem uniformly across all these owner words and their continuous realizations.

- [ ] **G3.B.N.OWNED.1** Give the complete cyclic owner/feature cover, including shared-side segments, endpoint contacts and coincident-owner transitions.
- [ ] **G3.B.N.OWNED.2** For each entire owner type, retain all physical one/two-circle-corner masks and every positive/zero weight choice.
- [ ] **G3.B.N.OWNED.3** Derive the exact physical contact, force and torque equations with the correct side applications and no uniform-tilt premise.
- [ ] **G3.B.N.OWNED.4** Prove a full radius-3/2 center cover, a strict common-piercing theorem, or the actual capacity-one statement across this whole domain.
- [ ] **G3.B.N.OWNED.5** Include every nonconstant periodic family and all owner/weight degeneration limits before closing OWNED.

#### G3.B.N.PINNED Free vertex edges with unique radial endpoints [CLOSED selected-core branch]

Source: C7_PINNED_VERTEX_CONTACT_TYPES.md, with the symmetric radial-run choice in C7_TWO_CIRCLE_CORNER_BLOCKS.md, Section8. These gates apply in R>=sqrt(17)/2; the smaller-radius C7 capacity is already closed by the origin-centered cover.

- [x] **G3.B.N.PINNED.CONTACT_RADIUS** Every common point p of two boundary squares satisfies |p|>=sqrt(R^2-1)-1, hence |p|>1/sqrt(2) in the residual window. One of the two tangent sectors has radial forward support at most one; no normal or vertex assumption is needed.
- [x] **G3.B.N.PINNED.PROFILES** Starting from the unique radial endpoint, every positive-length shared-side successor is forced by the circle equation and actual side overlap. The exact length2–5 center/corner profiles and every shared segment are written, with both traversal directions retained.
- [x] **G3.B.N.PINNED.VERTICES** Remove circle vertices, incoming-segment vertices and vertices below the contact-radius floor. The remaining squared vertex radii have disjoint ranges for every unequal pair of block lengths.
- [x] **G3.B.N.PINNED.L3_HIGH** Two length3 blocks sharing their high vertex have center-direction gap below40 degrees, contradicting the centered inner-arc theorem.
- [x] **G3.B.N.PINNED.L3_LOW** At one side-axis endpoint, the low-vertex stress requires its incoming mean above3/2. At the other, the previous mean lies below the radial shared segment. Strict failures persist on an open common-normal interval and retain zero circle loads.
- [x] **G3.B.N.PINNED.LOCAL_TYPES** The complete local free-edge list is radial/radial, or the unique outer-adjacent-vertex contact between two mirror blocks of length2. The latter four-body module is fixed by R up to global rotation/reflection.
- [x] **G3.B.N.PINNED.1** Contract all maximal shared-side blocks. Every free-incident block has at least two bodies, so at most three such blocks fit. A two-free-edge block must have one radial/radial edge and one unique/unique edge. Free cycles and disjoint free edges are impossible; at most two free edges survive.
- [x] **G3.B.N.PINNED.2** Every free-incident block has length at most5, so the full individual-block pose/side-segment list is complete. A length6 block against a radial singleton is excluded by the symmetric radial-run selection.
- [x] **G3.B.N.PINNED.ONE_RR.COVER** With exactly one free edge of radial/radial type, the unordered incident block lengths are (2,2), (2,3), (2,4), (2,5), (3,3), (3,4). The complementary path retains all other ring bodies and only owned point edges.
- [x] **G3.B.N.PINNED.ONE_RR.BOUND** C7_RADIAL_VERTEX_EDGE_EXCLUSION.md excludes all six length pairs uniformly. An owned far external point fixes every moment-normalized force and actual mean through a unique-corner block. A near-axis RR normal violates the radial circle cone for its fixed x>d; at x=d it fails for every strict nonaxis choice. All complementary paths and both extras remain.
- [x] **G3.B.N.PINNED.ONE_UU.COVER** With exactly one unique/unique free edge, its two length2 blocks form the exact mirror module; all three other ring bodies lie on the complementary owned path.
- [x] **G3.B.N.PINNED.ONE_UU.BOUND** C7_MIRROR_VERTEX_EDGE_EXCLUSION.md excludes every single mirror module. Its two common-cone endpoints force x=c and x=x_* at a radial shared side, while one fixed anchor normal cannot satisfy both circle cones. A strict endpoint failure persists in an open interval; all complementary paths, circle masks and actual means remain.
- [x] **G3.B.N.PINNED.TWO.COVER** With two free edges they form a three-block path, one edge of each type. The middle block and its unique/unique neighbor have length2; the other block has length2 or3. Thus the complete length list is 2+2+3, or 2+2+2 plus one additional unique-physical-circle-corner singleton on the owned complementary path.
- [x] **G3.B.N.PINNED.TWO.223** C7_TWO_FREE_EDGES_EXCLUSION.md excludes the entire 2+2+3 layout: its closing center gap exceeds60 degrees and both radii exceed sqrt(2), so those two squares cannot touch. No closing-owner or load specialization is used.
- [x] **G3.B.N.PINNED.TWO.222U** C7_TWO_FREE_EDGES_EXCLUSION.md retains both owners of the singleton/last-block contact and all shared means. Exact bounds on its two required points, with a full all-orientation two-point center lemma, force every singleton corner below411/200<sqrt(17)/2. Its required physical boundary contact is impossible even at zero multiplier.
- [x] **G3.B.N.PINNED.3** Both final exclusions retain the full nonnegative two-corner cone, all zero unique-body weights and every strict endpoint degeneration. Fixed means are deduced from force/torque, never substituted as a premise.
- [x] **G3.B.N.PINNED.4** The exclusions need only actual fixed external point/axis data at the selected block or anchor. Every other owned complementary path, owner transition and physical zero-weight contact remains arbitrary; the selected core is excluded independently of completion.
- [x] **G3.B.N.PINNED.5** The complete domain is excluded by simultaneous pre-KKT choices: adaptive radial-run intervals, the fixed-mean RR obstruction and the incompatible-endpoint UU obstruction. Uncrossing and thinning preserve all surviving point normals. The complete sources passed independent hand audits.
- [x] **G3.B.N.SIDE_AXIS** No free vertex/vertex edge remains in a selected positive high-radius C7. Every edge has a genuine side-axis owner; all zero-owner/two-owner transitions, shared sides and physical circle masks remain.
- [ ] **G3.B.N.ALL** Finish the entire OWNED capacity theorem. PINNED is closed; only then close B.CAP and the full boundary-only branch.

#### G3.B.CAP Required terminal theorem

- [ ] **G3.B.CAP.1** For every admissible ring, prove that its entire free completion domain cannot contain two interior-disjoint unit squares.
- [ ] **G3.B.CAP.1.a** Retain arbitrary centers and independent frames of both extra squares.
- [ ] **G3.B.CAP.1.b** Use actual square nonoverlap, including extra-to-extra separating axes and all ring obstacles.
- [ ] **G3.B.CAP.1.c** Include tangencies, parallel sides, shared-side contacts, two-circle-corner bodies and zero-load ring vertices.
- [ ] **G3.B.CAP.ALL** Conclude total capacity<=8 for this entire boundary-only branch.

#### G3.B.R Routes to CAP — alternatives, not additional geometric cases

**R.PIERCE OR R.COVER OR R.DIAM OR R.CLASSIFY OR a direct capacity argument** suffices, provided every extra premise is proved.

- [ ] **G3.B.R.PIERCE.1** Prove0 lies in the **open interior** of every admissible completion square, or prove a common strict piercing point for the entire completion domain.
- [ ] **G3.B.R.PIERCE.2** If only closed containment of0 is obtained, separately exclude two squares meeting0 only on their boundaries; closed piercing alone is insufficient.
- [x] **G3.B.R.COVER.0** CENTER_COVER_PIERCING.md proves the all-orientation radial-tail statement: a disjoint square meeting the outward radial tail of a unit T with p outside its open interior has center distance at least3/2 from p.
- [x] **G3.B.R.COVER.1** Therefore an open radius3/2 disk containing every ring center gives a common strict interior point for every enclosed unit, and completion capacity<=1. Contact tangencies and all separator owners are included.
- [x] **G3.B.R.COVER.2** A minimum enclosing center disk is determined by two antipodal centers or an acute supporting triple; the two-point case has radius<3/2 by DIAM.2.
- [x] **G3.B.R.COVER.3.a** The acute-triple graph gaps sum to7 and are, up to symmetry, (1,1,5), (1,2,4), (1,3,3), (2,2,3).
- [x] **G3.B.R.COVER.3.b** Pattern(1,1,5) has two sides<=sqrt2; acuteness and the sine rule give circumradius<=2/sqrt3<3/2.
- [x] **G3.B.R.COVER.3.c** If R<sqrt(17)/2, the usual circle-containment center bound puts every ring center in the open radius3/2 disk centered at0.
- [x] **G3.B.R.COVER.4.124** BOUNDARY_TWO_CONTACT_SPAN.md proves distance<3sqrt(3)/2 along two contacts. In a supporting triangle of circumradius>=3/2, the one-edge opposite angle is<pi/6 and the two-edge opposite angle is<pi/3, contradicting acuteness. Thus the entire(1,2,4) type is excluded.
- [ ] **G3.B.R.COVER.4.133** Exclude the entire pattern(1,3,3) for a positive-stress C7, including unequal center radii, independent frames, all side-owner directions, every owner transition and all shared application means.
- [ ] **G3.B.R.COVER.4.223** Exclude the entire pattern(2,2,3) for a positive-stress C7, using the actual force/torque equations. The corresponding unstressed statement is false.
- [x] **G3.B.R.COVER.CONTROL** C7_CENTER_COVER_GEOMETRIC_OBSTRUCTION.md gives exact unstressed physical rings of type(2,2,3), at Q and strictly belowQ, with covering radius>3/2. Its outgoing-contact torque identity proves that these rings have no positive C7 stress. A purely geometric cover theorem is REJECTED.
- [ ] **G3.B.R.COVER.4.boundary** Include all acute/right transition limits, multiple supporting centers and shared-side contacts. A right supporting triangle is already covered by its antipodal pair.
- [ ] **G3.B.R.COVER.5** Assemble a single open disk of radius3/2 containing all seven centers, then apply COVER.1 and the established localization theorem to close B.CAP.
- [ ] **G3.B.R.DIAM.1** Prove that a contact cycle of at most 7 unit squares enclosing two unit squares has boundary-center diameter>=3, without aligning the inner squares.
- [x] **G3.B.R.DIAM.2** BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md proves every physical boundary C7 has center diameter<3. The proof bounds entire angular shadows, then encloses all possible distant endpoint sectors in one disk of radius<3/2. No stress or regularity assumption is used.
- [ ] **G3.B.R.DIAM.3** Once DIAM.1 is proved, combine it with the completed DIAM.2. A far-vertex span>=4 does not supply the missing center-diameter lower bound.
- [ ] **G3.B.R.CLASSIFY.1.a** Cover every cyclic assignment of vertex/side and side/side ownership, retaining two-owner/zero-owner transitions.
- [x] **G3.B.R.CLASSIFY.1.b** The entire selected free-vertex-normal branch is excluded by the RR and mirror-module theorems. All one/two-circle-corner states and zero weights remain in the explicit OWNED domain; no one-owner normalization is inferred.
- [ ] **G3.B.R.CLASSIFY.2** Derive an exact stationary recurrence for each entire surviving ownership type.
- [ ] **G3.B.R.CLASSIFY.3** Classify all periodic solutions, including nonconstant ones and all transition boundaries.
- [ ] **G3.B.R.CLASSIFY.4** Prove capacity<=1 for every resulting family and prove the cover is exhaustive.

The regular C7 is a completed example with capacity 1, not an exhaustive stationary classification. The local concurrence and support bounds alone do not justify a one-owner assumption. The area theorem for k<=6 does not supply capacity 1 for k=7. The completed implications and reductions are marked individually; no unfinished terminal capacity route is promoted to a proved premise.

### G3.M Mixed cyclic components: universal retained-square target [OPEN]

For each coarse cell C with m positive bodies, prove that every realization with R<sqrt(Q) has no completion by 9-m unit squares. A stronger total-capacity<=8 theorem on the closed window may be used when true. If a cell survives at R=sqrt(Q), retain it for G5 rather than declaring it impossible.

### G3.M4 — Complete mixed cell: C1.3.b1 triangle plus leaf [CLOSED hand]

Name the leaf L0, its articulation A, and the other triangle vertices B0,C0. The positive edges are L0-A, A-B0, B0-C0, C0-A. There are **five** remaining physical squares. The notation L0/B0/C0 denotes bodies, not the loaded-set label L above.

#### G3.M4.0 Assemble the complete core reduction [CLOSED hand]

Source: TRIANGLE_LEAF_CORE_REDUCTION.md. The proof separately treats a Jordan triangle and a common three-body junction; both route every completion square into the same two residual regions.

- [x] **G3.M4.0.a input** A positive leaf is loaded, and its positive edge is a radial bridge.
- [x] **G3.M4.0.b input** One endpoint of every bridge is physically circle-clear; the loaded leaf is the outer endpoint, so A is circle-clear.
- [x] **G3.M4.0.c input** An unloaded degree-two body cannot have physically touching neighbors. Thus both triangle tips B0,C0 are loaded.
- [x] **G3.M4.0.d input** The leaf is exactly radial S or radial D, with the formulas in RADIAL_BRIDGE_AND_LEAF_REDUCTION.md.
- [x] **G3.M4.0.e** Assemble the three-load force/torque equations, physical L0-versus-B0/C0 separation, contact-junction cases and the full articulation pose cover in one proof source.
- [x] **G3.M4.0.f** Establish the exact routing of every completion square into the triangle hole or the three exterior boundary-port regions.
- [x] **G3.M4.0.g input** A genuine triangular contact-ring hole has capacity 0.
- [x] **G3.M4.0.h input** The exterior pocket of the touching circle-boundary pair B0,C0 has capacity 0.
- [x] **G3.M4.0.i** Assemble the consequence: all five extra squares must occupy the two remaining articulation/leaf regions, including shared-contact degeneracies.
- [x] **G3.M4.0.ALL** Complete reduction with no hidden circle-load, side-owner, symmetry or routing premise.

#### G3.M4.D — Radial diagonal leaf: full open-slider domain [CLOSED hand]

Rotate the radial leaf direction to e_x. Put d=R-sqrt(2). The strict selected normal excludes a point-only vertex/vertex bridge. Hence the articulation has the form

    A=[d-1,d] x [t-1/2,t+1/2],  -1/2<t<1/2,

with bridge point (d,0) in the relative interior of its right side. The physical D leaf remains an obstacle; it is not replaced merely by its force.

- [x] **G3.M4.D.1 NORMAL FORM** Write the exact derivation and all force/contact equations for this entire domain.
- [x] **G3.M4.D.1.a** Retain both signs of t and t=0; a reflection must act on the entire packing and all loads.
- [x] **G3.M4.D.1.b** Explain why |t|=1/2 is excluded for this selected certificate and where limiting physical configurations enter the global cover.
- [x] **G3.M4.D.2 LOAD TYPES** Cover one/two physical circle-corner states of B0 and C0, with every allowed positive-weight mask.
- [x] **G3.M4.D.3 CONTACT TYPES** Cover both owner directions and shared-side/strict point-contact limits at A-B0, A-C0 and B0-C0; derive rather than assume contact locations.
- [x] **G3.M4.D.4 TORQUE** Use the common moment of the three cycle edges and the zero bridge moment; include parallel-force and common-junction degeneracies.

##### D.LOC — Complete contact localization [CLOSED hand]

Source: D_LEAF_ARTICULATION_CONTACT_LOCALIZATION.md. Put s=1+sqrt2-R and h=t+1/2, so A=[-s,1-s] x [h-1,h], 0<h<1.

- [x] **G3.M4.D.LOC.1** Every positive circle corner of B0/C0 lies strictly in x<0, by the acute contact-load cone and horizontal balance against the D leaf.
- [x] **G3.M4.D.LOC.2** A supporting point p with normal n_y<0 has max-square-y minus p_y<1; include arbitrary means on a shared support side.
- [x] **G3.M4.D.LOC.3** No vertical triangle reaction is possible: it puts one neighbor above A while the support-span bound puts the other strictly below it, contradicting B0/C0 contact.
- [x] **G3.M4.D.LOC.4** No rightward reaction is possible: the two opposite-sign circle corners required by balance would violate their strict acuteness using s^2+(s+sqrt2)^2<R^2.
- [x] **G3.M4.D.LOC.5** The exhaustive alternatives are both normals=-e_x, or normals(-cos(phi),sin(phi)), (-cos(psi),-sin(psi)) at the two left corners, with 0<phi,psi<pi/2.
- [x] **G3.M4.D.LOC.6** Parallel reactions satisfy the weighted contact-height sum0; the oblique case satisfies h=tan(phi)/(tan(phi)+tan(psi)).

##### D.SELECT — Legitimate pre-stress removal of free articulation normals [CLOSED hand]

Source: D_LEAF_GENERIC_CONTACT_SELECTION.md. This is an existence statement about the selected minimizing certificate, not a claim about every admissible physical stress.

- [x] **G3.M4.D.SELECT.1** Resolve the variable-application issue first: a point-only strict vertex/vertex articulation edge forces both reactions nonaxis, hence both applications are fixed distinct articulation vertices with nonzero heights.
- [x] **G3.M4.D.SELECT.2** Eliminate the two triangle magnitudes to obtain E=n_B,y det(p_C,n_C)-n_C,y det(p_B,n_B)=0.
- [x] **G3.M4.D.SELECT.3** For a free articulation normal, E is a nonzero linear equation; each relevant candidate forbids a closed set with empty interior in the finite product of open normal intervals.
- [x] **G3.M4.D.SELECT.4** Choose every normal before the physical stress argument, simultaneously retaining nonradial/diagonal exclusions and matched opposite normals at four-square junctions.
- [x] **G3.M4.D.SELECT.5** The two articulation vertices are distinct, so their free parameters are not coupled by a single four-junction match. Uncrossing and thinning do not change surviving point-contact normals.
- [x] **G3.M4.D.SELECT.6** Preserve the planar body graph, <=27 scalar atoms, exterior circle ports and unique positive component. Every final D star was included among the finite candidate exclusions.
- [x] **G3.M4.D.SELECT.7 control** Retain the exact positive D core with older normal choices at79/40<R<2; it shows why arbitrary physical-core exclusion is false.
- [x] **G3.M4.D.SELECT.ALL** In a selected oblique D star, both articulation corners lie in relative interiors of loaded-neighbor sides. Only D.PARALLEL and D.OBLIQUE remain.

##### D.PARALLEL — Entire horizontal-reaction branch [CLOSED hand]

Source: D_LEAF_PARALLEL_LEFT_EXCLUSION.md; two independent hand audits passed. A complete side-support/vertex-support split excludes the core, so every completion target below is discharged without a region approximation.

- [x] **G3.M4.D.PARALLEL.0 input** Both neighbors lie in x<=-s and both contact application points lie on A's left side; the positive weighted height sum is0.
- [x] **G3.M4.D.PARALLEL.1.a** If either wall support is a vertical side, all application means are retained. The mutual-contact normal split and a uniform corner-cap theorem force the other neighbor to be circle-clear.
- [x] **G3.M4.D.PARALLEL.1.b** If both wall supports are vertices, exact lower/upper vertical sections classify every actual mutual contact, including wall-endpoint contacts.
- [x] **G3.M4.D.PARALLEL.1.c** Cover all combinations of these two neighbor types, including whole-packing reflection; no aligned-neighbor hypothesis may be imposed globally.
- [x] **G3.M4.D.PARALLEL.2** The coincident-breakpoint vertex/vertex contact contradicts symmetric torque. The strict breakpoint case has a derived side owner; whole-packing reflection covers the other owner.
- [x] **G3.M4.D.PARALLEL.3** Actual radius bounds force both vertex-supported neighbors to have unique far-left circle corners. Thus all two-corner masks are excluded by geometry, not omitted.
- [x] **G3.M4.D.PARALLEL.4** The two exact concurrence/torque equations force b>a and then a wall height below-1. A uniform analytic inequality on the complete derived angle range gives the contradiction.
- [x] **G3.M4.D.PARALLEL.ALL** Close every parallel-left selected D core over the full radius/height domain, including all shared-side means.

##### D.OBLIQUE — Entire fixed-owner opposite-corner branch [CLOSED hand]

Source: D_LEAF_NONPARALLEL_OWNER_EXCLUSION.md, independently hand-audited. The full core is excluded after a compatible simultaneous finite normal selection. No extra-square capacity estimate is needed.

- [x] **G3.M4.D.OBLIQUE.0 input** The two articulation contact points are(-s,h), (-s,h-1); each lies strictly inside a loaded-neighbor side, and h is fixed by the two slopes.
- [x] **G3.M4.D.OBLIQUE.1** Parameterize the two full neighbor frames and their interior side-contact coordinates; retain both signs and every allowable height.
- [x] **G3.M4.D.OBLIQUE.2.a** Derive the complete B0-owned B0/C0 contact chart and its valid parameter domain from physical nonoverlap.
- [x] **G3.M4.D.OBLIQUE.2.b** Horizontal reflection and exchange cover the C0-owned chart. The parallel-axis lemma excludes shared-side limits between B0 and C0, rather than omitting them.
- [x] **G3.M4.D.OBLIQUE.2.c** At least one neighbor has a unique physical circle corner. Its fixed side-interior A force and circle force exclude all but finitely many B0/C0 point normals; simultaneous pre-stress selection removes that contact type, including parallel fixed-force cases.
- [x] **G3.M4.D.OBLIQUE.3** Containment and force signs identify actual positive-weight circle corners for every one/two-corner mask. The two-C0-corner case is excluded directly; the unique-C0-corner case derives phi+psi<pi/4 from concurrence and torque.
- [x] **G3.M4.D.OBLIQUE.4** For h>=1/2 bound the C0 circle corner directly. For h<=1/2 use the exact pivot r0=(1-h)/cos(psi); on either side a genuine circle corner has squared norm<(s+1)^2+9/5<R^2. All heights and unequal angles are included.
- [x] **G3.M4.D.OBLIQUE.ALL** Both owners, all normal signs, all circle masks, all height ranges and every allowed transition are excluded in one universal selected-certificate theorem.

- [x] **G3.M4.D.5 ROUTING** Apply G3.M4.0 to all five whole extra squares, keeping physical zero-weight contacts.
- [x] **G3.M4.D.6 JOINT CAPACITY** The compatible finite normal selections and both complete D proofs exclude the entire selected core. The joint-capacity alternative is therefore unnecessary.
- [x] **G3.M4.D.6.a** No selected D core exists, so no allocation of five extras across its two regions occurs. No separate two-per-region theorem is asserted.
- [x] **G3.M4.D.6.b** Retain arbitrary extra frames, every actual separating-axis owner, and tangencies.
- [x] **G3.M4.D.ALL** Close every selected D-leaf realization across the full domain. The exceptional arbitrary-normal physical D core is retained as a control.

#### G3.M4.S — Radial side-normal leaf: complete aligned/tilted cover [CLOSED hand]

Source: S_LEAF_TRIANGLE_EXCLUSION.md, with the full core cover in TRIANGLE_LEAF_CORE_REDUCTION.md. One closed 90-degree inaccessible circle arc excludes the entire S core. All S completion-capacity targets below are discharged by this stronger core impossibility; no independent two-per-region estimate is asserted.

Put d=sqrt(R^2-1/4)-1. The physical leaf is [d,d+1] x [-1/2,1/2], and its bridge applies at p=(d,0). The articulation lies in x<=d and contains p in its right support face. Its complete pose cover has the following three branches; overlaps at symmetry endpoints are harmless.

- **S0: aligned side contact.** A=[d-1,d] x [t-1/2,t+1/2], with -1/2<=t<=1/2. The whole slider interval is retained.
- **S+: tilted vertex contact.** Choose 0<theta<=pi/4, a=cos(theta), b=sin(theta), and the corresponding side frame; center `(d-(a+b)/2,(a-b)/2)`.
- **S-: reflected tilted vertex contact.** The reflected frame and center `(d-(a+b)/2,-(a-b)/2)`.

The theta->0 limit of S+/S- gives only t=+/-1/2. It does **not** cover the aligned interior slider heights. The theta=pi/4 duplicate is retained or removed by an explicitly proved square symmetry.

- [x] **G3.M4.S.1 COVER** Prove that S0/S+/S- exhaust all actual articulation support faces at p.
- [x] **G3.M4.S.2.S0** Derive full cycle/bridge balance over the closed aligned slider interval and every B0/C0 load/contact type.
- [x] **G3.M4.S.2.S+** Derive the same equations over the full positive-tilt range, with actual contact application points.
- [x] **G3.M4.S.2.S-** Supply the full-packing reflection argument or a direct proof for the reflected range.
- [x] **G3.M4.S.3 ROUTING** Route every whole extra square into the two retained regions; do not assume0 lies in A.
- [x] **G3.M4.S.4 JOINT CAPACITY** For each complete S branch prove joint capacity<=4, or prove core infeasibility in the entire radius window.
- [x] **G3.M4.S.4.a** No S core occurs, so no 3+2 completion distribution can arise. The proof does not require a separate region-capacity estimate.
- [x] **G3.M4.S.4.b** Include t endpoints, zero tilt, diagonal tilt, two-circle-corner endpoints and all contact degeneracies.
- [x] **G3.M4.S.ALL** Assemble S0/S+/S- into the entire S-leaf exclusion.

#### G3.M4.ALL — Whole-cell closure [CLOSED hand]

Source: TRIANGLE_LEAF_CELL_CLOSED.md; independent assembly audit passed. The simultaneous certificate selection is compatible with every prior reduction. The coarse count is three closed and55 open, and every remaining selected positive cyclic component has at least five bodies.

- [x] **G3.M4.ALL.1** G3.M4.0 plus D.ALL plus S.ALL cover every selected C1.3.b1 realization.
- [x] **G3.M4.ALL.2** At most4 extras contradict the required5, or the alternative full-core exclusions already contradict the premise.
- [x] **G3.M4.ALL.3** Audit the full cell, including physically touching pairs with zero selected stress.
- [x] **G3.M4.ALL.4** Only then tick C1.3.b1 in CYCLIC_CELL_LEDGER.md and update the component-size lower bound to5.

### G3.M5–M9 — Remaining cells and a finite semantic refinement

After the first cell, process increasing m, using a shared theorem whenever it closes several entire cells. At fixed m, order by bridge count and then the sorted cyclic-block profile. Every open row in CYCLIC_CELL_LEDGER.md is an instance of the contract below. The boundary-only C7 subfamily is discharged only by G3.B; the rest of its coarse row remains in the mixed branch.

#### G3.M.F Finite data that may be split without discretizing poses

For at most nine labeled squares there are finitely many choices of each item below. The centers, side frames, radius, weights and application coordinates remain real variables.

- [ ] **G3.M.F.1 GRAPH** Specify the positive simple graph G and full physical touching graph H with G a subgraph of H; retain the 9-m zero-stress bodies.
- [ ] **G3.M.F.1.a** Cover every internal biconnected block adjacency and articulation placement allowed by the coarse profile.
- [ ] **G3.M.F.1.b** Keep only selected plane embeddings and circle-touching vertices on the exterior face, without imposing planarity on H.
- [ ] **G3.M.F.1.c** Include all bridge arrangements allowed by the four-body central bridge cover.
- [ ] **G3.M.F.2 LOADS** Specify physical boundary set B and positive load set L subset B, retaining B\L and physically clear positive bodies.
- [ ] **G3.M.F.2.a** Cover every circle-corner mask and every positive/zero weight mask on its one or two possible boundary corners.
- [ ] **G3.M.F.2.b** Apply loaded noncontact connectedness, distinct resultant directions, loaded endblocks and the completed two-load exclusion.
- [ ] **G3.M.F.3 CONTACT FEATURES** For each positive edge retain vertex/side, side/vertex, side/side and point-only vertex/vertex states with actual square features.
- [ ] **G3.M.F.3.a** Shared sides keep the application coordinate over the entire common segment, including endpoint atoms.
- [ ] **G3.M.F.3.b** Point-only contacts use the fixed strict normal choices of the selected certificate.
- [ ] **G3.M.F.3.c** Do not assume a two-force or radial law at a branching nonbridge vertex.
- [ ] **G3.M.F.4 JUNCTIONS** Cover the finite identifications of contact points and their cyclic square-sector orders; preserve the proved uncrossing convention.
- [ ] **G3.M.F.5 COMPLETION ROUTING** Specify which actual complementary region contains each zero-stress square's open interior; establish the separating barriers before using this label.
- [ ] **G3.M.F.5.a** Distinguish genuine holes from drawing faces created only by perturbing a shared junction.
- [ ] **G3.M.F.5.b** Use capacities 0/1/1/2 only for actual Jordan contact rings of length3/4/5/6.
- [ ] **G3.M.F.5.c** Empty touching-boundary-pair pockets only after the actual crosscut hypotheses are supplied.
- [ ] **G3.M.F.5.d** Retain every remaining exterior region and all mutual nonoverlap between its completion squares.
- [ ] **G3.M.F.COVER** Prove that the chosen finite semantic cases cover the entire coarse cell, with all degeneracies. A list of data types is not a completed geometric cover.

#### G3.M.C Exact closure contract instantiated for every open cell C

- [ ] **C.0 DOMAIN** State the whole continuous realization domain using F.1–F.5 and the original square/circle model.
- [ ] **C.1 EQUILIBRIUM** Write every body force and torque equation, actual shared support identity and circle normalization; derive all simplifications used later.
- [ ] **C.2 ROUTING** Account for all nine physical bodies and every possible location of the9-m extras.
- [ ] **C.3 BOUND** Prove R^2>=Q on the entire domain, or prove no9-body completion exists. A core-only radius bound cannot be substituted when a smaller core genuinely fits below Q.
- [ ] **C.3.a** If region capacities depend on a common parameter, prove their joint bound before summing them.
- [ ] **C.3.b** If a projection relaxation is used, verify that it is a necessary implication of actual square separation and sufficient for the asserted contradiction.
- [ ] **C.3.c** Include every endpoint, load degeneration and shared-support feature transition in the finite cover.
- [ ] **C.4 EQUALITY** If the cell survives atQ, record the exact saturated inequalities and free parameters; carry it into G5.
- [ ] **C.5 AUDIT** Check the complete parent implication and its prerequisite chain at the declared scope.
- [ ] **C.ALL** Tick the coarse row only after C.0–C.5 are complete. A uniform theorem may discharge several rows at once with explicit instantiations.

### G3.M5 — The four entire five-body cells [OPEN]

There are four physical completion squares in every case. For cyclic block sizes s_i and bridge count b, m=1+sum(s_i-1)+b. At m=5 this gives exactly the following four coarse cells. All fine geometric labels remain governed by G3.M.F and G3.M.C; no finite pose or angle discretization is a premise.

- [x] **G3.M5.CATALOG** The exhaustive coarse list is C1.3.b2, C1.4.b1, C1.5.b0, C2.33.b0. Three cyclic blocks would already require at least seven bodies.
- [ ] **G3.M5.ALL** Close all four complete cells, retaining every equality survivor and every one of the four extras.

#### M5.T2 — C1.3.b2: one triangle and two bridges [OPEN; active]

- [x] **M5.T2.LAYOUT** The exhaustive bridge-attachment layouts are a length-two arm at one triangle vertex, two leaves at one triangle vertex, or leaves at two distinct triangle vertices. This follows by removing the triangle edges and listing the two-edge attached forests.
- [x] **M5.T2.CHAIN.1** TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md gives the full load and radial-channel reduction. Only the leaf and the two triangle tips are loaded; the right articulation support lies at x=r_leaf-w<1/60, with w in {1,sqrt(2)}.
- [x] **M5.T2.CHAIN.2** Cover both S/D leaves, both widths, every articulation support pose and all physical contact/circle masks; the selected nonradial normal excludes the D/diagonal-transmitter combination directly.
- [x] **M5.T2.CHAIN.CONCURRENCE** A loaded two-force body with one boundary neighbor has nonparallel lines and positive radial concurrence behind both actual outward contacts, including the permitted outside-face two-corner case.
- [x] **M5.T2.CHAIN.ORDER** The true three-port tree fixes the reaction order. The common triangle moment is positive, so the articulation concurrence lies on the positive leaf axis and both reactions point left.
- [x] **M5.T2.CHAIN.TILTED** Cover the entire tilted articulation. Two required support caps have mutual center distance greater than sqrt(2), contradicting contact of the loaded tips.
- [x] **M5.T2.CHAIN.PARALLEL** Aligned parallel reactions place both tips in a center cap of diameter less than one, contradicting disjoint inscribed half-radius disks.
- [x] **M5.T2.CHAIN.SELECT** In the remaining aligned nonparallel chart, compatible pre-stress normal choices remove articulation and mutual free vertex contacts; both circle masks and both BC side owners remain.
- [x] **M5.T2.CHAIN.AXES** The exact circle-coordinate equations force a+c<1/6, then X_i>39/20 and Z_B+Z_C>5/3, contradicting R^2<=Q.
- [x] **M5.T2.CHAIN.3** The entire selected core is impossible throughout the window, so all four extras are accounted for without a separate completion bound. Root and separate independent hand audits passed.
- [x] **M5.T2.SAME.1** TRIANGLE_TWO_LEAVES_SAME_ARTICULATION_CLOSED.md gives the exhaustive unordered S/S, D/S, D/D cover, retaining both radial directions, every physical circle mask, actual mean and positive leaf weight.
- [x] **M5.T2.SAME.SS.COVER** TWO_S_LEAVES_ONE_TRIANGLE_ARTICULATION.md exhausts one side support, two adjacent vertices and two opposite vertices for the two equal-radius S applications.
- [x] **M5.T2.SAME.SS.SIDE** The complete side/side and side/vertex families lie in a shifted northeast quadrant. A 150-degree inaccessible circle arc contains the negative leaf-resultant cone, contradicting the pairwise acute triangle-tip circle corners.
- [x] **M5.T2.SAME.SS.ADJACENT** Adjacent vertex applications make the entire required left face too close to0 to meet any boundary body, contradicting articulation force balance.
- [x] **M5.T2.SAME.SS.OPPOSITE** Opposite vertices give the full displaced diamond family. Its half-plane bounds make a 120-degree lower circle arc inaccessible, again containing every negative leaf resultant.
- [x] **M5.T2.SAME.SS.ALL** The entire S/S leaf-type branch is excluded, including every actual mean and B/C circle mask. Root and separate audits passed.
- [x] **M5.T2.SAME.DS.COVER** TWO_MIXED_LEAVES_ONE_TRIANGLE_ARTICULATION.md reduces the S application in the full D articulation to the top side, northeast vertex or northwest vertex, after a whole-packing reflection.
- [x] **M5.T2.SAME.DS.NE** In the top-side/NE cases, exact support-height bounds make the southwest quadrant inaccessible to every boundary neighbor while its interior contains the negative leaf resultant.
- [x] **M5.T2.SAME.DS.NW** In the NW case the entire180–300-degree arc is inaccessible, and every positive leaf-weight combination has negative direction inside it.
- [x] **M5.T2.SAME.DS.ALL** All D/S poses and boundary masks are excluded, with every completion retained. Root and separate audits passed.
- [x] **M5.T2.SAME.DD.DOMAIN** TWO_D_LEAVES_ONE_TRIANGLE_ARTICULATION.md fixes the two D directions to adjacent side axes and the articulation to [-s,r]^2, with r=R-sqrt(2), s=1-r. The circle-clear articulation and the two unique-circle-corner triangle tips retain all actual contact points.
- [x] **M5.T2.SAME.DD.HIGH** For R>2 the whole southwest circle arc is inaccessible; at R=2 its only possible corner forces a radial-D tip whose second positive boundary contact contradicts torque and support width. The entire high-radius interval and its endpoint are excluded.
- [x] **M5.T2.SAME.DD.ORDER** The actual four-port embedding fixes the E,N,B,C order. Coincident articulation applications are excluded in every point/shared-side alternative; distinct applications reduce to the northwest/southwest corner case or the complete left-side/southwest case.
- [x] **M5.T2.SAME.DD.SELECT.POINT** With point-only B--C, the fixed-application boundary-tip theorem removes every free articulation or mutual vertex normal under one prelisted selection.
- [x] **M5.T2.SAME.DD.SELECT.SHARED** With a shared B--C side, collective pure translations annihilate its force for every application mean. The resulting nontrivial determinant removes a free outer normal; exact vertex radii exclude its coefficient degeneration. The apparent variable-mean aligned exception is geometrically impossible.
- [x] **M5.T2.SAME.DD.SELECT.PRESERVE** All candidate tips and shared blocks are listed before multipliers, matched junction parameters remain compatible, and uncrossing/thinning preserve the surviving point choices. No mean is fixed in advance.
- [x] **M5.T2.SAME.DD.CORNER.CHART** The full owned-corner chart retains both B--C side owners. Exact projections give j=K rho-a, U=1-b+L rho, 0<K<L and both circle-coordinate equations; the parallel shared-side alternative is already impossible by loaded-tip concurrence.
- [x] **M5.T2.SAME.DD.CORNER.OUTER_LARGE** In the northwest-owner chart, rho>=s/d puts the circle corner below the exact radius budget. Every contact-coordinate endpoint is retained.
- [x] **M5.T2.SAME.DD.CORNER.OUTER_SMALL** For rho<s/d, positive radial concurrence and articulation balance bound the two angles. A convex quartic sign argument on the whole r interval gives tan(phi)<2/5; the other circle corner then violates the same radius budget.
- [x] **M5.T2.SAME.DD.CORNER.INNER** Reflecting and interchanging the tips covers the southwest owner. Exact concurrence gives a<1/10 and c<1/6; both transverse circle coordinates exceed11/10, whereas their exact sum is below11/5.
- [x] **M5.T2.SAME.DD.SIDE.COVER** Torque gives a>b>0 for the southwest side normal. The other tip is aligned or tilted, and every possible mutual downward side axis belongs to one of the following cases.
- [x] **M5.T2.SAME.DD.SIDE.ALIGNED** All variable articulation means are retained. A southwest-tip owner is geometrically impossible; the other owner forces tau>as and an exact corner norm below39/10.
- [x] **M5.T2.SAME.DD.SIDE.PARALLEL** In parallel tip frames, the common support line gives tau=a Delta. Equality of circle-corner norms would require G(Delta)=0, but G is strictly decreasing and G(s)<0. This includes positive-length shared contacts and endpoint-only parallel contacts.
- [x] **M5.T2.SAME.DD.SIDE.C_OWNER** A southwest-tip owner gives an exact concurrence whose circle-coordinate ratio is below13/20 and normal coordinate below33/20; the squared norm is below39/10.
- [x] **M5.T2.SAME.DD.SIDE.B_LEFT** The downward-left owner of the other tip forces tau b>=v>1/sqrt(2)>b, contradicting the physical side coordinate tau<1.
- [x] **M5.T2.SAME.DD.SIDE.B_RIGHT** Its downward-right owner either contradicts the support ordering or again forces tau>as, so the same complete corner-norm bound applies.
- [x] **M5.T2.SAME.DD.BOUND** The entire D/D core is excluded throughout the radius window, including every radius, shared-side, parallel-frame and owner transition. Root and separate full hand audits passed.
- [x] **M5.T2.SAME.2** Each complete leaf-type proof uses the actual disjoint squares, their support contacts and mutual triangle-tip geometry. No two radial forces are replaced by an invented physical leaf.
- [x] **M5.T2.SAME.3** TRIANGLE_TWO_LEAVES_SAME_ARTICULATION_CLOSED.md combines all three leaf types under the same necessary selected certificate. The entire layout is impossible independently of the four extras; root and independent assembly audits passed.
- [x] **M5.T2.DISTINCT.1** TRIANGLE_DISTINCT_LEAVES_DOMAIN.md gives exactly three loaded bodies, the two radial leaves and C; A,B are physically circle-clear. It retains the full S support-face/vertex pose and the full D slider pose.
- [x] **M5.T2.DISTINCT.DD** Two D articulations would both contain0 in their open interiors; the entire D/D leaf pair is impossible.
- [x] **M5.T2.DISTINCT.MOMENT** Actual origin torque gives one common signed triangle moment H for every positive edge, with every shared application mean retained.
- [x] **M5.T2.DISTINCT.ZERO.NONPARALLEL** At H=0, two nonparallel C force lines would concur at0, contradicting the general-neighbor positive-concurrence calculation. No boundary-neighbor parallel exclusion is imported.
- [x] **M5.T2.DISTINCT.ZERO.PARALLEL** The radial-D alternative makes both neighbors overlap at its inner vertex. The radial-S alternative fixes both means at the inner midpoint, forces two aligned half-squares, and contradicts the required outward S/D leaf support. Thus every H=0 chart is excluded.
- [x] **M5.T2.DISTINCT.LOW** For d=sqrt(R^2-1/4)-1<1, both articulations contain0. Disjoint interiors force aligned S bodies with opposite transverse tangent half-planes; equal/opposite leaf directions contradict distinct circle-resultant directions.
- [x] **M5.T2.DISTINCT.ENDPOINT** At d=1, H!=0 forces a shared AB segment. Equal/opposite leaf directions fail as before; perpendicular directions force two C contact vectors with nonpositive scalar product, contradicting its strict circle-corner cone. The exact threshold R=sqrt(17)/2 is included.
- [x] **M5.T2.DISTINCT.2** The full remaining necessary domain is R>sqrt(17)/2, H!=0 and S/S or D/S, with dist(0,A),dist(0,B)<=delta=d-1<1/60. Every leaf angle, actual AB contact, C corner count/weight mask and four-square completion remains.
- [x] **M5.T2.DISTINCT.PORTS.CIRCLE** TRIANGLE_DISTINCT_LEAVES_PORT_ORIENTATION.md groups all positive circle atoms in their disjoint physical angular intervals. The resultant order agrees with these actual boundary groups, and deleting each triangle edge gives the necessary three-port branch order.
- [x] **M5.T2.DISTINCT.PORTS.ARTICULATIONS** Coincident cycle applications are too close to0 for C. A D leaf's side-interior application leaves no third unit tangent cone; an S coincidence forces two aligned half-squares that cannot carry the other distinct radial leaf. Thus all three articulation applications are distinct.
- [x] **M5.T2.DISTINCT.PORTS.C_CONTACTS** The two circle normals, when present, are consecutive and can be aggregated without crossing a pair normal. Ordered neighbor tangent sectors retain the pair-normal order even at coincident C contacts.
- [x] **M5.T2.DISTINCT.PORTS.H_POSITIVE** The C concurrence gives H>0 in the nonparallel chart. In the full parallel radial-S chart, the actual means satisfy y_A>0>y_B and give the same strict sign. Radial D would give the already excluded H=0.
- [x] **M5.T2.DISTINCT.PORTS.CONCURRENCE** At either nonparallel articulation, the common positive moment and ordered three-force balance give a strictly positive radial concurrence. No assertion of concurrence inside the body and no exclusion of parallel articulation forces is added.
- [x] **M5.T2.DISTINCT.DS.SUPPORT** TRIANGLE_DISTINCT_MIXED_LEAVES_EXCLUSION.md uses the whole D slider and B meeting D_delta to give h_A(n_AB)<=delta. The AB normal cannot be horizontal, so A's two cycle forces are nonparallel.
- [x] **M5.T2.DISTINCT.DS.DIRECTION** Positive radial concurrence and the full support inequality force, after reflection, n_y>17/18 and n_x>=0. The vertical case retains every actual top-side mean; the oblique case uses the northeast vertex.
- [x] **M5.T2.DISTINCT.DS.SPAN** A unit square with minimum support point p in direction m has u-span from p strictly below1 whenever m dot u<0. The proof covers vertex, side-interior and endpoint support points uniformly.
- [x] **M5.T2.DISTINCT.DS.BOUND** The other articulation normal points southwest. The support-span theorem puts all of C strictly below B's AB supporting line, whose projection gap is n_x+n_y>=1. This excludes the entire D/S core, with arbitrary owners, every C circle mask and all four extras. Root and separate full audits passed.
- [ ] **M5.T2.DISTINCT.SS.DOMAIN** Finish the full S/S family in the high-radius, nonzero-moment domain. Retain independent leaf angles, both aligned side means and tilted support-vertex articulations; neither a common frame nor origin containment is a premise.
- [x] **M5.T2.DISTINCT.SS.SUPPORT** DISTINCT_S_LEAF_CORE_AND_CORNER_MASK.md proves the whole unit-square support inequality: p=d e an outward support with d>=1 implies h_A(u)<=1 whenever e dot u<=0. All vertex-axis signs and every side mean are included.
- [x] **M5.T2.DISTINCT.SS.C_MASKS** A radial two-corner C has all points beyond projection d>1. Its contacts with both articulations would force both leaf directions and its own resultant to have positive projection on that axis, contradicting global balance. Every physical two-corner mask is excluded, even with only one positive atom.
- [x] **M5.T2.DISTINCT.SS.C_NONPARALLEL** C therefore has a unique positive circle atom and nonparallel pair forces: radial S is excluded, while radial D parallel forces would give H=0. Parallel forces at A or B remain.
- [x] **M5.T2.DISTINCT.SS.CONTROL.RADIUS** The exact parameter x=(sqrt(70)-8)/4 obeys 8x+2x^2=3/4 and9/100<x<1/10. With delta=x^2 and R^2=(2+delta)^2+1/4, the explicit S/S core lies strictly between17/4 andQ.
- [x] **M5.T2.DISTINCT.SS.CONTROL.PHYSICAL** The construction checks all five square containments, exactly three loaded bodies, all ten physical pair separations and every actual triangle shared segment. Both articulations remain circle-clear and C has exactly one physical circle corner.
- [x] **M5.T2.DISTINCT.SS.CONTROL.STRESS** Positive rational expressions in x give all pair magnitudes and corner weights. The three strict shared-side means yield exact force balance and a common moment H=(1-x^2)(1-x)^2>0. Every positive normal is already a genuine side axis, so no free-normal selection removes this core.
- [x] **M5.T2.DISTINCT.SS.CONTROL.SCOPE** Universal S/S core exclusion is false. The example is not a nine-square counterexample and does not establish any completion count. The full terminal theorem must bound every core's completion capacity by3 or classify all cores and prove that bound for every whole family.
- [ ] **M5.T2.DISTINCT.SS.FIXED** Apply the general fixed-tip theorem only at genuinely fixed distinct applications. Keep the coincident radial-D C vertex and every variable shared-side mean as explicit alternatives until separately resolved.
- [ ] **M5.T2.DISTINCT.SS.AB** Resolve all actual AB support features and every axis-owner/free-normal alternative, with the full nonzero common moment and both near-origin constraints.
- [ ] **M5.T2.DISTINCT.SS.PARALLEL** Prove the whole capacity implication with parallel articulation forces and every parallel-side or contact-coordinate endpoint retained. The exact positive control has parallel forces at A and strict shared means; positive radial concurrence may be used only in the nonparallel charts covered by its theorem.
- [ ] **M5.T2.DISTINCT.SS.BOUND** Prove at most three additional unit squares for every surviving S/S core, using the actual full free domain. A complete classification followed by capacity for every resulting family is also sufficient. A triangle's empty inner hole alone does not bound the four candidate exterior extras.
- [ ] **M5.T2.DISTINCT.3** Assemble the complete S/S completion conclusion with the D/D and D/S exclusions, the whole radius/zero-moment reductions, and every shared-side/degenerate contact case.
- [ ] **M5.T2.ASSEMBLE** Combine all three layouts, audit the same simultaneous certificate choice, and only then close C1.3.b2.

#### M5.B4L — C1.4.b1: a four-body block with one leaf [OPEN; active]

- [x] **M5.B4L.GRAPHS** The four-body biconnected graphs are C4, the diamond K4-e and K4. C4 and K4 each have one leaf-attachment orbit; the diamond has a hub and a tip orbit.
- [x] **M5.B4L.K4** NO_POSITIVE_K4_SUBGRAPH.md excludes the entire K4 branch, uniformly for every attachment, load mask and completion.
- [x] **M5.B4L.C4.1** The radial leaf theorem gives the full S/D cover and circle-clear attachment A. Since the leaf is loaded and every exactly-two-load component is already excluded, at least two of the other three block vertices are loaded: an adjacent pair, the opposite pair, or all three. All physical zero-weight circle contacts remain.
- [ ] **M5.B4L.C4.2** Retain both adjacent and opposite loaded pairs, all clear transmitters, every contact owner and every corner-weight mask.
- [x] **M5.B4L.C4.HOLE.1** FOUR_CYCLE_LEAF_HOLE_EMPTY.md retains every actual cycle application point and every arbitrarily small planar routing. A hypothetical inner unit preserves winding through the contact-chord homotopy.
- [x] **M5.B4L.C4.HOLE.2** Coincident contact vertices reduce to a retraced loop or a triangle of area at most sqrt(3)/2, so they cannot conceal a unit-area completion.
- [x] **M5.B4L.C4.HOLE.3** Equality in the full area-minus-occupied-chords bound forces a unit contact polygon, all chords whole inward sides, and the aligned four-neighbor cross.
- [x] **M5.B4L.C4.HOLE.4** Any zero-load degree-two ring body would transmit along a full side at a point-only vertex contact, violating strict normal selection. If all other three ring bodies are loaded, their exact corner equations force R^2=5/2, outside the window.
- [x] **M5.B4L.C4.HOLE.ALL** The whole C4-plus-leaf inner hole has capacity zero, for every load assignment and contact degeneracy. All four completion squares are exterior; root and separate audits passed.
- [x] **M5.B4L.C4.ADJACENT.CAP** FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md proves an all-orientation square cap: minimum projection at least59/60 confines its entire shadow within atan(13/20).
- [x] **M5.B4L.C4.ADJACENT.NEAR** Every radial-leaf articulation is within max(sqrt(R^2-1/4)-2,0) of0, including tilted S and every D slider.
- [x] **M5.B4L.C4.ADJACENT.CHANNEL** A positive normal channel through a zero-load degree-two body forces R>=sqrt(17)/2 and both articulation-support bounds of magnitude below1/60; its far square lies in the exact cap.
- [x] **M5.B4L.C4.ADJACENT.DETOUR** A boundary square touching both channel endpoints would have two points whose angular separation exceeds its strict atan(23/16) shadow bound. The argument needs no positive weight at the detour body and no circle contact at the far endpoint.
- [x] **M5.B4L.C4.ADJACENT.ALL** The entire adjacent-loaded-pair C4-plus-leaf pattern is impossible, for both leaves, every orientation, all shared means and both transmission widths. Root and separate audits passed.
- [ ] **M5.B4L.C4.OPPOSITE.DOMAIN** Retain the two loaded neighbors of A and the zero-load opposite transmitter, both S/D leaves, every actual support owner and all physical zero-weight circle contacts.
- [x] **M5.B4L.C4.OPPOSITE.WIDTH** UNIT_BYPASS_NORMAL_CHANNEL.md forces exactly one side-normal transmitter of reserve1. Any longer channel exceeds the unit bypass diameter; a diagonal transmitter forces incompatible transverse same-frame separation. Its application means remain over the full sides, and no common articulation/leaf frame is inferred.
- [x] **M5.B4L.C4.OPPOSITE.TRANSVERSE** UNIT_BYPASS_NORMAL_CHANNEL.md, Section4, gives the full separating-axis consequence. The bypass vertical projection contains the transmitter's full width-one interval; every possible square-axis separator then forces horizontal separation. Thus the articulation and transmitter lie side by side in the transmitter frame for every articulation angle, without requiring them to touch or have a common frame.
- [ ] **M5.B4L.C4.OPPOSITE.BOUND** Prove the whole opposite-load core/radius or joint four-extra exterior bound, using the exact width-one and transverse-separation reductions while retaining every actual application mean and articulation pose.
- [ ] **M5.B4L.C4.THREE.DOMAIN** Derive the complete three-loaded-block force/moment system, all physical circle-corner masks and both independent cycle contacts at the clear articulation.
- [ ] **M5.B4L.C4.THREE.BOUND** Prove the full three-load branch's radius or joint exterior-completion theorem, retaining every asymmetric and shared-side limit.
- [ ] **M5.B4L.C4.3** Combine the completed adjacent-load and empty-hole theorems with the entire opposite/three-load conclusions before closing C4.
- [ ] **M5.B4L.DIAMOND.HUB.1** Cover the loaded degree-two tips and all allowed states of the other hub; derive every radial-bridge and cycle-moment equation.
- [x] **M5.B4L.DIAMOND.HUB.S_BOUNDARY.1** S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md splits all boundary neighbors of an S articulation into two inaccessible-arc-separated sets with opposite vertical signs. Each physical boundary edge preserves its set, even for zero-weight bodies.
- [x] **M5.B4L.DIAMOND.HUB.S_BOUNDARY.ALL** If the second hub U physically touches the circle, the path B--U--C is a connected graph of boundary neighbors containing all other loads. Their vertical sum cannot cancel the S leaf. This whole branch is excluded for every U weight and actual pose.
- [ ] **M5.B4L.DIAMOND.HUB.S_CLEAR** Finish the entire S-leaf branch with a physically clear second hub, exactly three loaded bodies and all remaining physical contacts.
- [ ] **M5.B4L.DIAMOND.HUB.D** Finish both physical boundary/clear states of the second hub for a D leaf, retaining every shared-side mean and load mask.
- [ ] **M5.B4L.DIAMOND.HUB.2** Prove the complete hub-attachment bound, with all actual contact junctions and all four extras.
- [ ] **M5.B4L.DIAMOND.TIP.1** Cover the opposite tip and every allowed hub-load assignment, using the boundary-contact and two-load exclusions only where their hypotheses hold.
- [ ] **M5.B4L.DIAMOND.TIP.2** Prove the complete tip-attachment bound, retaining both owner directions and all shared-side means.
- [x] **M5.B4L.REGION_REDUCTION** The surviving C4 hole and both diamond triangle holes are empty, while the K4 graph is excluded. Every remaining completion region in this whole cell is exterior; no joint exterior bound is yet proved.
- [ ] **M5.B4L.ASSEMBLE** Combine C4, both diamond orbits and the completed K4 exclusion; only then close C1.4.b1.

#### M5.B5 — C1.5.b0: every five-body biconnected graph [OPEN; graph/load reduction CLOSED]

Source: FIVE_BODY_BICONNECTED_REDUCTION.md, using NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md. The proof is an exhaustive hand classification by edge count; a finite computation is not a premise. All four extras and every physical zero-weight contact remain.

- [x] **M5.B5.FINITE_DOMAIN** The labeled domain consists of the 2^10 simple edge sets, with connectivity after every vertex deletion. All physical realizations remain continuous.
- [x] **M5.B5.GRAPH_COVER** Minimum degree two gives complement degree at most two. Complement path/cycle classification gives all ten abstract biconnected types: one at five edges, two at six, three at seven, two at eight, one at nine and one at ten.
- [x] **M5.B5.DENSE** The adjacent-two-missing-edge graph, K5 minus an edge and K5 each contain K4 and are excluded.
- [x] **M5.B5.WHEEL** The four-rim wheel's complement has components of size at most two, incompatible with a connected loaded noncontact graph on at least three vertices.
- [x] **M5.B5.K23_BOOK_SUBDIVISION** K2,3, the three-page book and the once-subdivided K4 each force three loaded common neighbors of two vertices. The uniform exterior-face obstruction excludes all three entire graph types.
- [x] **M5.B5.SURVIVORS** Exactly three semantic graph families survive the necessary restrictions: C5, house and the fan over a four-vertex path. This is not an existence assertion for every remaining pose or mask.
- [x] **M5.B5.LOAD_COVER** The physical loaded noncontact graph is a subgraph of the positive-graph complement; therefore the induced complement on positive loads is connected. This supplies the exhaustive necessary masks below without confusing missing positive edges with physical separation.

##### M5.B5.C5 — complete three-/four-load cover; geometry OPEN

- [x] **M5.B5.C5.MASKS** With three loads, the loaded induced positive graph has exactly one edge, and the two zero-load vertices are nonadjacent. This is one dihedral orbit. Four loads leave one zero-load vertex, also one orbit. Five loads contradict the all-boundary=C7 theorem.
- [ ] **M5.B5.C5.THREE.DOMAIN** Derive the two clear transmission channels, every remaining physical circle-contact mask, and all actual contact-owner and circle-corner states.
- [ ] **M5.B5.C5.THREE.BOUND** Prove the whole three-load core/radius or four-extra completion bound, including all channel widths and asymmetric frames.
- [ ] **M5.B5.C5.FOUR.DOMAIN** Derive the full single-transmitter/cycle moment system, retaining every physical zero-weight circle contact.
- [ ] **M5.B5.C5.FOUR.BOUND** Prove the whole four-load bound across all contact owners, shared-side means and corner weights.
- [ ] **M5.B5.C5.ROUTING** The genuine five-ring hole has capacity one. Account for every exterior region and all mutual nonoverlap of the four extras before any capacity sum.
- [ ] **M5.B5.C5.ALL** Assemble both load families and every boundary case; retain any equality survivors.

##### M5.B5.HOUSE — complete three-mask-orbit cover; geometry OPEN

Label the positive-graph complement path 1--2--3--4--5. Vertex3 is the loaded degree-two roof; its positive neighbors1 and5 touch.

- [x] **M5.B5.HOUSE.MASKS** The complete labeled necessary load list is {1,2,3}, {2,3,4}, {3,4,5}, {1,2,3,4}, {2,3,4,5}. Reflection gives three orbits. All five loaded would create a boundary triangle.
- [ ] **M5.B5.HOUSE.END_TRIPLE** Prove the full geometry/completion theorem for {1,2,3} and its reflected mask, preserving all contact features and physical boundary states.
- [ ] **M5.B5.HOUSE.MIDDLE_TRIPLE** Prove the full theorem for {2,3,4}, including both zero-load higher-degree bodies and every stress distribution.
- [ ] **M5.B5.HOUSE.FOUR** Prove the full theorem for the four-load masks and every admissible zero-weight contact.
- [ ] **M5.B5.HOUSE.ROUTING** Empty actual triangle holes, treat four-/five-ring regions only with their genuine barriers, and prove the joint bound for all four extras.
- [ ] **M5.B5.HOUSE.ALL** Assemble the entire house graph, including feature transitions and equality survivors.

##### M5.B5.FAN — complete three-/four-load cover; geometry OPEN

Use path u1--u2--u3--u4 and universal hub H. The two endpoint tips u1,u4 are loaded. H is physically circle-clear because it touches at least three loaded boundary bodies.

- [x] **M5.B5.FAN.MASKS** The necessary loads are {u1,u2,u4}, {u1,u3,u4}, or all four path vertices. The first two are reflection partners. Zero-weight physical circle contacts at the two inner path vertices remain explicit.
- [ ] **M5.B5.FAN.THREE** Derive and solve the full three-load hub/path stress and physical contact geometry for both reflected masks.
- [ ] **M5.B5.FAN.FOUR** Derive and solve the full four-load branch, without equating all hub forces or assuming a common frame.
- [ ] **M5.B5.FAN.ROUTING** Treat all three triangle holes and actual exterior regions, including contact coincidences and every zero-stress completion square.
- [ ] **M5.B5.FAN.BOUND** Prove a whole core/radius obstruction or the joint four-extra completion bound on both load branches.
- [ ] **M5.B5.FAN.ALL** Retain all owner/corner masks, shared-side means and any equality survivors, then close the entire fan graph.

- [ ] **M5.B5.ALL** Audit and combine C5, house and fan. Only their complete geometry/completion conclusions can close C1.5.b0; the ten-to-three graph reduction leaves the coarse count unchanged.

#### M5.TT — C2.33.b0: two triangles sharing an articulation [OPEN]

- [x] **M5.TT.GRAPH** The two triangular blocks share exactly one articulation; four other bodies are the degree-two tips. No bridge is present.
- [x] **M5.TT.LOAD_INPUT** Every tip is loaded, since a clear degree-two transmitter cannot have touching neighbors. The articulation is physically circle-clear, since otherwise either triangle would contain three mutually touching boundary bodies.
- [ ] **M5.TT.CORE** Derive the complete four-load force/torque system and the full articulation contact cover, including shared-side means and common three-body junctions.
- [ ] **M5.TT.PHYSICAL_GRAPH** Retain all additional physical contacts between the two tip pairs, even if their selected stress is zero; do not assume the full touching graph is the abstract bowtie.
- [ ] **M5.TT.ROUTING** Empty the two genuine triangle holes and the two touching-boundary-pair exterior pockets, while treating common-junction limits directly. Route every whole extra into the exact remaining regions.
- [ ] **M5.TT.JOINT_BOUND** Prove the required joint capacity for all remaining regions, or a full selected-core/radius obstruction. A separate two-per-region claim is not a sufficient nine-square exclusion.
- [ ] **M5.TT.ALL** Include all contact owners, four independent circle masks, articulation poses and equality survivors, then close C2.33.b0.

#### G3.M.R Completion ordering by body count

- [ ] **G3.M5.ALL** All remaining mixed cells with m=5 and four completion squares.
- [ ] **G3.M6.ALL** All remaining mixed cells with m=6 and three completion squares.
- [ ] **G3.M7.ALL** All mixed cells with m=7 and two completion squares; separate the already-defined boundary C7 branch.
- [ ] **G3.M8.ALL** All mixed cells with m=8 and one completion square; a simple cycle is still allowed by the size theorem.
- [ ] **G3.M9.ALL** All mixed cells with m=9 and no completion squares; simple cycles are excluded, branching cyclic graphs remain.
- [ ] **G3.M.ALL** Combine the completed four-body cell and M5–M9, preserving every equality survivor.

### G3.ALL — Sharp coverage exit

- [ ] **G3.ALL.1** Every selected positive certificate is covered by G3.0, with no unproved global frame or origin-containment assumption.
- [ ] **G3.ALL.2** G3.B.CAP excludes the full boundary-only branch.
- [ ] **G3.ALL.3** G3.M.ALL gives the sharp bound or exclusion for every mixed branch.
- [ ] **G3.ALL.4** All radius-window and imported-theorem dependencies are explicit, and no physical square was discarded.
- [ ] **G3.ALL** Pass a complete sharp-coverage theorem to G4. This gate is OPEN.

---

## G2.O3.3 / O4 / O5 — Global sharp coverage [OPEN]

- [x] **O3.3.T** Every remaining tree realization is in P or Y after the closed origin cases.
- [x] **O3.3.C** Every selected cyclic component belongs to exactly one of the 58 coarse cells.
- [x] **O3.3.L2** Every two-loaded physical component has the new exact parallel/layered geometry, across the whole graph inventory.
- [ ] **O3.3.SHARP** Finish the general C7 completion and mixed cyclic components with 3–7 noncollinear loaded bodies, retaining all physical squares. P.ALL, Y.ALL, TREE.ALL and TL.COMPLETE are closed hand implications.
- [ ] **O4.1** Obtain exact orientation-uniform stress/support/capacity inequalities, not numerical dual values at selected poses.
- [ ] **O4.2** Preserve tangencies, zero weights and all physical completion constraints.
- [ ] **O4.3 alternative** A global CAP/QCAP/contact-area invariant can replace the inventory if it yields the unrestricted sharp theorem.
- [ ] **O5** Combine sharp coverage with compact attainment and G0.W; remove every unproved extra frame/row/contact hypothesis.

## G2.X / G4 — Unrestricted radius [BLOCKED]

- [x] **X.1** A subcritical packing has an unrestricted minimizing stress.
- [x] **X.2** The selected unique component is either a tree or cyclic; the tree branch is closed and the remaining cyclic branch splits into G3.B or G3.M, with all physical bodies retained.
- [ ] **X.3** Supply the missing sharp contradiction for the general C7 and mixed cyclic branches. The declared lower-window input is assembled in G0.W.2.
- [x] **G4.1** Exact construction gives the upper bound.
- [ ] **G4.2** Establish R9>=sqrt(Q) from original Packing only.
- [ ] **G4.2.a** Start from the original nine-square Packing predicate and obtain a compact minimizer with no extra orientation/contact hypothesis.
- [ ] **G4.2.b** Use the construction to place the minimum at or below sqrt(Q); use physical deletion and the exact n=8 import for its lower window.
- [ ] **G4.2.c** Select the simultaneous strict-normal, planar, unique positive certificate; verify all later reductions use this same allowable selection.
- [ ] **G4.2.d** Apply the completed tree/two-load exclusions and the complete G3.B/G3.M split.
- [ ] **G4.2.e** Derive R_min^2>=Q, retaining every zero-stress square in the invocation of the sharp completion theorem.
- [ ] **G4.2.f** Transfer the minimum bound to every original packing radius by minimality and nonnegativity.
- [ ] **G4.3** Match the existing nonnegative-radius/Optimum interface.
- [ ] **G4.3.a** Keep the existing definitions of unit square, closed containment and interior-disjointness unchanged.
- [ ] **G4.3.b** Pair the universal lower bound with the exact Q construction and identify the nonnegative optimal radius.
- [ ] **G4.3.c** Publish the precise dependency list, including whether the optional independent coarse lower bound W.3 has replaced the n=8 import.

## G5 — Every equality packing [PARTIAL]

- [x] **G5.0.a–c** Stratified and signed matched-chain families are necessary/sufficient within their hypotheses; common-coordinate equality has a signed skeleton after a frame choice.
- [x] **G5.0.d** Cap/solid-row terminals pin only their specified anchors. Capless, oblique and nonstratified Q examples remain required controls.
- [x] **G5.0.e necessary restriction** At q=Q, which is not 17/4, a selected two-loaded component cannot occur if all premises of TL.G apply. This is not a complete classification of the >=3-loaded equality cores.
- [ ] **G5.1** After optimality is proved, apply the necessary reductions to EACH original Q packing, not just a replacement minimizer.
- [ ] **G5.2** Characterize every surviving sharp cyclic/equality branch and its zero-weight limits.
- [ ] **G5.3** Provide concise exact necessary-and-sufficient domains for all free centers/angles.
- [ ] **G5.1.a** Once G4 is proved, each original packing atQ is itself minimizing; select its certificate without replacing its physical configuration.
- [ ] **G5.1.b** Retain every equality-compatible signature, including zero stress weights and additional physical contacts.
- [ ] **G5.2.a** Trace equality through each sharp metric inequality used by G3, rather than inferring it from numerical examples.
- [ ] **G5.2.b** Record exactly which stressed positions and frames are forced in each surviving branch.
- [ ] **G5.2.c** Prove the list of equality skeletons exhaustive; the known long/short anchors are conditional inputs until extracted in every surviving branch.
- [ ] **G5.3.a** Derive the exact domains of all unstressed centers and frames around each proved skeleton.
- [ ] **G5.3.b** Include every parameter endpoint, sliding freedom and genuinely rotated free square.
- [ ] **G5.3.c** Prove the converse for every stated parameter value using original containment and physical nonoverlap.
- [ ] **G5.3.d** Give an explicit parameterization or reduced exact domain; do not merely rename the original unrestricted nine-square feasibility problem.
- [ ] **G5.4** Use the actual rotation/relabeling/reflection convention; do not claim a rigid isolated pose when continuous freedoms exist.
- [ ] **G5.4.a** Allow overlapping parameter charts when needed; specify the symmetry relation rather than assuming unique chart representatives.
- [ ] **G5.4.b** Check the oblique-only, nonstratified, capless and two-stack equality controls against the complete classification.
- [ ] **G5.ALL** State and prove the unrestricted if-and-only-if equality theorem.

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
- [ ] **G6.5.a** Pin one source version for every used lemma and check that its hypotheses are supplied at each invocation.
- [ ] **G6.5.b** Verify that normal choices, uncrossing and sparsification preserve all properties subsequently used together.
- [ ] **G6.5.c** Recheck physical holes versus drawing faces, limiting winding, and boundary-versus-open-interior exclusions.
- [ ] **G6.5.d** Check all finite-cover transitions, especially the full aligned S slider branch and strict D endpoint exclusions.
- [ ] **G6.5.e** Confirm that every parent marked closed has a universal proof over its declared continuous domain.
- [ ] **G6.5.f** Audit equality necessity separately from the strict subcritical contradiction and from equality sufficiency.

## G7 — Standard Lean kernel / Palomar proof [DEFERRED; NOT STARTED]

- [ ] **G7.1** Exact original geometry, construction and equality types, without stronger Packing semantics.
- [ ] **G7.2** Compactness, active-gradient/conic arguments, physical stress and planar vector-flow lemmas using proved standard dependencies.
- [ ] **G7.3** Formalize the actual exhaustive sharp physical completion proof, not assumed normal forms or finite sampled cases.
- [ ] **G7.4** Equality necessity and sufficiency.
- [ ] **G7.5 DEFERRED** After the hand proof and draft formalization are complete, compilation/kernel replay requires a later instruction changing the current no-compilation/no-CI constraint. No native-kernel bypass, admission or undisclosed oracle.

## G8 — Integration [NOT STARTED]

- [ ] **G8.1** Add n=9 to Optimum/radius/packing registries and Challenge mirror.
- [ ] **G8.2** Update proof/equality documentation with exact audit and verification status.
- [ ] **G8.3** Check n=1–8 regression and source provenance.
- [ ] **G8.4** Finalize the draft PR only after the advertised unrestricted proof and required verification are actually complete.

## Current execution contract

1. P.ALL, Y.ALL, TREE.ALL and TL.COMPLETE are CLOSED hand at their stated scopes. Keep the general C7 and mixed 3–7-loaded cyclic completion obligations OPEN.
2. The 58 coarse cells now have **three whole-cell exclusions and 55 open rows**. Do not confuse subfamily restrictions with parent closure.
3. Follow the ordered G3 execution tree: the entire C1.3.b1 cell is closed; execute the four complete five-body cells with their exhaustive layout/graph domains, then the larger mixed cells. Pursue the entire C7 capacity in parallel, with its proved conditional piercing criterion and explicit center-cover blocker; continue the remaining mixed cells by component size. Use shared uniform arguments whenever possible. Do not create angle boxes merely to increase checked-gate counts.
4. Preserve exact physical negative controls and every unstressed completion body.
5. Commit finished arguments promptly and log UTC provenance, exact quantifiers, finite evidence and unchanged global blockers in TWO_LOAD_PROGRESS.md or a subsequent append-only checkpoint.
6. If a proposed reduction fails, retain the exact witness and revise it; do not defend a false stronger normalization by shrinking the domain indefinitely.
7. T9 remains open. The newest local manuscripts have passed separate hand audits, while G6 full-chain audit remains open. No Lean or CI success is claimed.


**Completion-continuation review:** the cap endpoint algebra, half-disk separating-axis proof, six-body cap coupling, singleton torque bound and five-body vertex routing received separate hand checks during this continuation. This is local review of the new implications, not a completed G6 audit of the full dependency chain. No Lean build or CI was run.
