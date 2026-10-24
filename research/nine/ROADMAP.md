# n=9 — ordered roadmap to the unrestricted hand proof

**PR:** #11, draft. **Reconciled source:** `f9fa9a3694185b0ba02b17fd5192f04fe07da791`.  
**Updated:** October 24, 2026, America/Chicago.

**The unrestricted lower bound R^2>=1105/256 and complete equality classification remain OPEN.** The construction attains Q. The full execution tree, exact subgates and boundary cases are in [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md).

## New whole-cell closure

[TRIANGLE_LEAF_CELL_CLOSED.md](TRIANGLE_LEAF_CELL_CLOSED.md) closes **C1.3.b1 / G3.M4.ALL**. The full core reduction, entire S branch, entire selected oblique D branch and entire parallel-left D branch have complete proofs. Their simultaneous pre-stress normal selections retain the actual physical geometry, planar uncrossing, sparsity and unique component. Both D proofs and the parent assembly have independent hand audits.

The unique positive cyclic component now has **5–9 bodies** and **3–7 noncollinear circle-loaded resultants**. Every other physical square remains. The coarse inventory is **four whole cells closed and 54 open**; these counts are not progress percentages.

### Completed whole-cell continuation

TRIANGLE_TWO_BRIDGES_CELL_CLOSED.md closes C1.3.b2. DISTINCT_S_LEAF_WALL_UPPER_CAPACITY.md proves upper capacity3 through actual ray screening and all-orientation center bounds; DISTINCT_S_LEAF_WALL_LOWER_EMPTY.md excludes both lower regions, including both possible oblique endpoint wraps. Every slider value and every candidate extra frame is covered. The parent assembly exhausts chain, same-articulation and distinct-articulation attachments under one compatible certificate. Independent full audits passed.

FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md makes a separate canonical-minimizer reduction: physical AU contact, singleton A-tip edges, and the full two-A-owned D-leaf exclusion. FOUR_CYCLE_UNIQUE_TIPS_EXCLUSION.md then closes the entire physical unique/unique opposite-load mask, with all U-parallel endpoints and actual channel means. FOUR_CYCLE_TWO_RADIAL_TIPS_EXCLUSION.md closes the entire physical two/two mask without secondary minimization. RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md now removes every free A-tip normal at the canonical minimizer for all physical circle masks. FOUR_CYCLE_MIXED_D_LEAF_EXCLUSION.md closes the entire radial-D-leaf opposite-load C4, including both mixed owner orders and every U-parallel radial endpoint. Together with the unique/unique and two/two exclusions, the sole opposite-load residual is an S leaf with one unique-circle-corner tip and one two-circle-corner tip. Both tip-owned contacts are also excluded for that S branch. Every actual channel mean and radial corner-weight split remains. The three-loaded-block C4 and both diamond attachment orbits remain open; this canonical reduction does not classify every original equality packing.

C7_CENTER_POLYGON_LOCALIZATION.md places every completion unit inside the strictly convex center polygon. C7_DIAMETER_EXTRACTION_COUNTEREXAMPLE.md disproves the unrestricted diameter extraction with an exact actual seven-square ring enclosing two units. C7_INNER_SIDE_CORNER_RESTRICTIONS.md proves that each inner square's own-frame center coordinates have absolute value below3721/7200, every inner vertex has norm greater than sqrt(5/2)-91/60, and any two inner frames satisfy cos(theta)>6/7. PARALLEL_INNER_PAIR_DIAMETER_EXTRACTION.md then excludes the entire theta=0 branch, with arbitrary gap and stagger: every qualifying enclosing center polygon would have diameter at least3. A surviving pair therefore has 0<theta<acos(6/7), with both exact disk-dependent restrictions retained. The full nonparallel completion/radius theorem remains open. The valid C7 route must retain the disk/annulus or positive stress. A complete R^2>=Q implication is sufficient for G3.B; the stronger no-two-extras-at-Q claim is optional, with equality handled separately.


## Completed inputs

- [x] Exact physical semantics, compact minimizer and actual force/torque certificate.
- [x] Entire common-coordinate-separable class, with its conditional equality skeleton.
- [x] Full P and Y completion capacities; every selected positive tree and every exactly-two-loaded component excluded in the declared window.
- [x] One selected planar positive component; at most 27 scalar atoms; all circle-touching vertices on its exterior face.
- [x] At most seven physical circle contacts, center separation greater than 40 degrees, and angular-neighbor contacts.
- [x] Boundary-only positive components are exactly C7; every extra lies inside its convex force-concurrence polygon.
- [x] Simple positive cycles have at most eight bodies.
- [x] Contact-ring interior capacities for k=3,4,5,6 are 0,1,1,2; exterior pockets of touching boundary pairs are empty.
- [x] C1.3.b0, C1.4.b0 and the entire C1.3.b1 are excluded.
- [x] NO_POSITIVE_K4_SUBGRAPH.md excludes K4 subgraphs throughout the selected graph inventory, including the K4 branch of C1.4.b1.
- [x] NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md excludes three circle-touching common positive neighbors of any two body vertices.
- [x] FIVE_BODY_BICONNECTED_REDUCTION.md classifies all ten five-body biconnected graph types and reduces them to C5, house and four-path fan with complete necessary positive-load masks.
- [x] TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md excludes the entire length-two arm layout of C1.3.b2, with every leaf/transmitter type and articulation pose.
- [x] TRIANGLE_TWO_LEAVES_SAME_ARTICULATION_CLOSED.md assembles the complete S/S, D/S and D/D exclusions and closes the entire same-articulation layout, including every shared mean and contact owner. The distinct-articulation completion is now also closed by the full assembly.
- [x] TRIANGLE_DISTINCT_LEAVES_DOMAIN.md and TRIANGLE_DISTINCT_LEAVES_PORT_ORIENTATION.md give the complete distinct-layout load/radius/moment domain and the positive radial-concurrence theorem, including parallel C forces and all actual means.
- [x] TRIANGLE_DISTINCT_MIXED_LEAVES_EXCLUSION.md excludes the entire distinct D/S branch through an owner-independent support-span contradiction. The remaining S/S completion is closed by the full exact-family capacity theorem.
- [x] DISTINCT_S_LEAF_CORE_AND_CORNER_MASK.md excludes every two-circle-corner C mask and supplies an exact positively stressed S/S core below Q. Blanket core exclusion is false; the subsequent complete slider classification and upper/lower capacity theorem prove capacity at most three throughout the family.
- [x] GENERAL_FIXED_TIP_NORMAL_SELECTION.md removes free vertex normals from every distinct-fixed-application unique-circle-corner tip without a boundary-neighbor premise; the coincident radial-D exception and variable means are retained.
- [x] UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md proves an orientation-uniform contact-triangle obstruction: a side-owned normal has nonnegative dot product with the other normal. Its radial-leaf consequence fixes the opposite support face without any circle or generic-normal premise.
- [x] DISTINCT_S_LEAVES_PARALLEL_ARTICULATION_REDUCTION.md reduces **every remaining distinct S/S core** to an articulation with an aligned leaf and parallel cycle forces. The complete tilted and shared-AB cases are excluded, all means and four extras retained. The full wall is classified below, and its complete upper/lower capacity theorem now closes the family.
- [x] DISTINCT_S_LEAVES_WALL_CLASSIFICATION.md exhausts every wall frame and contact owner. The three central frames align, x=(sqrt(70)-8)/4 fixes the exact radius, and the **entire** articulation interval is x(1-2x)/(1-x)<=t<2x, with explicit force and actual-mean intervals. Every interval member is a positive physical core; capacity<=3 is proved by the whole upper/lower routing theorems.
- [x] FOUR_CYCLE_PARALLEL_BYPASS_EXCLUSION.md excludes the **entire A/U-parallel opposite-load C4 chart**, including both S/D leaves, every tip frame and actual shared mean.
- [x] FOUR_CYCLE_OBLIQUE_TIP_OWNER_EXCLUSION.md excludes the complete chart where both loaded tips are oblique to the transmitter and own point contacts with the bypass, for all physical one/two-corner masks.
- [x] FOUR_CYCLE_UNIQUE_LOAD_NORMAL_SELECTION.md removes every free A-tip normal throughout the physical unique/unique mask while preserving all other variable means. The later all-mask selection and complete D-leaf theorem below supersede this earlier physical-mask restriction.
- [x] C7_HIGH_CENTER_CONTACT_TYPES.md classifies every high-center contact and proves every positively loaded two-owned body has center radius below23/16 and a right-angle force turn; the whole C7 capacity remains open.
- [x] FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md closes every adjacent-loaded-pair C4 leaf case by a full normal-channel/boundary-detour obstruction.
- [x] BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md removes free vertex normals from every unique-circle-corner degree-two star with fixed applications and at least one boundary neighbor; shared means are explicitly retained elsewhere.
- [x] C7_PINNED_VERTEX_CONTACT_TYPES.md reduces all free vertex edges to radial/radial contacts or mirror-paired two-square blocks. The complete length2–5 profiles, contact-radius bound and length3 exclusion are proved.
- [x] FOUR_CYCLE_LEAF_HOLE_EMPTY.md proves zero inner capacity for the whole C4-plus-leaf branch; all surviving C1.4.b1 completion is exterior.
- [x] C7 fixed-application and shared-side-block generic selection retains all application means and load masks. Free vertex edges require unique radial endpoints with both corner weights positive; radial runs have length at most two, and parallel radial pairs are impossible.
- [x] C7_TWO_FREE_EDGES_EXCLUSION.md excludes both whole two-free-edge layouts. C7_RADIAL_VERTEX_EDGE_EXCLUSION.md and C7_MIRROR_VERTEX_EDGE_EXCLUSION.md then exclude every remaining free edge by legitimate pre-stress open choices. The entire residual C7 contact domain is now side-axis-owned.
- [x] S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md closes the S-leaf diamond-hub case with a boundary second hub, by a connected-boundary-neighbor obstruction.
- [x] UNIT_BYPASS_NORMAL_CHANNEL.md reduces every unit-bypassed channel to one side-normal transmitter; the surviving opposite-load C4 retains its full width-one means.
- [x] Every physical boundary C7 has center diameter below 3; two consecutive contacts span less than 3sqrt(3)/2 in the high-radius range.
- [x] An open radius-3/2 cover of enclosing-ring centers implies a common strict interior point and completion capacity at most one.
- [x] An exact physical C7 control disproves the unstressed center-cover claim; that control has no positive C7 stress.
- [x] The explicit n=8 import supplies R>=79/40; its inherited arithmetic-table dependencies are declared.

These are hand implications. The full prerequisite-chain audit and Lean verification remain separate open work.

## Execute the five-body frontier, with C7 in parallel

The identity m=1+sum(block_size-1)+bridges gives exactly four five-body cyclic cells. C1.3.b2 is now closed by the full attachment/classification/capacity assembly; the three remaining cells retain four arbitrary physical completion squares.

| Order | Whole gate | Exhaustive scope | Required exit |
| --- | --- | --- | --- |
| CLOSED | C1.3.b2 | Entire three-attachment triangle-with-two-bridges cell | TRIANGLE_TWO_BRIDGES_CELL_CLOSED.md; upper/lower capacities3 and0 over the whole exact slider |
| 2 | C1.4.b1 | S-leaf mixed-mask opposite-load C4; three-loaded-block C4; both diamond orbits | All D leaves, unique/unique, two/two and both-tip-owned opposite-load branches CLOSED; finish S residual and the other full branches |
| 3 | C1.5.b0 | C5 with three/four loads; house with three mask orbits; fan with three/four loads | Finish each complete graph/load family with every actual contact and four extras |
| 4 | C2.33.b0 | Two triangles sharing one articulation, four loaded tips and every zero-weight physical contact | Full joint capacity or core/radius theorem |
| Parallel | G3.B.SHARP | Every all-owned boundary C7 with two arbitrary extras; remaining frame angle0<theta<acos(6/7) | Prove R^2>=Q, or the stronger capacity-one theorem; equality retained separately |
| 5 | G3.M6–M9 | Every remaining mixed cell in increasing component size | Sharp bound or full completion exclusion for each entire cell |
| 6 | G4 | All original nine-square packings | Universal R^2>=1105/256 |
| 7 | G5 | Every equality packing and every proposed parameter family | Necessary-and-sufficient unrestricted classification |
| 8 | G6–G8 | Full audit, later standard-kernel formalization and integration | Verified advertised theorem and completed PR |

Do not import S/D leaf geometry at a nonleaf bridge endpoint. Do not infer a common frame from parallel forces in a smaller subgraph. Every physical square, zero circle weight, shared-side application mean and contact-junction limit remains in the relevant full branch.

## Exact C7 frontier

[CENTER_COVER_PIERCING.md](CENTER_COVER_PIERCING.md) proves the strict-piercing implication from a radius-3/2 center cover. The desired cover may be translated; its center need not be the containing circle's origin. The diameter theorem excludes two-point supports of a failing minimum center disk. The two-contact span theorem excludes acute supporting triples with graph gaps (1,1,5) and (1,2,4).

The remaining covering targets are **positive-stress** supporting triples of types (1,3,3) and (2,2,3). [C7_CENTER_COVER_GEOMETRIC_OBSTRUCTION.md](C7_CENTER_COVER_GEOMETRIC_OBSTRUCTION.md) gives exact unstressed counterexamples of the latter type at Q and at strictly smaller radii, then proves that they cannot carry a positive C7 stress. Thus a general geometric center-cover theorem is a rejected normalization, not an unfinished premise to assume.

The simultaneous normal reductions are now complete through C7_RADIAL_VERTEX_EDGE_EXCLUSION.md and C7_MIRROR_VERTEX_EDGE_EXCLUSION.md. They exclude the entire free-vertex domain and leave **all edges side-axis-owned**, retaining every change of ownership and every shared-side mean. The proof uses a collective virtual motion, so variable shared-side applications are not frozen. C7_PINNED_VERTEX_CONTACT_TYPES.md now classifies every free edge within the second domain: radial/radial contacts or the unique outer-adjacent-corner contact between two mirror two-square blocks. All other length pairs and vertex types are excluded. Adaptive open choices require a shared-side neighbor at both ends of every radial pair. The full free-edge graph has at most two edges, with an exhaustive length2–5 block-profile cover. C7_TWO_FREE_EDGES_EXCLUSION.md closes both two-edge layouts; the two final open normal selections close the radial/radial and mirror modules completely. The all-owned domain still requires its full force/torque, center-cover or direct capacity theorem. Zero-owner/two-owner transitions remain; no one-owner-per-body assumption is supplied.

A complete direct capacity proof or a fully exhaustive stationary classification may replace the cover route. Such a classification must include two-owner/zero-owner transitions, one/two-circle-corner masks, zero circle loads and nonconstant periodic solutions. Closed origin containment alone would not give strict piercing. Far-vertex spans do not imply the needed boundary-center diameter lower bound.

## Finite coverage, audit and evidence

[CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md) lists all 58 coarse cells. The deep roadmap refines each open cell by positive versus physical contact graphs, embeddings, boundary/load masks, actual contact features, junction identifications and completion regions. Continuous poses and weights stay universally quantified. Finite semantic labels are not a numerical parameter cover.

Known equality controls prohibit assumed global common-frame, rigid-pose, stratification and sharp-cap hypotheses. A whole-cell closure is not inferred from one example or one contact-owner pattern.

[TWO_LOAD_PROGRESS.md](TWO_LOAD_PROGRESS.md) is the append-only evidence record. Commit finished proofs and exact roadmap updates through the GitHub connector with `[skip ci]`. Keep the PR draft while T9 is unfinished. No Lean compilation or CI is authorized under the current instruction; hand audits are not kernel verification.
