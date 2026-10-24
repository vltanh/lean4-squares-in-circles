# Nine unit squares in a circle — current hand-proof frontier

**Branch:** `research/nine-tablefree-hand` · **PR:** #11, draft.  
**Updated:** October 23, 2026, America/Chicago.  
**Target:** the unrestricted sharp squared radius Q=1105/256 and every attaining packing.

**The unrestricted lower bound and complete equality classification remain OPEN.** The construction attains Q. The entire four-body triangle-plus-leaf cell is now closed, so the selected unique positive cyclic component has **5–9 bodies** and **3–7 noncollinear circle-loaded resultants**. Every other physical square remains in the completion problem. The coarse inventory has **three whole cells closed and 55 open**.

## Latest whole-cell closure

[TRIANGLE_LEAF_CELL_CLOSED.md](TRIANGLE_LEAF_CELL_CLOSED.md) closes **C1.3.b1 / G3.M4.ALL**, with an independently audited assembly:

| Complete branch | Exact result | Source |
| --- | --- | --- |
| Full core reduction | Three loaded bodies, exhaustive S/D articulation cover, all contact degeneracies and all five extras retained | [TRIANGLE_LEAF_CORE_REDUCTION.md](TRIANGLE_LEAF_CORE_REDUCTION.md) |
| S leaf | Entire aligned slider interval and both tilted branches excluded by one inaccessible-arc argument | [S_LEAF_TRIANGLE_EXCLUSION.md](S_LEAF_TRIANGLE_EXCLUSION.md) |
| D contact reduction | All articulation reactions point left; exact parallel/opposite-corner alternative | [D_LEAF_ARTICULATION_CONTACT_LOCALIZATION.md](D_LEAF_ARTICULATION_CONTACT_LOCALIZATION.md) |
| D certificate choice | Simultaneous normal selection before the stress theorem removes vertex/vertex articulation contacts and retains uncrossing, sparsity and uniqueness | [D_LEAF_GENERIC_CONTACT_SELECTION.md](D_LEAF_GENERIC_CONTACT_SELECTION.md) |
| Oblique D | Both contact-axis owners, every physical circle-corner mask and every articulation height excluded | [D_LEAF_NONPARALLEL_OWNER_EXCLUSION.md](D_LEAF_NONPARALLEL_OWNER_EXCLUSION.md) |
| Parallel D | Every wall-side mean, arbitrary neighbor frame and mutual contact type excluded | [D_LEAF_PARALLEL_LEFT_EXCLUSION.md](D_LEAF_PARALLEL_LEFT_EXCLUSION.md) |

The proof excludes the selected core itself. It therefore accounts for the five extra squares without needing a separate bound in each completion region. The exact positive D core with older normal choices remains a control: the theorem concerns the necessary selected certificate of a minimizing packing.

## Latest completed five-body and C7 reductions

- [x] [TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md](TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md) excludes the **entire length-two arm layout** of C1.3.b2. It retains both leaf types, both transmitter widths, all articulation orientations, circle masks and contact owners. The two layouts with separate leaves remain open.
- [x] [FOUR_CYCLE_LEAF_HOLE_EMPTY.md](FOUR_CYCLE_LEAF_HOLE_EMPTY.md) proves that **every C4-plus-leaf inner hole has capacity zero**. Equality in the general hole-area bound forces an aligned cross, which cannot carry the required selected stress in the radius window. All four extras must be exterior; their joint capacity remains open.
- [x] [NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md](NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md) gives a uniform exterior-face obstruction. [FIVE_BODY_BICONNECTED_REDUCTION.md](FIVE_BODY_BICONNECTED_REDUCTION.md) then supplies the full ten-type classification and excludes seven types: **only C5, the house and the four-path fan remain**, with explicit necessary load masks.
- [x] The C7 manuscripts below make simultaneous pre-stress normal choices, including whole shared-side blocks and every application mean. A surviving free vertex/vertex edge must meet blocks with a unique radial endpoint body carrying two positive circle-corner weights.

These are complete implications at their stated scope, with independent hand audits. They do not close another coarse cell: the count remains **three closed and 55 open**.

## Continue in this order

The complete gate tree, including continuous domains, contact owners, boundary cases and parent exit conditions, is [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md). The next mixed frontier has exactly four five-body cells, each retaining four arbitrary completion squares.

| Gate | Entire scope | Current state |
| --- | --- | --- |
| C1.3.b2 | Two leaves at one triangle articulation, or leaves at two articulations | OPEN; the entire length-two arm is CLOSED |
| C1.4.b1 | C4 or diamond block with one leaf; both diamond attachment orbits | OPEN; K4 excluded and all cycle holes empty; exterior completion remains |
| C1.5.b0 | C5, house or four-path fan, with the complete necessary load cover and all physical contacts | OPEN; exhaustive graph/load reduction CLOSED |
| C2.33.b0 | Two triangles sharing one articulation, with four loaded tips and all physical contacts retained | OPEN |
| G3.B.CAP | Every positive boundary-only C7, with two arbitrary extra squares | OPEN; parallel whole branch |
| G3.M6–M9 | All remaining mixed cells in increasing component size | OPEN |
| G4–G8 | Universal sharpness, all equality cases, full-chain audit, later formalization and integration | OPEN or blocked by G3 |

[NO_POSITIVE_K4_SUBGRAPH.md](NO_POSITIVE_K4_SUBGRAPH.md) proves a new uniform obstruction: the selected positive graph has no K4 subgraph, anywhere in the inventory. An arbitrarily small physical embedding and an inner-square clearance argument prevent any embedded triangle from enclosing another body center. This closes the K4 branch of C1.4.b1, but does not close its C4 or diamond branches.

## C7: completed geometry and the exact remaining stress obligation

The boundary-only positive component must be one seven-cycle. Its actual force-concurrence polygon is convex, contains the origin, and contains every completion square. No regularity or common orientation is assumed.

- [x] [BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md](BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md): every physical boundary C7 has center diameter strictly below 3.
- [x] [CENTER_COVER_PIERCING.md](CENTER_COVER_PIERCING.md): if all enclosing-ring centers fit in an open disk of radius 3/2, every enclosed unit square contains that disk's center in its strict interior; capacity is at most one.
- [x] [BOUNDARY_TWO_CONTACT_SPAN.md](BOUNDARY_TWO_CONTACT_SPAN.md): two consecutive contacts span less than 3sqrt(3)/2 in the remaining high-radius range. Minimum-center-disk supporting triples with gaps (1,1,5) or (1,2,4) are excluded.
- [x] [C7_CENTER_COVER_GEOMETRIC_OBSTRUCTION.md](C7_CENTER_COVER_GEOMETRIC_OBSTRUCTION.md): the stronger **unstressed** center-cover claim is false, including at radii strictly below sqrt(Q). An exact one-parameter physical ring has a (2,2,3) supporting triple with covering radius greater than 3/2. The same manuscript proves that this ring has no positive C7 stress.
- [x] [C7_FIXED_APPLICATION_GENERIC_SELECTION.md](C7_FIXED_APPLICATION_GENERIC_SELECTION.md): simultaneous finite avoidance removes every free vertex-normal star with one physical circle corner and two fixed application points.
- [x] [C7_TWO_CIRCLE_CORNER_BLOCKS.md](C7_TWO_CIRCLE_CORNER_BLOCKS.md): vertex shells classify radial contacts; selected radial runs have length at most two, so at most four bodies are radial; no two radial bodies are parallel in a physical C7.
- [x] [C7_SHARED_SIDE_BLOCK_GENERIC_SELECTION.md](C7_SHARED_SIDE_BLOCK_GENERIC_SELECTION.md): a collective virtual-work identity handles all variable shared-side means and all circle-weight masks. Every block incident to a surviving free vertex edge has exactly one physical radial body, at an endpoint or as a singleton, with both corner weights positive.
- [ ] Finish both remaining contact domains: every edge has a side-axis owner, retaining two-owner/zero-owner transitions; or at least one free vertex edge survives between the constrained radial-endpoint blocks.
- [ ] The covering route must therefore use positive stress to handle the remaining patterns (1,3,3) and (2,2,3), or be replaced by a complete direct capacity argument.

The piercing criterion is sufficient for capacity one; the counterexample does not claim a two-square completion. For R<sqrt(17)/2, the origin already gives the required strict center cover. The unresolved C7 work is in the higher radius range and retains all physical frames, contact types and zero-load ring vertices.

## Completed prerequisite families

| Input | Exact scope | Primary source |
| --- | --- | --- |
| Lower working window | Delete one square and import the actual n=8 theorem to obtain R>=79/40; inherited table dependencies explicit | [LOWER_WINDOW_FROM_EIGHT.md](LOWER_WINDOW_FROM_EIGHT.md) |
| Physical stress | Actual shared application points, force and torque balance, at most 27 scalar atoms | [PHYSICAL_CONTACT_STRESS.md](PHYSICAL_CONTACT_STRESS.md) |
| Planarity and uniqueness | One selected planar positive component; every circle-touching vertex on its exterior face | [PHYSICAL_BODY_GRAPH_UNCROSSING.md](PHYSICAL_BODY_GRAPH_UNCROSSING.md), [UNIQUE_POSITIVE_COMPONENT.md](UNIQUE_POSITIVE_COMPONENT.md) |
| Full P and Y capacities | Entire slider and fan families; all positive trees and exactly-two-loaded components excluded | [TREE_AND_TWO_LOAD_COMPLETION.md](TREE_AND_TWO_LOAD_COMPLETION.md), [P_ALL_COMPLETION.md](P_ALL_COMPLETION.md), [Y_ALL_COMPLETION.md](Y_ALL_COMPLETION.md) |
| Boundary order | At most seven physical circle contacts; center-angle separation greater than 40 degrees; contacts join angular neighbors | [CENTERED_INNER_ARC.md](CENTERED_INNER_ARC.md), [CIRCLE_CONTACT_ANGULAR_ORDER.md](CIRCLE_CONTACT_ANGULAR_ORDER.md) |
| Simple cycles | A selected simple positive cycle has at most eight bodies | [SIMPLE_POSITIVE_CYCLE_BODY_BOUND.md](SIMPLE_POSITIVE_CYCLE_BODY_BOUND.md) |
| C7 force and routing | Convex concurrence polygon and containment of every completion square | [C7_FORCE_POLYGON.md](C7_FORCE_POLYGON.md), [C7_COMPLETION_LOCALIZATION.md](C7_COMPLETION_LOCALIZATION.md) |
| Contact holes | Ring sizes 3, 4, 5, 6 have interior capacities 0, 1, 1, 2, respectively | [CONTACT_RING_HOLE_AREA.md](CONTACT_RING_HOLE_AREA.md) |
| Outer pockets | The exterior pocket of every touching boundary pair is empty | [CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md](CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md) |
| Common-coordinate class | Complete sharp theorem within that declared class, allowing independent rotations | [COORDINATE_SEPARABLE_NINE_COMPLETE.md](COORDINATE_SEPARABLE_NINE_COMPLETE.md) |

The three closed coarse cells are C1.3.b0, C1.4.b0 and C1.3.b1. Uniform restrictions apply across other cells without marking unresolved multi-load or completion cases closed.

## Equality and method controls

The known Q constructions forbid assuming a global common frame, fixed row structure, rigid central pose or a sharp cap. The conditional equality families remain useful but are not an unrestricted necessity theorem. See [SIGNED_MATCHED_EQUALITY_FAMILY.md](SIGNED_MATCHED_EQUALITY_FAMILY.md), [STRATIFIED_EQUALITY_FAMILY.md](STRATIFIED_EQUALITY_FAMILY.md), [NO_GLOBAL_ORTHOGONAL_FRAME.md](NO_GLOBAL_ORTHOGONAL_FRAME.md), [NONSTRATIFIED_PARALLEL_NINE.md](NONSTRATIFIED_PARALLEL_NINE.md), and [TWO_STACK_SHARP_EQUALITY_WITNESS.md](TWO_STACK_SHARP_EQUALITY_WITNESS.md).

The positive regular C7 below Q is a feasible smaller core with capacity one; it does not classify every stationary ring. [ADDITIVE_MEASURE_OBSTRUCTION.md](ADDITIVE_MEASURE_OBSTRUCTION.md) excludes an independent-square nonnegative additive measure of total mass below nine as the missing proof method. Center-only relaxations, finite parameter scans and counts of checked subgates do not prove the universal theorem.

## Verification and navigation

The new local proofs and whole-cell assembly have independent hand audits. The complete earlier prerequisite chain and standard-kernel verification remain separate open gates. **No Lean compilation or CI was run. Every new commit uses `[skip ci]`, and PR #11 remains draft while the unrestricted theorem is unfinished.**

- [ROADMAP.md](ROADMAP.md): concise ordered frontier.
- [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): full G0–G8 execution contracts and deeply nested exit gates.
- [G2_SUBGATES.md](G2_SUBGATES.md): live prerequisite and closure ledger.
- [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md): all 58 coarse cells individually ticked, three closed and 55 open.
- [TWO_LOAD_PROGRESS.md](TWO_LOAD_PROGRESS.md): append-only proof, audit, commit and exact-regression provenance; earlier checkpoint counts remain historical.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): all six tree profiles, now closed.
