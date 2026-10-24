# Nine unit squares in a circle — current hand-proof frontier

**Branch:** `research/nine-tablefree-hand` · **PR:** #11, draft.  
**Updated:** October 24, 2026, America/Chicago.  
**Target:** the unrestricted sharp squared radius Q=1105/256 and every attaining packing.

**The unrestricted lower bound and complete equality classification remain OPEN.** The construction attains Q. The entire four-body triangle-plus-leaf cell is now closed, so the selected unique positive cyclic component has **5–9 bodies** and **3–7 noncollinear circle-loaded resultants**. Every other physical square remains in the completion problem. The coarse inventory has **five whole cells closed and 53 open**.

## Latest whole-cell closure: C1.3.b2

[TRIANGLE_TWO_BRIDGES_CELL_CLOSED.md](TRIANGLE_TWO_BRIDGES_CELL_CLOSED.md) closes **every triangle with two bridges**. The chain and same-articulation layouts were already excluded. The full distinct S/S family is now classified at one exact radius, over the entire slider interval x(1-2x)/(1-x)<=t<2x for x=(sqrt(70)-8)/4. [The upper region holds at most three extras](DISTINCT_S_LEAF_WALL_UPPER_CAPACITY.md), and [both lower regions are empty](DISTINCT_S_LEAF_WALL_LOWER_EMPTY.md). Both proofs retain all extra orientations, valid slider endpoints and squares that might extend around an obstacle end. Four extras are required for nine units, so the whole cell is excluded. Root and separate full capacity and assembly audits passed.

The exact positive five-body core remains valid; its universal capacity is at most eight units in total. The count is now **five closed coarse cells and 53 open**. The remaining five-body cells are C1.4.b1 and C1.5.b0; C2.33.b0 is closed by the complete bowtie theorem.

## Latest whole-cell closure: the bowtie

[BOWTIE_CELL_CLOSED.md](BOWTIE_CELL_CLOSED.md) closes the entire five-body bowtie C2.33.b0. The complete end-triangle theorem proves c_A dot M>0 for every actual owned/free articulation interface, every one-/two-circle-corner mask and every shared-side mean. Its new [mixed-owner](BOWTIE_MIXED_OWNER_PRESSURE.md), [radial-free](BOWTIE_RADIAL_FREE_INTERFACE_PRESSURE.md) and [shared/free](BOWTIE_SHARED_SIDE_FREE_INTERFACE.md) proofs retain the same compatible pre-certificate selection. The two bowtie block resultants must be opposite, contradicting their positive projections. All four extras remain arbitrary; no secondary minimizer or regional capacity estimate is needed.

Root and independent full hand audits passed every local source and the parent assembly. Review corrected an omitted variance term in an intermediate mixed-owner draft: the final proof uses the true circle-force mean length, with separate valid coefficients for unique and two-corner masks. The complete corrected source is committed. The coarse count is now **five whole cells closed and53 open**. The remaining five-body parents are C1.4.b1 and C1.5.b0; the unrestricted theorem and equality remain open.

## Latest whole-region and physical-mask checkpoint

[HOUSE_HOLE_EMPTY.md](HOUSE_HOLE_EMPTY.md) closes the entire house's bounded completion regions. An enclosed unit forces an aligned four-cycle cross; at a clear degree-three hub, every possible roof reaction has nonpositive outward-side projection while both cycle reactions have strictly negative projection. The positive force balance fails. The loaded roof and forbidden boundary triangle guarantee such a clear hub. Every load mask and actual mean is covered: all four house extras are exterior, while their joint exterior bound remains open.

[D_DIAMOND_RADIAL_HUB_EXCLUSION.md](D_DIAMOND_RADIAL_HUB_EXCLUSION.md) excludes the entire physical two-circle-corner second-hub mask in the D-leaf diamond, for every mask of its two tips. The proof retains both individual zero corner weights, every free normal and all shared means. Global corner directions, the full A support-sign cover and a purely geometric wall-pair theorem give the contradiction. The remaining second hub is positively loaded and has exactly one physical circle corner.

[BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md](BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md) closes the entire perpendicular A-owned class without selecting the mutual tip normal. [RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md](RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md) proves a uniform positive projection on each radial-S circle corner, margin121/1600. Consequently every both-radial end triangle has positive pressure for all contact owners and means. The complete both-A-owned class is resolved as well. The later complete mixed-owner and free-interface theorems now close the entire bowtie cell. The same radial-neighbor theorem excludes the all-radial four-load fan and house end-triple masks.

[C7_SHARP_BALANCED_RADIAL_TAIL.md](C7_SHARP_BALANCED_RADIAL_TAIL.md) supplies a sharp continuous two-coordinate bound over the complete balanced sector. [C7_OUTSIDE_INNER_RAY_WITNESS.md](C7_OUTSIDE_INNER_RAY_WITNESS.md) identifies the actual ray witness with an extracted far-face boundary unit using a unique narrow center cap; its signed offset excludes the whole balanced right-outside sector. The exact remaining split is the unbalanced right-outside branch or the asymmetric left-outside/right-inside branch. Both actual outer frames remain. No full C7 radius/capacity theorem is claimed. All these completed local and whole-region results have root and separate full hand audits.

## Latest structural and whole-branch checkpoint

[NO_UNLOADED_DIAMOND_HUB.md](NO_UNLOADED_DIAMOND_HUB.md) proves a new radius-free selected-certificate obstruction: an unloaded vertex of exact positive degree three cannot have a physical neighbor touching both other neighbors. The complete owner, corner, generic-normal and tangential-width proof closes the **entire S-leaf diamond-hub attachment**, the **entire diamond tip attachment for both leaf types**, and **both three-load fan masks**. All physical zero-weight contacts and actual means remain. C1.4.b1 now has exactly two unresolved families: the all-three-loaded C4, and the D-leaf diamond hub with a unique-physical-corner loaded second hub.

[BOWTIE_TIP_OWNED_PRESSURE.md](BOWTIE_TIP_OWNED_PRESSURE.md) and [BOWTIE_PARALLEL_PRESSURE.md](BOWTIE_PARALLEL_PRESSURE.md) prove c_A dot M>0 for two whole end-triangle domains, all physical circle masks retained. The parallel theorem explicitly includes coincident shared-wall endpoint means. Two blocks drawn from those domains cannot form a bowtie, since their resultants are opposite. The later full owner/free cover now closes the entire bowtie cell.

[FIVE_CYCLE_THREE_LOAD_DOUBLE_DIAGONAL_EXCLUSION.md](FIVE_CYCLE_THREE_LOAD_DOUBLE_DIAGONAL_EXCLUSION.md) excludes the entire two-diagonal-transmitter chart: legitimate endpoint ownership forces a common frame, and the actual BC contact gives R^2>=(9+6sqrt(2))/4>Q. The three-load C5 now has nonparallel isolated-load forces and at most one diagonal transmitter. The full nonparallel side/side and side/diagonal families, four-load C5 and house remain open.

[C7_INNER_OUTSIDE_FACE_CORNER_EXCLUSION.md](C7_INNER_OUTSIDE_FACE_CORNER_EXCLUSION.md) improves the full inner-pair domain to0<sin(theta)<4/15 by an all-frame outgoing-ray theorem. [C7_INNER_PAIR_FAR_FACE_CENTERS.md](C7_INNER_PAIR_FAR_FACE_CENTERS.md) then extracts two actual boundary centers beyond the pair's opposite outward faces and proves their exact diameter-gap budget, with every offset and outer frame retained. The full nonparallel radius/capacity implication remains open. These complete local results have root and separate full hand audits.

## Earlier whole-cell closure: C1.3.b1

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

- [x] [TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md](TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md) excludes the **entire length-two arm layout** of C1.3.b2. It retains both leaf types, both transmitter widths, all articulation orientations, circle masks and contact owners. The same-articulation layout is now also closed below; the distinct-articulation completion is now also closed by the whole-cell assembly.
- [x] [FOUR_CYCLE_LEAF_HOLE_EMPTY.md](FOUR_CYCLE_LEAF_HOLE_EMPTY.md) proves that **every C4-plus-leaf inner hole has capacity zero**. Equality in the general hole-area bound forces an aligned cross, which cannot carry the required selected stress in the radius window. All four extras must be exterior; their joint capacity remains open.
- [x] [NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md](NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md) gives a uniform exterior-face obstruction. [FIVE_BODY_BICONNECTED_REDUCTION.md](FIVE_BODY_BICONNECTED_REDUCTION.md) then supplies the full ten-type classification and excludes seven types: **only C5, the house and the four-path fan remain**, with explicit necessary load masks.
- [x] [FIVE_CYCLE_THREE_LOAD_PARALLEL_EXCLUSION.md](FIVE_CYCLE_THREE_LOAD_PARALLEL_EXCLUSION.md) excludes parallel pair forces at the isolated loaded vertex of the entire three-load C5 branch. Nonzero cycle moment excludes D; every side-normal transmitter ends too centrally for its boundary neighbor; two diagonal transmitters overlap. All actual means and four extras remain. The full nonparallel and four-load C5 families stay open.
- [x] [TRIANGLE_TWO_LEAVES_SAME_ARTICULATION_CLOSED.md](TRIANGLE_TWO_LEAVES_SAME_ARTICULATION_CLOSED.md) closes the **entire same-articulation layout**. The complete S/S, D/S and [D/D proof](TWO_D_LEAVES_ONE_TRIANGLE_ARTICULATION.md) retain every support feature, actual shared-side mean, contact owner, positive leaf weight and radius endpoint. Root and separate audits passed; all four extras remain accounted for by the core exclusion.
- [x] [TRIANGLE_DISTINCT_LEAVES_DOMAIN.md](TRIANGLE_DISTINCT_LEAVES_DOMAIN.md) gives the full distinct-articulation domain: exactly three loads, no D/D pair, nonzero triangle moment, and R>sqrt(17)/2 including an exact endpoint exclusion. [TRIANGLE_DISTINCT_LEAVES_PORT_ORIENTATION.md](TRIANGLE_DISTINCT_LEAVES_PORT_ORIENTATION.md) proves the moment sign and positive radial concurrence, including parallel C forces and every actual mean.
- [x] [TRIANGLE_DISTINCT_MIXED_LEAVES_EXCLUSION.md](TRIANGLE_DISTINCT_MIXED_LEAVES_EXCLUSION.md) excludes the **entire distinct D/S branch**. A positive-concurrence support calculation and an exact unit-square support-span bound contradict the required final triangle contact, for every contact owner and circle mask. The S/S completion is now also closed by the exact-family capacity theorem.
- [x] [DISTINCT_S_LEAF_CORE_AND_CORNER_MASK.md](DISTINCT_S_LEAF_CORE_AND_CORNER_MASK.md) excludes every physical two-circle-corner mask of C, then constructs an exact positive S/S core strictly below the target radius, with fixed side normals and strict shared means. **A blanket S/S core exclusion is false.** The subsequent full classification and universal upper/lower capacity theorem now close every such core completion.
- [x] [GENERAL_FIXED_TIP_NORMAL_SELECTION.md](GENERAL_FIXED_TIP_NORMAL_SELECTION.md) removes free vertex normals from every unique-circle-corner degree-two tip with distinct fixed applications, even when both neighbors are circle-clear. Variable shared means and the exact coincident radial-D exception remain.
- [x] [FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md](FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md) excludes the entire adjacent-loaded-pair C4-plus-leaf pattern. Its stronger geometric theorem prevents a normal channel from a near-origin articulation from returning through a circle-touching neighbor.
- [x] [BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md](BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md) extends generic selection to a degree-two unique-circle-corner tip with only one boundary neighbor. Both actual applications must be fixed; variable shared-side means remain outside this lemma.
- [x] [S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md](S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md) excludes a radial S leaf when every other load lies in a connected physical graph of boundary neighbors of its articulation. It closes the entire S-leaf diamond-hub branch with a physically boundary second hub, including zero weight there.
- [x] [UNIT_BYPASS_NORMAL_CHANNEL.md](UNIT_BYPASS_NORMAL_CHANNEL.md) proves that any normal channel whose endpoints have a common unit-square neighbor has exactly one side-normal transmitter. The opposite-load C4 branch therefore has reserve exactly one, with all means retained. A full separating-axis argument also forces the bypass articulation and transmitter to lie side by side in the transmitter frame, including every tilted articulation.
- [x] [UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md](UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md) proves an orientation-uniform contact-triangle obstruction: a side-owned normal has nonnegative dot product with the other normal. Its radial-leaf consequence fixes the opposite support face without any circle or generic-normal premise.
- [x] [DISTINCT_S_LEAVES_PARALLEL_ARTICULATION_REDUCTION.md](DISTINCT_S_LEAVES_PARALLEL_ARTICULATION_REDUCTION.md) reduces **every remaining distinct S/S core** to an articulation with an aligned leaf and parallel cycle forces. The complete tilted and shared-AB cases are excluded, all means and four extras retained. The full wall is classified below, and its complete upper/lower capacity theorem now closes the family.
- [x] [DISTINCT_S_LEAVES_WALL_CLASSIFICATION.md](DISTINCT_S_LEAVES_WALL_CLASSIFICATION.md) exhausts every wall frame and contact owner. The three central frames align, x=(sqrt(70)-8)/4 fixes the exact radius, and the **entire** articulation interval is x(1-2x)/(1-x)<=t<2x, with explicit force and actual-mean intervals. Every interval member is a positive physical core; capacity<=3 is proved by the whole upper/lower routing theorems.
- [x] [FOUR_CYCLE_PARALLEL_BYPASS_EXCLUSION.md](FOUR_CYCLE_PARALLEL_BYPASS_EXCLUSION.md) excludes the **entire A/U-parallel opposite-load C4 chart**, including both S/D leaves, every tip frame and actual shared mean.
- [x] [FOUR_CYCLE_OBLIQUE_TIP_OWNER_EXCLUSION.md](FOUR_CYCLE_OBLIQUE_TIP_OWNER_EXCLUSION.md) excludes the complete chart where both loaded tips are oblique to the transmitter and own point contacts with the bypass, for all physical one/two-corner masks.
- [x] [FOUR_CYCLE_UNIQUE_LOAD_NORMAL_SELECTION.md](FOUR_CYCLE_UNIQUE_LOAD_NORMAL_SELECTION.md) removes every free A-tip normal throughout the physical unique/unique mask while preserving all other variable means. The later all-mask selection and complete D-leaf theorem below supersede this earlier physical-mask restriction.
- [x] The **entire C7 free-normal branch is now excluded**. The completed block/profile selections and the two final vertex-edge exclusions leave actual side-axis owners on every edge. The remaining full C7 capacity problem retains all owner transitions and shared-side means.

The complete upper/lower capacity and attachment assembly close C1.3.b2. Other local implications retain their stated scopes and do not close their larger parents. The count is **five closed and 53 open**.


### Completed whole-cell continuation

TRIANGLE_TWO_BRIDGES_CELL_CLOSED.md closes C1.3.b2. DISTINCT_S_LEAF_WALL_UPPER_CAPACITY.md proves upper capacity3 through actual ray screening and all-orientation center bounds; DISTINCT_S_LEAF_WALL_LOWER_EMPTY.md excludes both lower regions, including both possible oblique endpoint wraps. Every slider value and every candidate extra frame is covered. The parent assembly exhausts chain, same-articulation and distinct-articulation attachments under one compatible certificate. Independent full audits passed.

FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md makes a separate canonical-minimizer reduction: physical AU contact, singleton A-tip edges, and the full two-A-owned D-leaf exclusion. FOUR_CYCLE_UNIQUE_TIPS_EXCLUSION.md then closes the entire physical unique/unique opposite-load mask, with all U-parallel endpoints and actual channel means. FOUR_CYCLE_TWO_RADIAL_TIPS_EXCLUSION.md closes the entire physical two/two mask without secondary minimization. RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md now removes every free A-tip normal at the canonical minimizer for all physical circle masks. FOUR_CYCLE_MIXED_D_LEAF_EXCLUSION.md closes the entire radial-D-leaf opposite-load C4, including both mixed owner orders and every U-parallel radial endpoint. FOUR_CYCLE_MIXED_S_LEAF_EXCLUSION.md now closes every remaining S-leaf support feature and owner order. FOUR_CYCLE_OPPOSITE_LOAD_BRANCH_CLOSED.md assembles the entire opposite-loaded-pair C4 exclusion, with all physical corner masks, zero individual radial weights, actual channel means and four extras retained. The two independent audits passed. Together with the adjacent-load theorem, this leaves only the all-three-loaded C4; the remaining D-leaf unique-corner loaded-hub diamond branch remains open. This canonical lower-bound reduction does not classify every original equality packing.

C7_CENTER_POLYGON_LOCALIZATION.md places every completion unit inside the strictly convex center polygon. C7_DIAMETER_EXTRACTION_COUNTEREXAMPLE.md disproves the unrestricted diameter extraction with an exact actual seven-square ring enclosing two units. C7_INNER_SIDE_CORNER_RESTRICTIONS.md proves that each inner square's own-frame center coordinates have absolute value below3721/7200, every inner vertex has norm greater than sqrt(5/2)-91/60, and any two inner frames satisfy cos(theta)>6/7. PARALLEL_INNER_PAIR_DIAMETER_EXTRACTION.md then excludes the entire theta=0 branch, with arbitrary gap and stagger: every qualifying enclosing center polygon would have diameter at least3. That initial restriction is now sharpened below to0<sin(theta)<4/15, with both exact disk-dependent restrictions retained. The full nonparallel completion/radius theorem remains open. The valid C7 route must retain the disk/annulus or positive stress. A complete R^2>=Q implication is sufficient for G3.B; the stronger no-two-extras-at-Q claim is optional, with equality handled separately.

## Continue in this order

The complete gate tree, including continuous domains, contact owners, boundary cases and parent exit conditions, is [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md). The five-body inventory has four cells; C1.3.b2 and C2.33.b0 are closed and two remain open, each retaining four arbitrary completion squares.

| Gate | Entire scope | Current state |
| --- | --- | --- |
| C1.3.b2 | All three bridge attachments, every leaf type and all four extras | CLOSED; entire slider upper/lower capacities3 and0, full assembly audited |
| C1.4.b1 | All-three-loaded C4; D-leaf diamond hub with a unique-physical-corner loaded second hub | OPEN; other C4/diamond attachments CLOSED; all holes empty |
| C1.5.b0 | C5, house or four-path fan, with the complete necessary load cover and all physical contacts | OPEN; exhaustive graph/load reduction CLOSED |
| C2.33.b0 | Entire bowtie, all circle masks, means and four extras | CLOSED; complete end-triangle pressure and opposite-resultant assembly |
| G3.B.CAP | Every positive boundary-only C7, with two arbitrary extra squares | OPEN; parallel branch excluded; actual opposite boundary centers extracted |
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
- [x] [C7_PINNED_VERTEX_CONTACT_TYPES.md](C7_PINNED_VERTEX_CONTACT_TYPES.md) exhausts the free vertex-edge geometry: only radial/radial contacts or mirror-paired two-square blocks remain. All other block-length pairs and vertex types are excluded; the local proof also gives a uniform lower radius for every boundary/boundary contact point.
- [x] Adaptive open choices on maximal radial runs require positive-length shared sides at both ends of every radial pair. At most two free edges survive; the full arrangement and length2–5 block-profile cover is explicit.
- [x] [C7_TWO_FREE_EDGES_EXCLUSION.md](C7_TWO_FREE_EDGES_EXCLUSION.md) independently excludes both complete two-free-edge layouts: 2+2+3 by closing-center separation, and 2+2+2 plus a singleton by an orientation-uniform two-point radius bound.
- [x] [C7_RADIAL_VERTEX_EDGE_EXCLUSION.md](C7_RADIAL_VERTEX_EDGE_EXCLUSION.md) uniquely propagates moment-normalized forces and means from an owned external point through each pinned block, then chooses a strict radial-pair normal incompatible with every resulting fixed mean, including its endpoint.
- [x] [C7_MIRROR_VERTEX_EDGE_EXCLUSION.md](C7_MIRROR_VERTEX_EDGE_EXCLUSION.md) excludes the last mirror vertex edge: its two limiting normals force shared means that a fixed radial-anchor normal cannot both support. One strict cone failure gives a compatible open selection.
- [x] [C7_HIGH_CENTER_CONTACT_TYPES.md](C7_HIGH_CENTER_CONTACT_TYPES.md) gives the complete local contact cover for every center of radius at least3/2. Loaded high-center bodies own zero or one incident normal; a positively loaded two-owned body instead has center radius below23/16 and a90-degree force-polygon turn. All shared means and unloaded transmitters remain.
- [ ] Finish the **all-owned contact domain**: every edge has an actual side-axis owner, while zero-owner/two-owner bodies, two-circle-corner bodies, zero weights and all shared application means remain.
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

The five closed coarse cells are C1.3.b0, C1.4.b0, C1.3.b1, C1.3.b2 and C2.33.b0. Uniform restrictions apply across other cells without marking unresolved multi-load or completion cases closed.

## Equality and method controls

The known Q constructions forbid assuming a global common frame, fixed row structure, rigid central pose or a sharp cap. The conditional equality families remain useful but are not an unrestricted necessity theorem. See [SIGNED_MATCHED_EQUALITY_FAMILY.md](SIGNED_MATCHED_EQUALITY_FAMILY.md), [STRATIFIED_EQUALITY_FAMILY.md](STRATIFIED_EQUALITY_FAMILY.md), [NO_GLOBAL_ORTHOGONAL_FRAME.md](NO_GLOBAL_ORTHOGONAL_FRAME.md), [NONSTRATIFIED_PARALLEL_NINE.md](NONSTRATIFIED_PARALLEL_NINE.md), and [TWO_STACK_SHARP_EQUALITY_WITNESS.md](TWO_STACK_SHARP_EQUALITY_WITNESS.md).

The positive regular C7 below Q is a feasible smaller core with capacity one; it does not classify every stationary ring. [ADDITIVE_MEASURE_OBSTRUCTION.md](ADDITIVE_MEASURE_OBSTRUCTION.md) excludes an independent-square nonnegative additive measure of total mass below nine as the missing proof method. Center-only relaxations, finite parameter scans and counts of checked subgates do not prove the universal theorem.

## Verification and navigation

The new local proofs and whole-cell assembly have independent hand audits. The complete earlier prerequisite chain and standard-kernel verification remain separate open gates. **No Lean compilation or CI was run. Every new commit uses `[skip ci]`, and PR #11 remains draft while the unrestricted theorem is unfinished.**

- [ROADMAP.md](ROADMAP.md): concise ordered frontier.
- [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): full G0–G8 execution contracts and deeply nested exit gates.
- [G2_SUBGATES.md](G2_SUBGATES.md): live prerequisite and closure ledger.
- [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md): all 58 coarse cells individually ticked, five closed and 53 open.
- [TWO_LOAD_PROGRESS.md](TWO_LOAD_PROGRESS.md): append-only proof, audit, commit and exact-regression provenance; earlier checkpoint counts remain historical.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): all six tree profiles, now closed.
