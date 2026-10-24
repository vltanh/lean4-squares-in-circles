# Nine unit squares in a circle — current research handoff

**Branch:** `research/nine-tablefree-hand` · **PR:** #11, draft.
**Target:** unrestricted sharp squared radius Q=1105/256 and all attaining packings. The construction attains Q; **the unrestricted matching lower bound and complete equality necessity remain OPEN**.

**Latest continuation, 2026-10-24:** **The unrestricted lower bound and complete equality classification remain OPEN.** P_ALL_COMPLETION.md and Y_ALL_COMPLETION.md now close the full P and Y families. Together with the exhaustive tree reduction, every selected positive tree component is excluded from a nine-square packing in the declared radius window. P also completes the five-/six-body reduction, excluding every selected positive component with exactly two circle-loaded bodies, including cyclic components. The certificate can now be selected with exactly one positive component and a planar body graph; its 4–9 bodies form a cyclic component with 3–7 noncollinear circle resultants. Every other physical square has zero stress and remains a completion obstacle. The remaining geometric obligations are the general boundary-only C7 completion and mixed components containing a circle-clear body. Two coarse cells remain closed and 56 open. No Lean compilation or CI has been run.

## New global reduction: one planar positive component

[PHYSICAL_BODY_GRAPH_UNCROSSING.md](PHYSICAL_BODY_GRAPH_UNCROSSING.md) constructs a selected physical force-and-torque certificate whose **body-pair graph is planar**, with every physical circle-touching vertex on its exterior face. At a four-square junction, an exact positive force identity replaces crossing opposite-pair contacts by actual shared-side endpoint contacts. Conic thinning restores the at-most-27 scalar-atom bound without restoring a crossing. Strict point-contact normal choices are retained.

[UNIQUE_POSITIVE_COMPONENT.md](UNIQUE_POSITIVE_COMPONENT.md) proves that this selected certificate has **exactly one positive component**. Attach all positive circle atoms as boundary ports. Disjoint plane components have nonalternating ports; force balance gives no gap longer than a semicircle. A second component would have all its ports strictly inside one such gap, contradicting its own balance. The antipodal endpoint case and contact-only components are included.

- [x] **CY.PLANAR:** selected physical body-graph planarity, exterior-face circle contacts, and the original 27-atom bound; independently hand-audited.
- [x] **CY.UNIQUE:** all positive contact and circle atoms belong to one component; two separate hand audits.
- [x] **CY.ZERO:** all remaining physical bodies carry zero stress and remain part of the completion problem.
- [ ] **CY.SHARP:** prove the sharp capacity of the surviving unique cyclic component, including the general C7 and mixed cases.

In the declared radius window this component has 4–9 bodies and 3–7 noncollinear loaded resultants. The four-body triangle-plus-leaf cell remains open. Neither planarity of arbitrary stresses nor planarity of the full physical touching graph is claimed. The coarse count remains two closed and 56 open cells.

## New seven-cycle force geometry and completion localization

[C7_FORCE_POLYGON.md](C7_FORCE_POLYGON.md) proves that every positive boundary-only C7 has a convex polygon of contact-force concurrence points inside its seven actual squares. The polygon contains the origin, its edges follow the positive contact forces through the actual contact points, and loaded vertices are radial to their circle resultants. The proof covers both one- and two-circle-corner bodies and zero-load transmitters; regularity is not assumed.

[C7_COMPLETION_LOCALIZATION.md](C7_COMPLETION_LOCALIZATION.md) then proves that every additional square lies inside that convex polygon. Exterior pockets are empty: simultaneously dilating their extra-square centers away from the neighboring bodies' common contact preserves all separations until an impossible eighth circle contact occurs. The topological argument retains all shared-side contacts and two-circle-corner caps.

- [x] **CY.C7.POLYGON:** complete force-line concurrence and convexity theorem, independently hand-audited.
- [x] **CY.C7.LOCALIZE:** complete exterior-pocket exclusion and containment of every extra square in the concurrence polygon, with two separate hand audits.
- [ ] **CY.C7.COMPLETE:** exclude two disjoint unit squares inside that polygon while avoiding the actual seven boundary squares.

These implications do not close the general C7 capacity or change the coarse count of two closed and 56 open cells. Mixed cyclic components also remain open. No Lean compilation or CI has been run.

## New simple-cycle body bound

[SIMPLE_POSITIVE_CYCLE_BODY_BOUND.md](SIMPLE_POSITIVE_CYCLE_BODY_BOUND.md) proves that a selected positive component whose body-pair graph is a simple cycle has at most **eight bodies**. The proof first excludes crossing opposite-pair edges at a four-square junction, derives a Jordan cycle with the physical circle-touching bodies in circular center order, then charges more than 40 degrees to each cycle body through exact transmission-channel bounds. It retains circle-touching bodies with zero circle weight and arbitrary square orientations.

This closes the nine-body **simple-cycle** subfamily. It does not close the entire C1.9.b0 coarse cell, which also includes branching biconnected graphs, or completion of smaller cycles. The whole-cell count remains two closed and 56 open. The manuscript has received two separate hand audits; the complete prerequisite chain and Lean verification remain open.

## Boundary-contact continuation: one seven-cycle is the only boundary-only positive component

[CIRCLE_CONTACT_ANGULAR_ORDER.md](CIRCLE_CONTACT_ANGULAR_ORDER.md) proves a global geometric reduction throughout the declared radius window. Distinct circle-touching center directions are more than 36 degrees apart; touching pairs are less than 72 degrees apart and consecutive in angular order. Each circle-touching square has angular shadow strictly shorter than 60 degrees. Hence the complete physical circle-touching graph consists of paths, or is one seven-cycle. These statements include zero-multiplier contacts and bodies.

A contact between two circle-touching squares cannot have radial force line. Force and torque therefore exclude leaves in any positive stress component all of whose bodies touch the circle, even if some of their circle multipliers vanish. Such a component is exactly the seven-cycle and includes all physical circle-touching squares. Its two remaining completion squares are circle-clear.

[CENTERED_INNER_ARC.md](CENTERED_INNER_ARC.md) strengthens the center separation to strictly more than 40 degrees: every circle-touching square contains a closed centered 40-degree arc of the radius-5/4 circle in its open interior. Its proof is an exact shifted-cubic positivity argument.

The general seven-cycle completion capacity is still OPEN. Components containing a circle-clear body also remain OPEN. This is a whole-class reduction, not a closure of any additional coarse cell: the inventory remains two closed and 56 open.

[SEVEN_LOADED_RING_COUNTEREXAMPLE.md](SEVEN_LOADED_RING_COUNTEREXAMPLE.md) gives an exact positive seven-cycle with radius cos(pi/7)+1/(2 sin(pi/7)) below sqrt(17/4). Its own completion capacity is one, but its regularity is not assumed for arbitrary rings. [ADDITIVE_MEASURE_OBSTRUCTION.md](ADDITIVE_MEASURE_OBSTRUCTION.md) proves that any single nonnegative additive measure charging every contained square at least one has total mass at least 181/20>9, already at squared radius 17/4. Thus neither a component-only radius claim nor that independent-square weighting method can supply the missing proof.

## Start here

- [ROADMAP.md](ROADMAP.md): concise current mathematical frontier.
- [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): full G0–G8 contracts, nested reciprocal/physical/layering subgates and exact open capacities.
- [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md): all 58 coarse cells individually ticked, two excluded and 56 open.
- [G2_SUBGATES.md](G2_SUBGATES.md): current G2 scope and source links.
- [TWO_LOAD_PROGRESS.md](TWO_LOAD_PROGRESS.md): new UTC proof commits, exact executed checks, corrected report provenance and negative controls.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): all six tree profiles, now closed by the complete P/Y capacities.

Earlier PROGRESS_LEDGER.md, ORIGIN_POCKET_PROGRESS.md and QUADRANT_BLOCK_PROGRESS.md remain chronological records; their older open-cell counts are superseded by the current ledger.

## New general theorem: two-loaded reciprocal rigidity

[TWO_LOAD_RECIPROCAL_RIGIDITY.md](TWO_LOAD_RECIPROCAL_RIGIDITY.md), first commit 248202d, proves:

> If a physical force-and-torque-balanced positive component inside D_q, q>9/4, has exactly two circle-loaded bodies, then **all positive pair-contact normals are parallel**.

This is not an assumed frame normalization. The proof uses the actual planar contact-point incidence graph, correct cyclic order of square normal cones and junction tangent cones, and an exact reciprocal-force area identity. Adjacent circle atoms can be combined into an exterior port through the empty circle cap outside the loaded side. Two loaded bodies give two opposite exterior forces, whose force polygon has zero area. All finite force polygons have nonnegative area and the signed total cancels, forcing every polygon to be degenerate. An extreme-ray argument at multiple junctions recovers parallelism of original pair forces from their aggregates.

The argument does **not** assume the body-pair graph planar, nor equate the <=19-term planar translational certificate with the <=27-atom physical torque certificate. Independent review must check the cyclic-order/exterior-port/face-potential steps carefully.

### Whole-class radius and layer consequences

In the explicit window 79/40<=R<=sqrt(Q), two-loaded components have **q=17/4**. The endpoints are radial S squares at (+/-3/2,0), all internal squares are aligned in the two x=+/-1/2 layers, and every directed endpoint-to-endpoint path has exactly two internal bodies.

With the selected strictly exposing normal at point-only vertex/vertex contacts, the layer heights lie in (-1,1); each layer has at most two bodies. Thus there are **four, five or six bodies** in the component. All positive triangles and all two-loaded 7–9-body components are excluded.

**Completion update:** the genuinely staggered six-cycle and theta cores remain valid physical examples, but [SIX_BODY_TWO_LOAD_COMPLETION.md](SIX_BODY_TWO_LOAD_COMPLETION.md), commit 52fec6f, proves that no such six-body core can be completed to nine. [FIVE_BODY_TWO_LOAD_REDUCTION.md](FIVE_BODY_TWO_LOAD_REDUCTION.md), commit b46db3a, proves that every five-body completion either contains an actual P skeleton or has at most eight squares in total. The reduction retains heights outside the old P slider range rather than assuming them away.

## New completion and global geometry tools

- [DIAGONAL_CENTER_EXCLUSION.md](DIAGONAL_CENTER_EXCLUSION.md): a square avoiding the right radial terminal has center x<1; avoiding both terminals gives -1<x<1.
- [HALF_CAP_CENTER_SEPARATION.md](HALF_CAP_CENTER_SEPARATION.md): in the cap y>=1/2 of D_(17/4), center sign determines an unavoidable interior point (+/-3/7,5/4). At most two squares fit, with strictly opposite center signs.
- [HALF_DISK_CLOSE_CENTER_RIGIDITY.md](HALF_DISK_CLOSE_CENTER_RIGIDITY.md): two squares in a half-disk whose horizontal centers differ by at most 1/2 must be the aligned north terminal and an aligned lower neighbor.
- [CYCLIC_GLOBAL_CONTINUATION.md](CYCLIC_GLOBAL_CONTINUATION.md): seven physical circle contacts at most, no triple boundary-touching junction, and distinct circle-resultant directions. These necessary restrictions retain every remaining square and do not close the 56 remaining coarse cells.

## New entire coarse cell closure: C1.4.b0

[FOUR_BODY_CYCLIC_CELL_CLOSED.md](FOUR_BODY_CYCLIC_CELL_CLOSED.md), commit 05e15a0, covers every biconnected simple graph on four bodies:

- C4 is excluded by the preceding normal-channel and loaded-noncontact theorems.
- K4 is excluded because its loaded subset touches pairwise.
- For the diamond K4-e, connected loaded noncontact leaves only the two nonadjacent tips loaded. New two-load parallelism then contradicts its positive triangle: three positive-length projection intervals cannot all touch pairwise while their interiors are pairwise disjoint.

This completes the whole cell, including every load assignment, all individual orientations and the five other physical completion squares. The earlier isolated-triangle cell C1.3.b0 was already closed. **56 coarse cells remain open**, including those with three-or-more-loaded possibilities not addressed by the new theorem.

Prior input sources, not double-counted as new: [ACUTE_LOADED_CONTACT_GRAPH.md](ACUTE_LOADED_CONTACT_GRAPH.md), commit 690f245, and [PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md](PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md), commit a89802c.

## Exact executed regressions and essential controls

[check_two_load_reciprocals.py](check_two_load_reciprocals.py), source commit **0d4c958**, was matched to the committed Git blob and SHA-256 and actually run at **2026-10-23 19:32:40 UTC**, Python **3.13.5**, exit **0**. An identical-source rerun passed at **19:44:32 UTC**. [TWO_LOAD_RECIPROCAL_EXACT_CHECK.json](TWO_LOAD_RECIPROCAL_EXACT_CHECK.json) records the pinned run.

The standard-library exact checker covers 12 radius comparisons, all 64 labelled four-body graphs and loaded subsets, and five full physical examples. For each physical example it checks every corner and SAT pair, each actual shared application point, normalized load and exact force/torque balance, incidence rotation-system topology, dual face integration, convex force polygons and signed-area cancellation.

Negative controls are intentional:

1. A nonparallel three-loaded Y has finite reciprocal area +4/3 and exterior area -4/3, so the two-load hypothesis cannot be dropped.
2. An abstract balanced planar vector system with wrong cyclic force order has cancelling positive/negative finite areas; balance alone is insufficient.
3. A two-loaded six-cycle at inner heights +/-3/5 lies outside the P slider domain.
4. A six-body two-loaded theta graph has seven contacts and is not a simple cycle.
5. A five-body two-loaded cycle with a bridge exists; the core itself must not be declared infeasible instead of proving its nine-square completion capacity.

The report's initial manual transcription of the three-loaded areas was corrected at commit 4843058; the actual executed script outputs +4/3 and -4/3. Finite checks do not constitute the general theorem, independent full audit, Lean proof or CI.

## Complete P/Y capacities close every positive tree

The previous tree theorem, in the declared lower-radius window, forces q=17/4 and exactly six origin-incidence profiles. TREE.12, TREE.03, TREE.04 and the strict-normal point-only TREE.02.P branch are excluded by complete physical capacity arguments. Every surviving tree configuration is covered by the exact reduction in [REMAINING_TREE_TWO_FAMILY_REDUCTION.md](REMAINING_TREE_TWO_FAMILY_REDUCTION.md):

**P.ALL, CLOSED hand:** [P_ALL_COMPLETION.md](P_ALL_COMPLETION.md) excludes five arbitrary extra squares for every aligned path with centers (-3/2,0),(-1/2,tau1),(1/2,tau2),(3/2,0), throughout the closed slider square [-1/2,1/2]^2. The quantitative proof derives an inner vertical section below 19/120, forces both sliders down, and puts every opposite-side extra through one common interior point. It retains arbitrary square orientations and every physical separating axis.

**Y.ALL, CLOSED hand:** [Y_ALL_COMPLETION.md](Y_ALL_COMPLETION.md) proves at most three extras for the entire nonaligned five-body fan, alpha in (0,1), theta in (0,pi/2). The actual core screens three rays; the two possible extra-square pockets have capacities one and two. [TREE_AND_TWO_LOAD_COMPLETION.md](TREE_AND_TWO_LOAD_COMPLETION.md) assembles TREE.ALL and TL.COMPLETE, with the radius-window prerequisite explicit.

Do not assert separate two-per-side capacities for P or use only center/inscribed-disk relaxation: exact false-relaxation witnesses are already committed. The complete P capacity closes the whole two-load class; the separate Y proof handles the three-loaded fan.

## New complete pocket and section bounds

[WEDGE_135_CAPACITY_ONE.md](WEDGE_135_CAPACITY_ONE.md) proves that every screened origin pocket of aperture at most 135 degrees holds at most one extra square. The proof covers both square orientations and every separating-axis owner. Its analytic inputs are [OWNED_AXIS_TERMINAL_CAP_EXCLUSION.md](OWNED_AXIS_TERMINAL_CAP_EXCLUSION.md), [POSITIVE_NORMAL_CAP_FLOOR_EXCLUSION.md](POSITIVE_NORMAL_CAP_FLOOR_EXCLUSION.md), and [RIGHT_OWNED_DOWNWARD_SEPARATOR.md](RIGHT_OWNED_DOWNWARD_SEPARATOR.md). No parameter table or interval cover is used. This settles the smaller Y pocket. [HALF_POCKET_TRIPLE_RIGIDITY.md](HALF_POCKET_TRIPLE_RIGIDITY.md) proves that every upper E/W triple is the canonical aligned triple, and consequently every screened pocket of aperture strictly below 180 degrees has capacity two. These complete the larger Y pocket as well.

[HIGH_CENTER_COMMON_POINT.md](HIGH_CENTER_COMMON_POINT.md) proves the sharp common-point threshold 3/sqrt(5). [TERMINAL_CAP_SECTION_EXCLUSION.md](TERMINAL_CAP_SECTION_EXCLUSION.md) proves the quantitative single-square cap exclusion at 19/120 needed to couple the two sides of P. The open north-disk intersection lemmas and [ANNULAR_SAME_SIDE_PAIR_EXCLUSION.md](ANNULAR_SAME_SIDE_PAIR_EXCLUSION.md) complete the quantitative P proof. [P_HALF_POCKET_SECTION_PROOF.md](P_HALF_POCKET_SECTION_PROOF.md) independently proves upper capacity three. HALF.3 also supplies a shorter canonical-triple proof of P.

## Prior tools and their scope

- **Common-coordinate class:** COORDINATE_SEPARABLE_NINE_COMPLETE.md closes every packing separated pairwise by a common perpendicular frame, allowing individual rotations. That global-frame assumption is false for some equality packings.
- **Minimizer and stress:** SPARSE_MINIMIZER_STRESS.md, PLANAR_STRESS_CORE.md, ROTATION_STATIONARY_STRESS.md and PHYSICAL_CONTACT_STRESS.md provide necessary reductions, not q>=Q themselves.
- **Radial bridges:** RADIAL_BRIDGE_AND_LEAF_REDUCTION.md supplies radial bridge cuts and S/D loaded leaves. Cycle edges need not be radial.
- **Cap and row:** UNRESTRICTED_THREE_SQUARE_CAP.md and SOLID_FOUR_ROW_UNRESTRICTED_NINE.md give oblique-safe terminals and every-direction necessary strip occupancy. A solid row is not a staggered chain.
- **Quadrant:** QUADRANT_UNAVOIDABLE_POINT.md proves capacity one for a whole square in an origin quadrant of D_(17/4). General added squares can cross quadrant boundaries, so routing remains necessary.
- **Signed/grid stresses:** FOUR_ANCHOR_STRESS.md, SIGNED_MATCHED_CHAIN_STRESS.md and GRID_FOUR_CORNER_STRESS.md retain their exact terminal hypotheses.

Mandatory equality controls remain NO_GLOBAL_ORTHOGONAL_FRAME.md, NONSTRATIFIED_PARALLEL_NINE.md, TWO_STACK_SHARP_EQUALITY_WITNESS.md and the capless Q witness. They rule out the corresponding global normalizations.

## Exact remaining proof obligations

1. Exclude two arbitrary circle-clear completion squares for every admissible boundary-only seven-cycle; the regular example alone does not settle the full family.
2. Prove the sharp bound for cyclic mixed components with 3–7 loaded bodies, retaining all physical squares, or supply a uniform global replacement. P.ALL, Y.ALL, TREE.ALL and the entire two-load completion class are closed hand implications.
3. The lower-window import is assembled in [LOWER_WINDOW_FROM_EIGHT.md](LOWER_WINDOW_FROM_EIGHT.md), using the actual n=8 declarations and deletion of one square. It retains the n=8 arithmetic-table dependencies. Replace that import if an entirely standalone table-free bound is required.
4. Assemble unrestricted optimality, all equality necessity/converse, independent whole-proof audit, standard-kernel Lean and public integration.

Commit whole quantified arguments and log their exact evidence. Two closed coarse cyclic cells are not a proof-completion percentage. The unrestricted theorem remains unfinished.
