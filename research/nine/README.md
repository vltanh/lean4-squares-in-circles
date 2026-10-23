# Nine unit squares in a circle — current research handoff

**Branch:** `research/nine-tablefree-hand` · **PR:** #11, draft.
**Target:** unrestricted sharp squared radius Q=1105/256 and all attaining packings. The construction attains Q; **the unrestricted matching lower bound and complete equality necessity remain OPEN**.

**Latest continuation, 2026-10-23:** a new hand theorem proves parallel contact forces in **every physical positive component with exactly two circle-loaded bodies**, including cyclic/branching components. It closes the diamond residual and the **entire four-body cyclic coarse cell C1.4.b0**. Two of the 58 coarse cyclic cells are now closed, 56 remain open. P.ALL, Y.ALL and larger two-loaded completion capacities are still open. Independent full audit, Lean compilation and CI are not claimed.

## Start here

- [ROADMAP.md](ROADMAP.md): concise current mathematical frontier.
- [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): full G0–G8 contracts, nested reciprocal/physical/layering subgates and exact open capacities.
- [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md): all 58 coarse cells individually ticked, two excluded and 56 open.
- [G2_SUBGATES.md](G2_SUBGATES.md): current G2 scope and source links.
- [TWO_LOAD_PROGRESS.md](TWO_LOAD_PROGRESS.md): new UTC proof commits, exact executed checks, corrected report provenance and negative controls.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): original six tree profiles and their surviving P/Y families.

Earlier PROGRESS_LEDGER.md, ORIGIN_POCKET_PROGRESS.md and QUADRANT_BLOCK_PROGRESS.md remain chronological records; their older open-cell counts are superseded by the current ledger.

## New general theorem: two-loaded reciprocal rigidity

[TWO_LOAD_RECIPROCAL_RIGIDITY.md](TWO_LOAD_RECIPROCAL_RIGIDITY.md), first commit 248202d, proves:

> If a physical force-and-torque-balanced positive component inside D_q, q>9/4, has exactly two circle-loaded bodies, then **all positive pair-contact normals are parallel**.

This is not an assumed frame normalization. The proof uses the actual planar contact-point incidence graph, correct cyclic order of square normal cones and junction tangent cones, and an exact reciprocal-force area identity. Adjacent circle atoms can be combined into an exterior port through the empty circle cap outside the loaded side. Two loaded bodies give two opposite exterior forces, whose force polygon has zero area. All finite force polygons have nonnegative area and the signed total cancels, forcing every polygon to be degenerate. An extreme-ray argument at multiple junctions recovers parallelism of original pair forces from their aggregates.

The argument does **not** assume the body-pair graph planar, nor equate the <=19-term planar translational certificate with the <=27-atom physical torque certificate. Independent review must check the cyclic-order/exterior-port/face-potential steps carefully.

### Whole-class radius and layer consequences

In the explicit window 79/40<=R<=sqrt(Q), two-loaded components have **q=17/4**. The endpoints are radial S squares at (+/-3/2,0), all internal squares are aligned in the two x=+/-1/2 layers, and every directed endpoint-to-endpoint path has exactly two internal bodies.

With the selected strictly exposing normal at point-only vertex/vertex contacts, the layer heights lie in (-1,1); each layer has at most two bodies. Thus there are **four, five or six bodies** in the component. All positive triangles and all two-loaded 7–9-body components are excluded.

**Limit:** a five-/six-body parallel component can have inner heights outside [-1/2,1/2], so it is not automatically a family-P skeleton. The exact six-cycle at heights +/-3/5 and a six-body theta graph are retained controls. Full physical completions of these layered cores remain open.

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

## Established tree reductions and remaining P/Y families

The previous tree theorem, in the declared lower-radius window, forces q=17/4 and exactly six origin-incidence profiles. TREE.12, TREE.03, TREE.04 and the strict-normal point-only TREE.02.P branch are excluded by complete physical capacity arguments. Every surviving tree configuration is covered by the exact reduction in [REMAINING_TREE_TWO_FAMILY_REDUCTION.md](REMAINING_TREE_TWO_FAMILY_REDUCTION.md):

**P.ALL, OPEN:** aligned centers (-3/2,0),(-1/2,tau1),(1/2,tau2),(3/2,0), tau_i in [-1/2,1/2], plus FIVE arbitrary unit squares in D_(17/4). The flat solid row is closed; all staggered parameters are not.

**Y.ALL, OPEN:** the whole side/vertex five-body fan with alpha in (0,1), theta in (0,pi/2), three radial terminals and FOUR arbitrary additional squares. The nonaligned core is feasible; the missing theorem is its completion capacity.

Do not assert separate two-per-side capacities for P or use only center/inscribed-disk relaxation: exact false-relaxation witnesses are already committed. The new two-load theorem does not solve P's completion and does not apply to Y's three-loaded core.

## Prior tools and their scope

- **Common-coordinate class:** COORDINATE_SEPARABLE_NINE_COMPLETE.md closes every packing separated pairwise by a common perpendicular frame, allowing individual rotations. That global-frame assumption is false for some equality packings.
- **Minimizer and stress:** SPARSE_MINIMIZER_STRESS.md, PLANAR_STRESS_CORE.md, ROTATION_STATIONARY_STRESS.md and PHYSICAL_CONTACT_STRESS.md provide necessary reductions, not q>=Q themselves.
- **Radial bridges:** RADIAL_BRIDGE_AND_LEAF_REDUCTION.md supplies radial bridge cuts and S/D loaded leaves. Cycle edges need not be radial.
- **Cap and row:** UNRESTRICTED_THREE_SQUARE_CAP.md and SOLID_FOUR_ROW_UNRESTRICTED_NINE.md give oblique-safe terminals and every-direction necessary strip occupancy. A solid row is not a staggered chain.
- **Quadrant:** QUADRANT_UNAVOIDABLE_POINT.md proves capacity one for a whole square in an origin quadrant of D_(17/4). General added squares can cross quadrant boundaries, so routing remains necessary.
- **Signed/grid stresses:** FOUR_ANCHOR_STRESS.md, SIGNED_MATCHED_CHAIN_STRESS.md and GRID_FOUR_CORNER_STRESS.md retain their exact terminal hypotheses.

Mandatory equality controls remain NO_GLOBAL_ORTHOGONAL_FRAME.md, NONSTRATIFIED_PARALLEL_NINE.md, TWO_STACK_SHARP_EQUALITY_WITNESS.md and the capless Q witness. They rule out the corresponding global normalizations.

## Exact remaining proof obligations

1. Prove whole-family P.ALL and Y.ALL capacities, or one invariant covering both.
2. Prove full completions for the five-/six-body parallel two-loaded survivors, and sharp inequalities for all remaining >=3-loaded cyclic cells or a uniform global replacement.
3. Retain the explicit 79/40 lower-window import from n=8 or prove it independently; do not advertise a standalone table-free dependency chain before this is resolved.
4. Assemble unrestricted optimality, all equality necessity/converse, independent whole-proof audit, standard-kernel Lean and public integration.

Commit whole quantified arguments and log their exact evidence. Two closed coarse cyclic cells are not a proof-completion percentage. The unrestricted theorem remains unfinished.