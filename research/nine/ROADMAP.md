# n=9 — current roadmap: all trees and two-load completions closed

**Checkpoint:** 2026-10-24 complete P/Y continuation. **The unrestricted lower bound and complete equality classification remain OPEN.** P_ALL_COMPLETION.md and Y_ALL_COMPLETION.md now close the full P and Y families. Together with the exhaustive tree reduction, every selected positive tree component is excluded from a nine-square packing in the declared radius window. P also completes the five-/six-body reduction, excluding every selected positive component with exactly two circle-loaded bodies, including cyclic components. Every surviving component is cyclic and has 3–7 noncollinear circle resultants. The remaining geometric obligations are the general boundary-only C7 completion and mixed components containing a circle-clear body. Two coarse cells remain closed and 56 open. No Lean compilation or CI has been run.

The new P/Y, cap, and section arguments have received separate hand audits. A full independent audit of the entire prerequisite chain remains open. No Lean compilation, CI or proof-completion percentage is claimed.

## Boundary-contact continuation: one seven-cycle is the only boundary-only positive component

[CIRCLE_CONTACT_ANGULAR_ORDER.md](CIRCLE_CONTACT_ANGULAR_ORDER.md) proves a global geometric reduction throughout the declared radius window. Distinct circle-touching center directions are more than 36 degrees apart; touching pairs are less than 72 degrees apart and consecutive in angular order. Each circle-touching square has angular shadow strictly shorter than 60 degrees. Hence the complete physical circle-touching graph consists of paths, or is one seven-cycle. These statements include zero-multiplier contacts and bodies.

A contact between two circle-touching squares cannot have radial force line. Force and torque therefore exclude leaves in any positive stress component all of whose bodies touch the circle, even if some of their circle multipliers vanish. Such a component is exactly the seven-cycle and includes all physical circle-touching squares. Its two remaining completion squares are circle-clear.

The general seven-cycle completion capacity is still OPEN. Components containing a circle-clear body also remain OPEN. This is a whole-class reduction, not a closure of any additional coarse cell: the inventory remains two closed and 56 open.

[SEVEN_LOADED_RING_COUNTEREXAMPLE.md](SEVEN_LOADED_RING_COUNTEREXAMPLE.md) gives an exact positive seven-cycle with radius cos(pi/7)+1/(2 sin(pi/7)) below sqrt(17/4). Its own completion capacity is one, but its regularity is not assumed for arbitrary rings. [ADDITIVE_MEASURE_OBSTRUCTION.md](ADDITIVE_MEASURE_OBSTRUCTION.md) proves that any single nonnegative additive measure charging every contained square at least one has total mass at least 181/20>9, already at squared radius 17/4. Thus neither a component-only radius claim nor that independent-square weighting method can supply the missing proof.

## Canonical deep roadmap and source records

- [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): full G0–G8 contracts with new TL.R/TL.P/TL.G subsubgates and checked four-body adjacency cases.
- [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md): all 58 coarse rows, now two checked and 56 unchecked.
- [G2_SUBGATES.md](G2_SUBGATES.md): live mathematical scope and remaining completion contracts.
- [TWO_LOAD_PROGRESS.md](TWO_LOAD_PROGRESS.md): current UTC proof commits, pinned exact run, report correction and negative controls.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): all six tree profiles and their completed P/Y capacities.
- QUADRANT_BLOCK_PROGRESS.md, ORIGIN_POCKET_PROGRESS.md and PROGRESS_LEDGER.md retain earlier chronological checkpoints.

## Target and essential scope

Q=1105/256. An exact nine-square construction attains Q. The missing theorem is R^2>=Q for **every** nine independently oriented physical unit-square packing, with disjoint open interiors, followed by all equality configurations.

The whole common-coordinate-separable class is hand-proved. It is not unrestricted Packing: some exact Q packings have genuinely oblique-only separating pairs. The physical stress certificate is a necessary reduction at a minimizer, not by itself the sharp lower bound.

High-radius graph consequences use **79/40<=R<=sqrt(Q)**. LOWER_WINDOW_FROM_EIGHT.md now supplies the exact n=8 import and deletion argument. Its arithmetic-table dependencies remain explicit; a standalone table-free hand proof would replace that import. The new parallel-force theorem itself assumes only q>9/4.

## New theorem: exactly two loaded bodies force all contacts parallel

[TWO_LOAD_RECIPROCAL_RIGIDITY.md](TWO_LOAD_RECIPROCAL_RIGIDITY.md), initial commit 248202d, proves a global **load-cardinality** restriction, without assuming the component is a tree or a simple cycle.

In the true contact-point incidence graph, physical force directions follow the cyclic order around each square and each shared junction. Consecutive circle atoms on each loaded square can be combined into one exterior port through its empty outer chord cap. With exactly two loaded bodies, the exterior has two opposite resultant forces.

An exact dual face-potential construction gives reciprocal force polygons. Each finite polygon is weakly convex and has nonnegative signed area; all their signed areas cancel against the exterior polygon. The latter has two edges and zero area. Hence every finite polygon has zero area and all aggregated forces are parallel. A separate normal-cone extreme-ray argument recovers parallelism of every ORIGINAL pair force at multiple junctions.

This uses planarity of the physical **incidence** graph, not an unproved planar body-pair graph. It does not conflate the <=19 planar translational stress with the <=27 physical torque-balanced certificate.

### Exact research-window consequences

At 79/40<=R<=sqrt(Q), every such two-loaded component has:

- squared radius **17/4**;
- loaded side-normal endpoints centered at (-3/2,0),(3/2,0);
- all unloaded bodies axis-aligned in x=-1/2 or x=1/2 layers;
- exactly two internal bodies on every directed loaded-to-loaded path;
- **four, five or six bodies total** for the selected strictly exposing point-only normal convention.

Thus every triangle-containing two-loaded component and every two-loaded component with 7–9 bodies is excluded. This is a uniform theorem across the inventory, not another narrow angle/offset subclass.

**Whole completion progress:** [SIX_BODY_TWO_LOAD_COMPLETION.md](SIX_BODY_TWO_LOAD_COMPLETION.md), commit 52fec6f, proves that every six-body layered core has room for at most two arbitrary extra squares. [FIVE_BODY_TWO_LOAD_REDUCTION.md](FIVE_BODY_TWO_LOAD_REDUCTION.md), commit b46db3a, proves that every five-body core either contains a genuine P skeleton or has room for at most three extras. The five-body proof derives the singleton height bound from torque and handles the doubled column outside the P interval directly. P_ALL_COMPLETION.md now closes that last gate. Consequently no selected positive component with exactly two loaded bodies can occur in a nine-square packing in the declared window.

The new cap-sign, diagonal-center and half-disk pair lemmas allow arbitrary orientations of every added square. [CYCLIC_GLOBAL_CONTINUATION.md](CYCLIC_GLOBAL_CONTINUATION.md) also supplies a seven-body physical boundary-contact budget, excludes triple boundary-touching junctions, and proves distinct loaded resultant directions. Thus the remaining load class is 3–7 bodies with noncollinear resultants. These are necessary restrictions, not a sharp radius certificate for that class.

## Whole coarse cell C1.4.b0 closed

[FOUR_BODY_CYCLIC_CELL_CLOSED.md](FOUR_BODY_CYCLIC_CELL_CLOSED.md), commit 05e15a0, covers all biconnected simple four-body graphs:

| Exhaustive adjacency type | Full exclusion |
|---|---|
| C4 | Prior channel theorem excludes two loaded bodies; loaded-noncontact connectedness excludes three/four |
| K4 | Loaded subset is a touching clique, impossible |
| Diamond K4-e | Only two nonadjacent tips can be loaded. New parallelism makes its positive triangles impossible as one-dimensional touching intervals |

All load choices, individual square orientations, actual contact points and the five other physical squares are covered. The result excludes the whole selected component, so no unstressed completion is silently omitted.

The loaded-noncontact and simple-four-cycle results were already committed in ACUTE_LOADED_CONTACT_GRAPH.md (690f245) and PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md (a89802c). They are credited as prior inputs, not double-counted new proofs.

## Current ticked frontier

| Gate | State |
|---|---|
| G2.C common-coordinate-separable theorem | [x] CLOSED hand |
| Tree six-profile cover and P/Y normal forms | [x] CLOSED reductions |
| TREE.12, .03, .04 and point-only .02.P | [x] CLOSED completion bounds |
| CAP/QCAP all-angle tools and every-direction necessary counts | [x] CLOSED at stated scope |
| CY.BLOCK 58 coarse cells | [x] Exhaustive bookkeeping, not sharp geometry |
| CY.ACUTE / CY.CHANNEL | [x] Necessary load/contact rules and simple C4 exclusion |
| **CY.TWOLOAD** | [x] NEW all-component parallelism and window quantization |
| **C1.4.b0** | [x] NEW whole four-body cell excluded |
| C1.3.b0 | [x] Previously excluded |
| **P.ALL / Y.ALL** | [x] CLOSED full physical capacities |
| **TREE.ALL / TL.COMPLETE** | [x] CLOSED conditional on the explicit radius window |
| **TL.COMPLETE6** | [x] CLOSED whole family: at most two extras |
| **TL.REDUCE5 / TL.ALL_TO_P** | [x] CLOSED whole reduction to P.ALL |
| **CY.ARC / CY.INCIDENCE / CY.DIRECTIONS** | [x] CLOSED necessary restrictions |
| **Remaining 56 coarse cyclic cells** | [ ] OPEN uniform sharpness |
| G4/G5 unrestricted radius and all equality | [ ] OPEN/BLOCKED |
| G6 full independent audit | [ ] NOT COMPLETED |
| G7–G8 standard-kernel Lean and integration | [ ] NOT STARTED |

### P.ALL and Y.ALL are complete

P_ALL_COMPLETION.md excludes five arbitrary extras for the entire closed two-slider range. An upper triple either is canonical or has a small inner square; its vertical-axis section lies below 19/120. Both sliders then force every lower extra below -161/120<-3/sqrt(5), where all such squares share an interior point. The independent HALF.3 classification now supplies a shorter alternative proof.

Y_ALL_COMPLETION.md routes every whole extra square into two screened pockets. One has aperture at most 135 degrees and capacity one; the other has aperture strictly below 180 degrees and capacity two. Thus every nonaligned Y core permits at most three extras. TREE_AND_TWO_LOAD_COMPLETION.md closes every positive tree and every two-load component, retaining the declared radius-window condition.

### Newly closed analytic subgates

- [x] **WEDGE.2:** every screened pocket of aperture at most 135 degrees has capacity one. Full proof: WEDGE_135_CAPACITY_ONE.md.
- [x] **P.HIGH:** the sharp center-height threshold 3/sqrt(5) forces a common interior point. HIGH_CENTER_COMMON_POINT.md.
- [x] **P.CAP:** the quantitative terminal-cap inequality at section threshold 19/120 holds for every square orientation and every physical separator. TERMINAL_CAP_SECTION_EXCLUSION.md.
- [x] **HALF.3 / Y.STRICT:** every upper E/W triple is canonical; every strict terminal half-pocket has capacity two. HALF_POCKET_TRIPLE_RIGIDITY.md.
- [x] **P.ANNULAR / P.SECTION:** the complete same-side pair exclusion and upper section theorem supply the quantitative path proof.
- [x] **P.ALL / Y.ALL / TREE.ALL / TL.COMPLETE:** whole-family completion arguments, including all parameter boundaries and independent extra-square orientations.

## Actual exact regression evidence

[check_two_load_reciprocals.py](check_two_load_reciprocals.py), source **0d4c958**, was matched to its committed Git blob and SHA-256 before an actual run at **2026-10-23 19:32:40 UTC**, Python **3.13.5**, exit **0**. [TWO_LOAD_RECIPROCAL_EXACT_CHECK.json](TWO_LOAD_RECIPROCAL_EXACT_CHECK.json) records 12 exact radius comparisons, all 64 labelled four-body graphs/load subsets and five complete physical stress/reciprocal examples. An identical source rerun passed at **19:44:32 UTC**.

Checks include corners, all physical SAT pairs, genuine application points, force/torque balance, incidence rotation-system Euler characteristic, exact dual integration, convex finite polygons and signed-area cancellation.

Retained controls: a three-loaded nonparallel Y with reciprocal areas +4/3 and -4/3; an abstract wrong-direction-order vector graph with cancelling positive/negative areas; a six-cycle at inner heights +/-3/5 outside P; and a two-loaded six-body theta graph that is not a simple cycle.

These finite checks do not prove the general packing theorem, substitute for an independent audit or constitute Lean/CI verification.

## Next proof obligation

Handle the general C7 completion and the remaining cyclic mixed components with 3–7 noncollinear loaded bodies. Retain every unstressed body and every actual separator/corner/torque constraint. A coarse cell with an unresolved multi-load family stays unchecked. The two-load reciprocal argument cannot simply be extended: with three or more noncollinear resultants the exterior force polygon may have positive area.

All finished implications are committed and logged. PR #11 remains draft; the unrestricted proof remains unfinished.
