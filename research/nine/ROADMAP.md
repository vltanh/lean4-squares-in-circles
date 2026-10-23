# n=9 — current roadmap: universal two-load rigidity and whole four-body cyclic closure

**Checkpoint:** 2026-10-23 two-load reciprocal continuation. **The unrestricted n=9 proof is NOT finished.** A new hand theorem covers every physical positive component with exactly two circle-loaded bodies, forcing all pair forces parallel. It closes the diamond residual and therefore the **entire four-body coarse cyclic cell C1.4.b0**. Of the 58 coarse cells, two are now excluded and **56 remain open**. P.ALL, Y.ALL, larger layered-core completions, global equality and verification remain unresolved.

The new general arguments are hand manuscripts pending independent mathematical audit. No Lean compilation, CI or proof-completion percentage is claimed.

## Canonical deep roadmap and source records

- [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): full G0–G8 contracts with new TL.R/TL.P/TL.G subsubgates and checked four-body adjacency cases.
- [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md): all 58 coarse rows, now two checked and 56 unchecked.
- [G2_SUBGATES.md](G2_SUBGATES.md): live mathematical scope and remaining completion contracts.
- [TWO_LOAD_PROGRESS.md](TWO_LOAD_PROGRESS.md): current UTC proof commits, pinned exact run, report correction and negative controls.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): original tree profiles and P/Y survivor cover.
- QUADRANT_BLOCK_PROGRESS.md, ORIGIN_POCKET_PROGRESS.md and PROGRESS_LEDGER.md retain earlier chronological checkpoints.

## Target and essential scope

Q=1105/256. An exact nine-square construction attains Q. The missing theorem is R^2>=Q for **every** nine independently oriented physical unit-square packing, with disjoint open interiors, followed by all equality configurations.

The whole common-coordinate-separable class is hand-proved. It is not unrestricted Packing: some exact Q packings have genuinely oblique-only separating pairs. The physical stress certificate is a necessary reduction at a minimizer, not by itself the sharp lower bound.

High-radius graph consequences use **79/40<=R<=sqrt(Q)**. This lower window must be explicitly imported from the established n=8 result, with its proof dependencies, or proved independently for a standalone hand proof. The new parallel-force theorem itself assumes only q>9/4.

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

**Important remaining capacity:** five- and six-body parallel components really exist and can have inner heights outside [-1/2,1/2]. They are not automatically old family P. Their complete physical additions to nine remain open.

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
| **P.ALL / Y.ALL** | [ ] OPEN physical capacities |
| **Five/six-body two-loaded layered completion** | [ ] OPEN |
| **Remaining 56 coarse cyclic cells** | [ ] OPEN uniform sharpness |
| G4/G5 unrestricted radius and all equality | [ ] OPEN/BLOCKED |
| G6 full independent audit | [ ] NOT COMPLETED |
| G7–G8 standard-kernel Lean and integration | [ ] NOT STARTED |

### P.ALL and Y.ALL remain unchanged

P fixes aligned centers (-3/2,0),(-1/2,tau1),(1/2,tau2),(3/2,0), with tau_i in [-1/2,1/2], and requires exclusion of FIVE arbitrary additional squares in D_(17/4). Only flat-row capacity is finished.

Y fixes the full nonaligned side/vertex five-square fan with alpha in (0,1), theta in (0,pi/2), including its three radial terminals, and requires exclusion of FOUR arbitrary added squares. Its physical core exists. Neither new reciprocal rigidity nor quadrant capacity alone closes Y.

## Actual exact regression evidence

[check_two_load_reciprocals.py](check_two_load_reciprocals.py), source **0d4c958**, was matched to its committed Git blob and SHA-256 before an actual run at **2026-10-23 19:32:40 UTC**, Python **3.13.5**, exit **0**. [TWO_LOAD_RECIPROCAL_EXACT_CHECK.json](TWO_LOAD_RECIPROCAL_EXACT_CHECK.json) records 12 exact radius comparisons, all 64 labelled four-body graphs/load subsets and five complete physical stress/reciprocal examples. An identical source rerun passed at **19:44:32 UTC**.

Checks include corners, all physical SAT pairs, genuine application points, force/torque balance, incidence rotation-system Euler characteristic, exact dual integration, convex finite polygons and signed-area cancellation.

Retained controls: a three-loaded nonparallel Y with reciprocal areas +4/3 and -4/3; an abstract wrong-direction-order vector graph with cancelling positive/negative areas; a six-cycle at inner heights +/-3/5 outside P; and a two-loaded six-body theta graph that is not a simple cycle.

These finite checks do not prove the general packing theorem, substitute for an independent audit or constitute Lean/CI verification.

## Next proof obligation

Use the new invariant to close **whole physical completion families**, not only additional graph labels: larger two-loaded layered cores, P/Y, or >=3-loaded cyclic cells. Retain every unstressed body and every actual separator/corner constraint. A coarse cell with an unresolved >=3-loaded family remains unchecked even if its two-loaded subclass is eliminated.

All finished implications are committed and logged. PR #11 remains draft; the unrestricted proof remains unfinished.