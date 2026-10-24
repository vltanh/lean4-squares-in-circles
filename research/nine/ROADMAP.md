# n=9 — ordered roadmap to the unrestricted hand proof

**PR:** #11, draft. **Reconciled source:** `604c93973e656f7219de9f6a2ec01780919ddb04`.  
**Updated:** October 23, 2026, America/Chicago.

**The unrestricted lower bound R^2>=1105/256 and complete equality classification remain OPEN.** The construction attains Q. The full execution tree, exact subgates and boundary cases are in [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md).

## New whole-cell closure

[TRIANGLE_LEAF_CELL_CLOSED.md](TRIANGLE_LEAF_CELL_CLOSED.md) closes **C1.3.b1 / G3.M4.ALL**. The full core reduction, entire S branch, entire selected oblique D branch and entire parallel-left D branch have complete proofs. Their simultaneous pre-stress normal selections retain the actual physical geometry, planar uncrossing, sparsity and unique component. Both D proofs and the parent assembly have independent hand audits.

The unique positive cyclic component now has **5–9 bodies** and **3–7 noncollinear circle-loaded resultants**. Every other physical square remains. The coarse inventory is **three whole cells closed and 55 open**; these counts are not progress percentages.

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
- [x] FOUR_CYCLE_LEAF_HOLE_EMPTY.md proves zero inner capacity for the whole C4-plus-leaf branch; all surviving C1.4.b1 completion is exterior.
- [x] C7 fixed-application and shared-side-block generic selection retains all application means and load masks. Free vertex edges require unique radial endpoints with both corner weights positive; radial runs have length at most two, and parallel radial pairs are impossible.
- [x] Every physical boundary C7 has center diameter below 3; two consecutive contacts span less than 3sqrt(3)/2 in the high-radius range.
- [x] An open radius-3/2 cover of enclosing-ring centers implies a common strict interior point and completion capacity at most one.
- [x] An exact physical C7 control disproves the unstressed center-cover claim; that control has no positive C7 stress.
- [x] The explicit n=8 import supplies R>=79/40; its inherited arithmetic-table dependencies are declared.

These are hand implications. The full prerequisite-chain audit and Lean verification remain separate open work.

## Execute the five-body frontier, with C7 in parallel

The identity m=1+sum(block_size-1)+bridges gives exactly four five-body cyclic cells. Each retains four arbitrary physical completion squares.

| Order | Whole gate | Exhaustive scope | Required exit |
| --- | --- | --- | --- |
| 1 | C1.3.b2 | Entire length-two arm CLOSED; two leaves at one articulation or at two distinct articulations remain | Finish both entire two-leaf layouts and assemble the whole cell |
| 2 | C1.4.b1 | C4 plus leaf; diamond plus leaf at a hub or tip | K4 excluded and all holes empty; prove the full core or joint exterior-completion bound |
| 3 | C1.5.b0 | C5 with three/four loads; house with three mask orbits; fan with three/four loads | Finish each complete graph/load family with every actual contact and four extras |
| 4 | C2.33.b0 | Two triangles sharing one articulation, four loaded tips and every zero-weight physical contact | Full joint capacity or core/radius theorem |
| Parallel | G3.B.CAP | Every positive boundary C7 with two arbitrary extra squares | Prove completion capacity at most one |
| 5 | G3.M6–M9 | Every remaining mixed cell in increasing component size | Sharp bound or full completion exclusion for each entire cell |
| 6 | G4 | All original nine-square packings | Universal R^2>=1105/256 |
| 7 | G5 | Every equality packing and every proposed parameter family | Necessary-and-sufficient unrestricted classification |
| 8 | G6–G8 | Full audit, later standard-kernel formalization and integration | Verified advertised theorem and completed PR |

Do not import S/D leaf geometry at a nonleaf bridge endpoint. Do not infer a common frame from parallel forces in a smaller subgraph. Every physical square, zero circle weight, shared-side application mean and contact-junction limit remains in the relevant full branch.

## Exact C7 frontier

[CENTER_COVER_PIERCING.md](CENTER_COVER_PIERCING.md) proves the strict-piercing implication from a radius-3/2 center cover. The desired cover may be translated; its center need not be the containing circle's origin. The diameter theorem excludes two-point supports of a failing minimum center disk. The two-contact span theorem excludes acute supporting triples with graph gaps (1,1,5) and (1,2,4).

The remaining covering targets are **positive-stress** supporting triples of types (1,3,3) and (2,2,3). [C7_CENTER_COVER_GEOMETRIC_OBSTRUCTION.md](C7_CENTER_COVER_GEOMETRIC_OBSTRUCTION.md) gives exact unstressed counterexamples of the latter type at Q and at strictly smaller radii, then proves that they cannot carry a positive C7 stress. Thus a general geometric center-cover theorem is a rejected normalization, not an unfinished premise to assume.

The simultaneous normal reductions are now complete in C7_FIXED_APPLICATION_GENERIC_SELECTION.md, C7_TWO_CIRCLE_CORNER_BLOCKS.md and C7_SHARED_SIDE_BLOCK_GENERIC_SELECTION.md. They leave two exhaustive contact domains: **all edges side-axis-owned**, retaining changes of ownership; or **some free vertex/vertex edge**, incident to shared-side blocks each pinned at a unique radial endpoint with both corner weights positive. The proof uses a collective virtual motion, so variable shared-side applications are not frozen. These are necessary structure restrictions, not a stationary classification or capacity bound.

A complete direct capacity proof or a fully exhaustive stationary classification may replace the cover route. Such a classification must include two-owner/zero-owner transitions, one/two-circle-corner masks, zero circle loads and nonconstant periodic solutions. Closed origin containment alone would not give strict piercing. Far-vertex spans do not imply the needed boundary-center diameter lower bound.

## Finite coverage, audit and evidence

[CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md) lists all 58 coarse cells. The deep roadmap refines each open cell by positive versus physical contact graphs, embeddings, boundary/load masks, actual contact features, junction identifications and completion regions. Continuous poses and weights stay universally quantified. Finite semantic labels are not a numerical parameter cover.

Known equality controls prohibit assumed global common-frame, rigid-pose, stratification and sharp-cap hypotheses. A whole-cell closure is not inferred from one example or one contact-owner pattern.

[TWO_LOAD_PROGRESS.md](TWO_LOAD_PROGRESS.md) is the append-only evidence record. Commit finished proofs and exact roadmap updates through the GitHub connector with `[skip ci]`. Keep the PR draft while T9 is unfinished. No Lean compilation or CI is authorized under the current instruction; hand audits are not kernel verification.
