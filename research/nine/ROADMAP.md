# n=9 — ordered roadmap to the unrestricted hand proof

**PR:** #11, draft. **Reconciled source:** `9a4573dd083f0e95ae270b760f849cfc880f2bd3`.  
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
- [x] Every physical boundary C7 has center diameter below 3; two consecutive contacts span less than 3sqrt(3)/2 in the high-radius range.
- [x] An open radius-3/2 cover of enclosing-ring centers implies a common strict interior point and completion capacity at most one.
- [x] An exact physical C7 control disproves the unstressed center-cover claim; that control has no positive C7 stress.
- [x] The explicit n=8 import supplies R>=79/40; its inherited arithmetic-table dependencies are declared.

These are hand implications. The full prerequisite-chain audit and Lean verification remain separate open work.

## Execute the five-body frontier, with C7 in parallel

The identity m=1+sum(block_size-1)+bridges gives exactly four five-body cyclic cells. Each retains four arbitrary physical completion squares.

| Order | Whole gate | Exhaustive scope | Required exit |
| --- | --- | --- | --- |
| 1 | C1.3.b2 | Triangle with a length-two bridge arm, two leaves at one articulation, or leaves at two distinct articulations | Sharp lower bound or full nine-square exclusion across all three layouts |
| 2 | C1.4.b1 | C4 plus leaf; diamond plus leaf at a hub or tip; K4 plus leaf | K4 branch closed; finish the other complete graph/attachment branches |
| 3 | C1.5.b0 | Every five-body biconnected selected graph, with every load and actual contact pattern | Full sharp bound or completion exclusion; retain equality survivors |
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

A complete direct capacity proof or a fully exhaustive stationary classification may replace the cover route. Such a classification must include two-owner/zero-owner transitions, one/two-circle-corner masks, zero circle loads and nonconstant periodic solutions. Closed origin containment alone would not give strict piercing. Far-vertex spans do not imply the needed boundary-center diameter lower bound.

## Finite coverage, audit and evidence

[CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md) lists all 58 coarse cells. The deep roadmap refines each open cell by positive versus physical contact graphs, embeddings, boundary/load masks, actual contact features, junction identifications and completion regions. Continuous poses and weights stay universally quantified. Finite semantic labels are not a numerical parameter cover.

Known equality controls prohibit assumed global common-frame, rigid-pose, stratification and sharp-cap hypotheses. A whole-cell closure is not inferred from one example or one contact-owner pattern.

[TWO_LOAD_PROGRESS.md](TWO_LOAD_PROGRESS.md) is the append-only evidence record. Commit finished proofs and exact roadmap updates through the GitHub connector with `[skip ci]`. Keep the PR draft while T9 is unfinished. No Lean compilation or CI is authorized under the current instruction; hand audits are not kernel verification.
