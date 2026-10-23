# n=9 CYCLIC — exhaustive coarse cells and exact sharp-closure ledger

**Checkpoint:** 2026-10-23 quadrant/block continuation, base 59d0c9.
**Global sharp theorem remains OPEN.** This ledger makes the cyclic bookkeeping finite and exhaustive at the **block-size / bridge-count level**. It does NOT claim that these cells are individual contact graphs, that their continuous geometries are solved, or that 58 is a small final geometric classification.

The two surviving tree completion families **P.ALL** and **Y.ALL** remain OPEN separately. The original six tree cases and their closed subcases are recorded in FINITE_TREE_CASE_LEDGER.md and REMAINING_TREE_TWO_FAMILY_REDUCTION.md. This file does not reopen or silently close those tree obligations.

## 1. Exact coverage theorem and conventions

Source: [CYCLIC_BLOCK_INVENTORY.md](CYCLIC_BLOCK_INVENTORY.md), commit b3bac6e.

Choose one connected positive body-pair component containing a cycle, with n<=9 physical square bodies. Let k_1<=...<=k_m be its maximal cyclic vertex-biconnected block sizes, each >=3, and b its number of bridges. The block-cut tree gives

    n = 1 + b + sum(k_i-1) <= 9.

All other **9-n physical squares** remain in that cell's completion premise. The graph is the simple positive body-pair graph, not the contact-point incidence graph or the set of all physical contacts. We do not assume this body graph planar.

- [x] **CY.B1:** block-cut identity proved by the elementary block-incidence tree argument.
- [x] **CY.B2:** 21 sorted block-size profiles and 58 bridge-count cells are the complete solutions of the integer budget.
- [x] **CY.LOAD.1:** an unloaded positive appendage with only one external attachment body is impossible by the summed force/support identity.
- [x] **CY.LOAD.2:** each endblock must contain a circle-loaded nonarticulation body.
- [x] **CY.LOAD.3:** in 79/40<=R<=sqrt(Q), the loaded body subset cannot be pairwise physically touching. Exact normalized circle-force balance and the center centroid give R^2<=625/162<(79/40)^2 otherwise.
- [x] **C1.3.b0:** a selected triangle component with no bridges is therefore excluded in that window.
- [ ] **CY.SHARP:** sharp bounds for the other 57 complete geometric cells. Neither the finite budget nor the load rules prove these bounds.

If a packing has several cyclic positive components, choose one and assign its unique sorted profile and b. The inventory is disjoint for that **selected component**, not a claim that the underlying packing can have only one possible stress or one possible component choice.

## 2. Individually ticked cells

For each OPEN row, its theorem quantifies over **all** block adjacencies, articulation arrangements, contact locations, orientations, loads, zero-weight physical obstacles and all remaining physical squares having that row's data. A proof for one graph or drawing does not close a row.

| Cell | Cyclic block sizes | Bridges b | Component bodies n | Other physical squares 9-n | Sharp closure |
|---|---|---:|---:|---:|---|
| C1.3.b0 | 3 | 0 | 3 | 6 | [x] Excluded in explicit window |
| C1.3.b1 | 3 | 1 | 4 | 5 | [ ] OPEN |
| C1.3.b2 | 3 | 2 | 5 | 4 | [ ] OPEN |
| C1.3.b3 | 3 | 3 | 6 | 3 | [ ] OPEN |
| C1.3.b4 | 3 | 4 | 7 | 2 | [ ] OPEN |
| C1.3.b5 | 3 | 5 | 8 | 1 | [ ] OPEN |
| C1.3.b6 | 3 | 6 | 9 | 0 | [ ] OPEN |
| C1.4.b0 | 4 | 0 | 4 | 5 | [ ] OPEN |
| C1.4.b1 | 4 | 1 | 5 | 4 | [ ] OPEN |
| C1.4.b2 | 4 | 2 | 6 | 3 | [ ] OPEN |
| C1.4.b3 | 4 | 3 | 7 | 2 | [ ] OPEN |
| C1.4.b4 | 4 | 4 | 8 | 1 | [ ] OPEN |
| C1.4.b5 | 4 | 5 | 9 | 0 | [ ] OPEN |
| C1.5.b0 | 5 | 0 | 5 | 4 | [ ] OPEN |
| C1.5.b1 | 5 | 1 | 6 | 3 | [ ] OPEN |
| C1.5.b2 | 5 | 2 | 7 | 2 | [ ] OPEN |
| C1.5.b3 | 5 | 3 | 8 | 1 | [ ] OPEN |
| C1.5.b4 | 5 | 4 | 9 | 0 | [ ] OPEN |
| C1.6.b0 | 6 | 0 | 6 | 3 | [ ] OPEN |
| C1.6.b1 | 6 | 1 | 7 | 2 | [ ] OPEN |
| C1.6.b2 | 6 | 2 | 8 | 1 | [ ] OPEN |
| C1.6.b3 | 6 | 3 | 9 | 0 | [ ] OPEN |
| C1.7.b0 | 7 | 0 | 7 | 2 | [ ] OPEN |
| C1.7.b1 | 7 | 1 | 8 | 1 | [ ] OPEN |
| C1.7.b2 | 7 | 2 | 9 | 0 | [ ] OPEN |
| C1.8.b0 | 8 | 0 | 8 | 1 | [ ] OPEN |
| C1.8.b1 | 8 | 1 | 9 | 0 | [ ] OPEN |
| C1.9.b0 | 9 | 0 | 9 | 0 | [ ] OPEN |
| C2.33.b0 | 3,3 | 0 | 5 | 4 | [ ] OPEN |
| C2.33.b1 | 3,3 | 1 | 6 | 3 | [ ] OPEN |
| C2.33.b2 | 3,3 | 2 | 7 | 2 | [ ] OPEN |
| C2.33.b3 | 3,3 | 3 | 8 | 1 | [ ] OPEN |
| C2.33.b4 | 3,3 | 4 | 9 | 0 | [ ] OPEN |
| C2.34.b0 | 3,4 | 0 | 6 | 3 | [ ] OPEN |
| C2.34.b1 | 3,4 | 1 | 7 | 2 | [ ] OPEN |
| C2.34.b2 | 3,4 | 2 | 8 | 1 | [ ] OPEN |
| C2.34.b3 | 3,4 | 3 | 9 | 0 | [ ] OPEN |
| C2.35.b0 | 3,5 | 0 | 7 | 2 | [ ] OPEN |
| C2.35.b1 | 3,5 | 1 | 8 | 1 | [ ] OPEN |
| C2.35.b2 | 3,5 | 2 | 9 | 0 | [ ] OPEN |
| C2.36.b0 | 3,6 | 0 | 8 | 1 | [ ] OPEN |
| C2.36.b1 | 3,6 | 1 | 9 | 0 | [ ] OPEN |
| C2.37.b0 | 3,7 | 0 | 9 | 0 | [ ] OPEN |
| C2.44.b0 | 4,4 | 0 | 7 | 2 | [ ] OPEN |
| C2.44.b1 | 4,4 | 1 | 8 | 1 | [ ] OPEN |
| C2.44.b2 | 4,4 | 2 | 9 | 0 | [ ] OPEN |
| C2.45.b0 | 4,5 | 0 | 8 | 1 | [ ] OPEN |
| C2.45.b1 | 4,5 | 1 | 9 | 0 | [ ] OPEN |
| C2.46.b0 | 4,6 | 0 | 9 | 0 | [ ] OPEN |
| C2.55.b0 | 5,5 | 0 | 9 | 0 | [ ] OPEN |
| C3.333.b0 | 3,3,3 | 0 | 7 | 2 | [ ] OPEN |
| C3.333.b1 | 3,3,3 | 1 | 8 | 1 | [ ] OPEN |
| C3.333.b2 | 3,3,3 | 2 | 9 | 0 | [ ] OPEN |
| C3.334.b0 | 3,3,4 | 0 | 8 | 1 | [ ] OPEN |
| C3.334.b1 | 3,3,4 | 1 | 9 | 0 | [ ] OPEN |
| C3.335.b0 | 3,3,5 | 0 | 9 | 0 | [ ] OPEN |
| C3.344.b0 | 3,4,4 | 0 | 9 | 0 | [ ] OPEN |
| C4.3333.b0 | 3,3,3,3 | 0 | 9 | 0 | [ ] OPEN |

## 3. Uniform cell contract and useful finite subgates

For each unchecked cell C:

- [ ] **C.GEOM:** either prove all its physically realizable geometries enter a finite explicit stress/pocket/completion description, or establish a direct inequality for the whole cell. The abstract block sizes alone do not determine such a description.
- [ ] **C.LOAD:** impose actual force/torque equilibrium, genuine contact points, loaded endblocks and nonclique loaded support, without importing tree radiality on nonbridge edges.
- [ ] **C.COMPLETE:** retain all 9-n remaining squares and their true corner/SAT constraints. A lower-radius core may exist even if nine-square completion is impossible.
- [ ] **C.SHARP:** prove q>=Q uniformly over every allowed orientation and completion, or exclude the entire selected-component cell within the stated window.
- [ ] **C.EQUALITY:** record all q=Q possibilities, including zero-weight free squares and boundary degeneracies, when required for the global equality theorem.

These are theorem contracts, not a requirement to do 57 separate brute-force searches. A global invariant or a theorem covering several profiles is preferable. In particular, the same proof may close an entire column of bridge counts or all loaded-endblock patterns at once.

## 4. Existing negative controls and dependency boundary

The exact record-radius oblique witness and signed matched-chain equality family must be retained. No theorem says arbitrary loaded bodies form a clique, no theorem gives a global common orthogonal separating frame, and a positive core of fewer than nine squares need not itself require radius sqrt(Q).

The endblock loaded-body rule is necessary but insufficient. An intermediate block need not have a private loaded body; deleting such blocks on that basis would be invalid. A triangle block with bridge attachments is not the excluded isolated-triangle cell.

The exact checker check_quadrant_blocks.py enumerates the 58 integer cells and exercises every cell with an abstract graph witness. It checks all simple graphs through five vertices and a deterministic larger sample. **This is finite regression of the block bookkeeping, not a physical square feasibility proof or a universal sharp inequality.** The analytic block-cut argument is the coverage proof.

## 5. Current completion boundary

- [x] Exhaustive coarse cyclic block/bridge inventory.
- [x] Loaded endblock and loaded-clique restrictions.
- [x] C1.3.b0 full exclusion in the explicit radius window.
- [ ] Remaining 57 cyclic cells sharply bounded.
- [ ] P.ALL and Y.ALL sharply bounded.
- [ ] Lower-window prerequisite made independent or explicitly imported.
- [ ] Unrestricted G4, all equality packings, independent audit, Lean kernel verification and public integration.

No percentage is attached to these counts. The cells have unequal difficulty and continuous geometric freedoms. A finite ledger prevents omitted bookkeeping cases; it does not certify that the remaining research is routine or close to finished.