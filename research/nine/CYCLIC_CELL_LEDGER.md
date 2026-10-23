# n=9 CYCLIC — 58 exhaustive coarse cells, TWO whole cells closed

**Checkpoint:** 2026-10-23 two-load reciprocal continuation, read base a89802c. **Global sharp theorem remains OPEN.** The inventory is exhaustive at the **block-size / bridge-count level**, not an assertion that each cell is a single contact graph or has solved continuous geometry.

**NEW:** the entire four-body cell **C1.4.b0** is now excluded by the hand argument in FOUR_BODY_CYCLIC_CELL_CLOSED.md. The three-body cell C1.3.b0 was already excluded. Therefore **56 cells remain OPEN**. The new two-loaded-component rigidity also applies across the inventory, but does not close cells whose >=3-loaded possibilities remain unresolved.

P.ALL and Y.ALL remain OPEN separately. All results called CLOSED hand are mathematical manuscripts pending independent full audit and Lean verification. See TWO_LOAD_PROGRESS.md for current exact source and execution provenance.

## 1. Coverage theorem and exact graph conventions

Source: CYCLIC_BLOCK_INVENTORY.md, commit b3bac6e.
Choose one connected cyclic positive simple body-pair component with n<=9 bodies. If its maximal cyclic vertex-biconnected block sizes are k_1<=...<=k_m, k_i>=3, and it has b bridges, then

    n = 1 + b + sum(k_i-1) <= 9.

Every one of the **9-n other physical squares** remains in the cell's completion premise. The body-pair graph need not be planar; it is distinct from the planar physical contact-point incidence graph and from all zero-stress physical contacts.

- [x] **CY.B1–B2:** exact block-cut identity and complete list of 21 sorted profiles / 58 bridge-count cells.
- [x] **CY.LOAD.1–2:** no circle-free positive appendage attached through one body; each endblock has a loaded nonarticulation body.
- [x] **CY.LOAD.3:** in 79/40<=R<=sqrt(Q), a component's loaded subset cannot all physically touch pairwise.
- [x] **CY.ACUTE:** ACUTE_LOADED_CONTACT_GRAPH.md strengthens this to **connectedness of the loaded physical NONCONTACT graph**. It concerns actual contact, not only positive edges.
- [x] **CY.CHANNEL:** PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md proves normal-channel uniqueness, two-loaded simple-cycle quantization and full simple C4 exclusion.
- [x] **CY.TWOLOAD:** TWO_LOAD_RECIPROCAL_RIGIDITY.md proves every positive component with exactly two loaded bodies has all pair forces parallel. In the window it has q=17/4 and, for the strictly exposing point-contact certificate, 4–6 bodies in two aligned internal layers. Triangle-containing and 7–9-body two-loaded components are excluded.
- [x] **C1.3.b0:** selected triangle component excluded in the window.
- [x] **C1.4.b0:** all C4, diamond and K4 components excluded in the window; source FOUR_BODY_CYCLIC_CELL_CLOSED.md.
- [ ] **CY.SHARP:** 56 remaining complete geometric cells. The necessary restrictions and finite count do not prove their sharp completion bounds.

The lower-radius window remains an explicit imported n=8 prerequisite or a separate proof obligation. The coarse inventory itself needs no radius bound. Selecting one component never discards the other physical squares.

## 2. Individually ticked cells

Each OPEN row quantifies over all block adjacencies, articulation arrangements, contact points, independent angles, positive loads, zero-stress physical obstacles and the complete remaining-square packing.

| Cell | Cyclic block sizes | Bridges b | Component bodies n | Other physical squares 9-n | Sharp closure |
|---|---|---:|---:|---:|---|
| C1.3.b0 | 3 | 0 | 3 | 6 | [x] Excluded in explicit window |
| C1.3.b1 | 3 | 1 | 4 | 5 | [ ] OPEN |
| C1.3.b2 | 3 | 2 | 5 | 4 | [ ] OPEN |
| C1.3.b3 | 3 | 3 | 6 | 3 | [ ] OPEN |
| C1.3.b4 | 3 | 4 | 7 | 2 | [ ] OPEN |
| C1.3.b5 | 3 | 5 | 8 | 1 | [ ] OPEN |
| C1.3.b6 | 3 | 6 | 9 | 0 | [ ] OPEN |
| C1.4.b0 | 4 | 0 | 4 | 5 | [x] NEW all C4/diamond/K4 excluded |
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

## 3. Closed four-body cell: complete internal subgates

Source: FOUR_BODY_CYCLIC_CELL_CLOSED.md, commit 05e15a0.

- [x] **C1.4.b0.GRAPH:** the only biconnected simple four-body adjacency types are C4, K4-e and K4. This follows from edge counts 4/5/6 and minimum degree two, not a sampled drawing.
- [x] **C1.4.b0.C4:** two loaded bodies would force a six-body simple cycle; three or four loaded bodies violate connected loaded noncontact. Prior complete channel result.
- [x] **C1.4.b0.K4:** the loaded subset is a touching clique and is impossible.
- [x] **C1.4.b0.DIAMOND.LOADS:** only the two nonadjacent tips can be loaded; every other loaded subset violates the noncontact rule.
- [x] **C1.4.b0.DIAMOND.GEOM:** the new two-loaded reciprocal theorem forces all pair normals parallel. The diamond's positive triangles would be three pairwise touching, pairwise interior-disjoint positive-length intervals on one line, an impossibility.
- [x] **C1.4.b0.ALL:** every load/angle/contact realization is excluded independently of the other five physical squares.

## 4. Exact status of the new cross-cell two-loaded theorem

Source: TWO_LOAD_RECIPROCAL_RIGIDITY.md, first commit 248202d, clarified in 9fad28e.

- [x] **TL.RECIP:** plane force-polygon signed-area cancellation, with convex direction order and two external ports, forces all aggregate incidence forces parallel.
- [x] **TL.PHYS:** square normal/tangent cones, empty outer circle-chord caps and common-point extreme rays justify the reciprocal hypotheses and recover every original pair normal.
- [x] **TL.LAYER:** in the window, all two-loaded components have q=17/4 and aligned internal layers x=+/-1/2 between radial loaded endpoints x=+/-3/2.
- [x] **TL.COUNT:** strict point-only normal selection gives 4–6 bodies, excluding all two-loaded 7–9-body subfamilies. No positive triangle occurs.
- [ ] **TL.COMPLETE5–6:** the full physical completion capacity for the five-/six-body aligned layered survivors is not proved. Some heights are outside [-1/2,1/2]; they are not automatically the older P domain.
- [ ] Components with >=3 loaded bodies in the larger cells remain unresolved unless separately excluded.

This is a theorem spanning all cells, not a license to tick every cell containing a two-loaded subcase. A physical two-loaded six-body theta graph and a simple six-cycle are retained as exact controls.

## 5. Uniform contract for EACH open cell

- [ ] **C.GEOM:** cover every internal block adjacency and articulation arrangement, or prove an inequality directly over the full cell.
- [ ] **C.LOAD:** impose true force/torque, actual contact points, loaded endblocks, connected loaded noncontact and TL restrictions where applicable. Do not impose bridge radiality on cycle edges.
- [ ] **C.COMPLETE:** retain all 9-n remaining physical squares and all zero-weight contacts.
- [ ] **C.SHARP:** prove q>=Q for every allowed realization or exclude the whole selected component in the window.
- [ ] **C.EQUALITY:** preserve every q=Q degeneracy and free-square rotation when needed for global equality.

These are quantified contracts, not 56 independent angle-grid searches. Prefer one global physical/force invariant that closes many cells.

## 6. Exact regressions and current boundary

The old check_quadrant_blocks.py verifies finite block bookkeeping, not physical sharpness. The NEW check_two_load_reciprocals.py, source 0d4c958, was matched by Git blob and SHA-256 and run at **2026-10-23 19:32:40 UTC**, Python 3.13.5, exit 0. TWO_LOAD_RECIPROCAL_EXACT_CHECK.json records all four-body abstract graphs/load patterns and exact physical force-polygon examples, including the necessary nonparallel three-loaded control.

Finite examples do not prove the reciprocal geometry universally or replace an independent mathematical audit. All new general statements are hand manuscripts pending that audit; no Lean/CI is claimed.

- [x] Complete 58-cell coarse coverage.
- [x] C1.3.b0 and C1.4.b0 whole exclusions in the explicit window.
- [ ] Remaining 56 cells uniformly sharply bounded.
- [ ] P.ALL and Y.ALL capacities.
- [ ] Declared lower-window dependency, unrestricted G4/G5, full audit and standard-kernel Lean/integration.

Counts are not completion percentages. The remaining cells retain unequal, continuous geometric complexity.