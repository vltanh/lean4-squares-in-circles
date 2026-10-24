# n=9 CYCLIC — 58 exhaustive coarse cells, TWO whole cells closed

**Checkpoint:** 2026-10-23 completion continuation. **Global sharp theorem remains OPEN.** The inventory is exhaustive at the block-size / bridge-count level; each cell retains its full continuous contact geometry.

**Current closure:** C1.3.b0 and the entire four-body cell C1.4.b0 are excluded. Therefore **56 cells remain OPEN**. Across every cell, the full P capacity now completes the five-/six-body reductions and excludes every exactly-two-load nine-square completion. Necessary global contact/resultant restrictions also apply to all cells, but no unresolved multi-load cell is marked closed.

P.ALL and Y.ALL are now CLOSED hand, and their exhaustive reduction closes every positive tree in the declared window. All results called CLOSED hand are mathematical manuscripts pending independent full audit and Lean verification. See TWO_LOAD_PROGRESS.md for current exact source and execution provenance.

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
- [x] **TL.COMPLETE6:** SIX_BODY_TWO_LOAD_COMPLETION.md excludes every six-body core from a nine-square completion, allowing arbitrary extra orientations.
- [x] **TL.REDUCE5:** FIVE_BODY_TWO_LOAD_REDUCTION.md covers every five-body core: actual P containment, or at most three additional squares.
- [x] **TL.ALL_TO_P:** every nine-square packing with a two-loaded positive component in the window contains an actual P skeleton.
- [x] **P.ALL / TL.COMPLETE5 / TL.COMPLETE:** P_ALL_COMPLETION.md closes the whole P domain and consequently every two-loaded completion, including cyclic components.
- [ ] Components with >=3 loaded bodies in the larger cells remain unresolved unless separately excluded.

These theorems span all cells without closing any cell whose multi-load realizations remain unresolved. The physical six-body theta graph and simple six-cycle remain exact feasible cores; their completion to nine is now excluded.

### Global physical restrictions

[CYCLIC_GLOBAL_CONTINUATION.md](CYCLIC_GLOBAL_CONTINUATION.md) proves:

- [x] **CY.ARC:** at most seven physical squares touch the containing circle in the declared window; every such square occupies an inner-circle open arc longer than pi/4.
- [x] **CY.INCIDENCE:** for R>sqrt(2), no point belongs to three circle-touching squares.
- [x] **CY.DIRECTIONS:** distinct loaded bodies have distinct circle-resultant directions. A balanced collinear family has exactly two loaded bodies.

Together with TL.COMPLETE and TREE.ALL, every surviving selected component is cyclic and has 3–7 loaded bodies with noncollinear resultants. This does not supply its sharp metric inequality. In particular C4.3333.b0 remains open: a chain of four triangles can have six loaded nonarticulation bodies and three clear articulations.

### New whole boundary-graph reduction

[CIRCLE_CONTACT_ANGULAR_ORDER.md](CIRCLE_CONTACT_ANGULAR_ORDER.md) proves that the complete graph induced by physical circle-touching squares is a disjoint union of paths, or is one C7. Every such shadow is shorter than 60 degrees; contact edges respect angular order. A positive stress component whose bodies all touch the circle has no leaves by force/torque, and therefore is exactly that C7, including all physical circle-touching bodies.

- [x] **CY.BOUNDARY:** complete boundary graph and positive-component reduction, allowing zero circle multipliers on some circle-touching bodies.
- [ ] **CY.C7.COMPLETE:** the general seven-cycle with two arbitrary circle-clear extras.
- [ ] **CY.MIXED.COMPLETE:** all remaining components containing a circle-clear body.

The exact regular C7 below Q is feasible and has one completion slot; it does not close C1.7.b0, whose other graphs/load choices and nonregular seven-cycles remain covered by the open row. Likewise, excluding all-boundary five-/six-body components does not close their coarse cells with circle-clear bodies. **All 56 open rows remain unchecked.**

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
- [x] P.ALL and Y.ALL capacities; TREE.ALL and the entire two-load completion class in the declared window.
- [ ] Declared lower-window dependency, unrestricted G4/G5, full audit and standard-kernel Lean/integration.

Counts are not completion percentages. The remaining cells retain unequal, continuous geometric complexity.
