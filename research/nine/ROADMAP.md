# n=9 — ordered roadmap to the unrestricted hand proof

**PR:** #11, draft. **Reconciled source:** `697af9be7d3bd969e5a8bab70fedbf89253a7aa9`.  
**Updated:** October 23, 2026, America/Chicago.

**The unrestricted lower bound R^2>=1105/256 and complete equality classification remain OPEN.** The construction attains the claimed radius. The detailed proof tree, exact subgates and boundary cases are in [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md).

## Completed inputs

- [x] Exact physical semantics, compact minimizer and actual force/torque certificate.
- [x] Entire common-coordinate-separable class, with its conditional equality skeleton.
- [x] Full P and Y completion capacities; every positive tree excluded in the declared radius window.
- [x] Every exactly-two-loaded positive component excluded, including cyclic/branching cores.
- [x] One selected planar positive component; at most 27 scalar atoms; all circle-touching vertices on its exterior face.
- [x] At most7 physical circle contacts, >40-degree center separation, and the physical circle-contact angular-neighbor rule.
- [x] Boundary-only positive components are exactly C7; every extra lies inside the convex force-concurrence polygon.
- [x] Simple positive cycles have at most8 bodies.
- [x] Contact-ring interior capacities for k=3,4,5,6 are0,1,1,2; exterior pockets of touching boundary pairs are empty.
- [x] Entire S-leaf triangle-plus-leaf branch excluded; the D articulation has a complete two-pattern contact reduction.
- [x] Pre-stress generic physical-normal selection removes D vertex/vertex articulation contacts and retains all certificate properties.
- [x] Every physical boundary C7 has center diameter<3.
- [x] An open radius3/2 cover of ring centers implies one strict piercing point and completion capacity<=1.
- [x] Explicit n=8 import supplies79/40<=R; its current arithmetic-table dependencies are declared.

These are hand implications. The full prerequisite-chain audit and Lean verification are separate open work.

## Execute in this order

| Step | Gate | Complete scope | Exit condition |
| --- | --- | --- | --- |
| 1 | G3.M4.0 [x] | Every triangle-plus-leaf core, all load states, full S/D articulation cover and whole-square routing | CLOSED: TRIANGLE_LEAF_CORE_REDUCTION.md |
| 2a | G3.M4.D.PARALLEL | Both articulation reactions horizontal; every actual contact mean and circle mask | Exclude the whole selected core, or prove joint capacity<=4 |
| 2b | G3.M4.D.OBLIQUE | Opposite articulation corners in relative interiors of loaded-neighbor sides | Cover both owners of the B/C contact and prove whole-branch exclusion or capacity |
| 3 | G3.M4.S [x] | Aligned shared-side slider plus both tilted-vertex branches, with all endpoints | CLOSED: entire S core impossible |
| 4 | G3.M4.ALL | Assemble D and the completed S branch | D remains; only then close C1.3.b1 |
| Parallel | G3.B.CAP | Every positive boundary-only C7, arbitrary two extra squares | Prove capacity<=1 inside its actual free domain |
| 5 | G3.M5–M9 | All remaining mixed cyclic cells, in increasing component size | Sharp lower bound or full nine-square exclusion for each whole cell |
| 6 | G4 | All original nine-square packings | Universal R^2>=1105/256 |
| 7 | G5 | Every equality packing and every proposed parameter family | Exact necessary-and-sufficient classification |
| 8 | G6–G8 | Full audit, later formalization and integration | Verified advertised theorem; draft PR can then be finalized |

The first cell has four positive bodies and requires five extras. Its full core/routing reduction and its entire S-leaf branch are now closed; only D remains. Its inner triangle hole and the touching-boundary-pair exterior pocket are empty. The exact unresolved capacity is **at most four extras jointly in the two remaining articulation/leaf regions**. A separate bound of two per region is not assumed.

The complete S proof retains its entire aligned slider interval and both tilted formulas. For D, the bridge point lies strictly inside the articulation side. D_LEAF_ARTICULATION_CONTACT_LOCALIZATION.md proves the two remaining reactions point left; D_LEAF_GENERIC_CONTACT_SELECTION.md removes vertex/vertex articulation edges before the stress is chosen. This leaves the two full D branches in the table. The generic selection includes variable shared-side means and matched four-junction normals; it does not assume a special post-stress normal or fixed corner-weight split.

## Finite case coverage and controls

[CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md) lists all 58 coarse block/bridge cells. Two are closed and56 remain open. The deep roadmap refines each open cell by positive versus physical contact graphs, embeddings, boundary/load masks, actual contact features, junction identifications and completion regions. All continuous poses remain universally quantified. These data types are a finite-cover contract, not a claim that their geometry has been solved.

The C7 capacity routes are alternatives. Common **strict** origin piercing would suffice; closed origin containment alone would not. The proposed diameter route requires both a lower bound>=3 from two enclosed units and an upper bound<3 for the boundary centers; the upper bound<3 is now proved in BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md, while the enclosing-two lower bound remains open. A regularity route must cover two-owner/zero-owner transitions and nonconstant stationary solutions. No such assumption is imported.

A further C7 route now has a completed implication: CENTER_COVER_PIERCING.md proves capacity<=1 from an open radius3/2 disk containing all ring centers. The remaining cover theorem reduces to an acute supporting triple of the minimum enclosing center disk. Gap pattern(1,1,5) is excluded; patterns(1,2,4), (1,3,3), (2,2,3) remain. The center of the desired disk may be translated; it need not be the original circle center.

The S-leaf exclusion uses a closed 90-degree circle arc inaccessible to any neighbor of the articulation. The two touching triangle bodies have pairwise acute positive circle corners, whose sum must balance the leaf; this is impossible across the forbidden arc. The argument covers all aligned heights and tilted frames at once.

Known equality controls prohibit global common-frame, rigid-pose, stratification and sharp-cap assumptions. Actual squares, all zero-stress bodies and all zero-weight physical contacts remain throughout. A whole-cell closure is not inferred from a single example, graph drawing or numerical parameter cover.

## Evidence and workflow

[TWO_LOAD_PROGRESS.md](TWO_LOAD_PROGRESS.md) is the append-only proof/evidence record. [G2_SUBGATES.md](G2_SUBGATES.md) and [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md) give live scope; older ledgers preserve historical checkpoints.

Commit each complete proof and its exact roadmap changes through the GitHub connector. Use `[skip ci]`, keep the PR draft while T9 is unfinished, and run no Lean compilation or CI under the current instruction. Hand audits do not count as kernel verification. Counts of checked subgates are not progress percentages.
