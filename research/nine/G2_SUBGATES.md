# n=9 — live G2 ledger: P/Y capacities and 57 open coarse cyclic cells

**Checkpoint:** 2026-10-23 quadrant/block continuation, read base 59d0c9.
**Unrestricted q>=Q=1105/256 is NOT proved.** The whole coordinate-separable class is closed at hand level. Surviving positive-tree geometries reduce to P.ALL or Y.ALL; neither capacity is closed. Cyclic selected components now have a proved 58-cell coarse block/bridge cover, with only C1.3.b0 excluded. The other 57 sharp physical cell theorems remain open.

General results are analytic hand arguments pending independent mathematical audit and Lean verification. Finite exact regression is not a universal proof. Historical ledger versions remain in Git.

**Canonical contracts:** DEEP_GATED_ROADMAP.md. **Individual cases:** FINITE_TREE_CASE_LEDGER.md and CYCLIC_CELL_LEDGER.md. **Current UTC progress:** QUADRANT_BLOCK_PROGRESS.md. Preceding PROGRESS_LEDGER.md and ORIGIN_POCKET_PROGRESS.md remain historical records.

## 1. Ticked parent ledger

| Gate | Scope | Status |
|---|---|---|
| G2.C | All common-coordinate-separable nine-square packings, independent square frames allowed | [x] CLOSED hand |
| O3.0.2 | Compact minimizer, genuine contacts, normalized exact active stress | [x] CLOSED hand necessary reduction |
| O3.1a–g | Sparse planar translational support; separate angular/physical incidence certificates; radial bridge rules | [x] CLOSED hand necessary reductions |
| TREE.F1–F2 | Every positive tree in declared window has q0=17/4 and one of six origin-incidence profiles | [x] CLOSED hand exhaustive reduction |
| TREE.12, TREE.03, TREE.04 | Whole physical nine-square completion exclusions | [x] CLOSED hand |
| TREE.02.P | Point-only central contact, selected strictly exposing normal | [x] CLOSED hand full contact subtype |
| TREE.REMAINDER | Every surviving tree completion is in P or Y | [x] CLOSED hand normal form |
| **P.ALL** | Entire staggered path plus five arbitrary physical squares | [ ] **OPEN** |
| **Y.ALL** | Entire side/vertex fan plus four arbitrary physical squares | [ ] **OPEN** |
| QCAP.1–3 | Quadrant unavoidable point/capacity one and every-frame axis-crossing count at q<=17/4 | [x] NEW CLOSED hand tool/necessary condition |
| CY.BLOCK | Exact 21 block-size profiles / 58 bridge-count cells | [x] NEW CLOSED hand **coarse coverage**, not sharpness |
| CY.LOAD.1–3 | No unloaded one-body appendage; loaded endblocks; loaded subset not a touching clique in window | [x] NEW CLOSED hand necessary/exclusion rules |
| C1.3.b0 | Selected triangle component, no bridges, full completion retained | [x] NEW CLOSED hand exclusion in window |
| Other 57 cyclic cells | All graphs, loads, poses and 9-n physical completion squares | [ ] **OPEN sharp bounds** |
| O3.3.SHARP / O4 / O5 | All full realizations uniformly sharply covered | [ ] OPEN/BLOCKED |
| G4 / G5.U | Unrestricted lower bound and all equality packings | [ ] OPEN/BLOCKED |
| G6–G8 | Independent full audit, standard-kernel Lean and public integration | [ ] NOT COMPLETED |

**No false counting:** one cyclic cell excluded is not 1/58 of a proof; the remaining cells have unequal geometric complexity. An exhaustive coarse partition is not a small sharp terminal classification.

## 2. Earlier complete coordinate branch remains closed

COORDINATE_SEPARABLE_NINE_COMPLETE.md combines the rank-product extraction, four-chain shadow, complete zigzag exclusion, signed 4+3 stress, crossed-four-chains-plus-ninth exclusion and elementary five-element matching. Both (4,1) and (3,2) two-stack complements are settled inside that class. Do not reopen them for narrower angle/height inequalities.

The exact no-global-frame equality witness forbids applying this theorem from unrestricted physical nonoverlap alone.

## 3. Existing unrestricted stress input — preserve representation distinctions

SPARSE_MINIMIZER_STRESS.md proves compact attainment and exact normalized nonnegative actual-contact stress at a hypothetical subcritical minimizer. The fixed-frame certificate has <=19 terms and attains the unknown q0.

PLANAR_STRESS_CORE.md produces an outer-loaded planar **translational support**. ROTATION_STATIONARY_STRESS.md supplies a separate angular certificate. PHYSICAL_CONTACT_STRESS.md refines this to true shared application points with force/torque balance, <=27 atoms and a planar **contact-point incidence graph**. The corresponding body-pair graph need not be planar and is not silently identified with the 19-term graph.

RADIAL_BRIDGE_AND_LEAF_REDUCTION.md makes positive body-pair bridges radial and covered by <=4 central circle-clear bodies. Off-origin point-only vertex contacts use a chosen strict nonradial normal and cannot be bridges. Nonbridge forces are not forced radial.

The tree-radius and loaded-clique exclusions have the explicit premise **79/40<=R<=sqrt(Q)**. Import the prior n=8 lower bound explicitly or prove the coarse lower window separately; it is not supplied by the new capacity tools.

## 4. Tree scope: exhaustive reductions, unchanged P/Y parents

### TREE.F1–F2 [CLOSED hand]

TREE_BODY_LOCALIZATION.md localizes every unloaded tree body, gives radial S/D geometry to every loaded body and reduces origin-avoiding unloaded bodies to one-step transmitters. TREE_RADIUS_QUANTIZATION.md excludes origin-interior roots, forces q0=17/4 and proves exactly six origin-incidence profiles through 2s+v<=4 and s+v>=2.

### Full completion cases

- [x] **TREE.12:** a cardinal terminal cage leaves total capacity <=8; arbitrary extra rotations retained.
- [x] **TREE.04:** the central solid 2x2 block permits only four outer squares, total<=8.
- [x] **TREE.03:** three vertex-origin cones leave annular gaps totaling pi/2; required angular separation excludes six extras, total<=8.
- [x] **TREE.02.P:** the selected strict point-contact normal forces four terminals; exact screened-pocket capacities exclude completion to nine.
- [x] **TREE.02.E / TREE.11 / TREE.20 routing:** REMAINING_TREE_TWO_FAMILY_REDUCTION.md proves all survivors are P or Y, with angular and slider boundary cases retained.

### P.ALL [OPEN]

Four aligned roots have centers (-3/2,0),(-1/2,tau1),(1/2,tau2),(3/2,0), |tau_i|<=1/2, in D_(17/4). Prove that no FIVE arbitrary additional unit squares fit.

- [x] Flat row excluded by the earlier solid-row theorem.
- [x] Exact three-above-staggered-row example rejects an independent two-per-side bound.
- [x] NEW exact five-center relaxation satisfies radius<=3/2, pairwise distance>=1 and inscribed-disk clearance from every root rectangle. Hence those center constraints alone cannot prove the theorem.
- [ ] Retain full square orientation/corner/SAT geometry and prove a whole-range coupled capacity bound. QCAP needs a derived whole-square quadrant placement, not merely center signs.

### Y.ALL [OPEN]

The five-body fan comprises H=[-alpha,1-alpha]x[0,1], K=[0,u]+[0,v] with u=(cos(theta),-sin(theta)), v=(-sin(theta),-cos(theta)), and radial terminals S(north),S(u),S(v), for alpha in (0,1), theta in (0,pi/2). Prove no FOUR arbitrary extra squares fit in D_(17/4).

- [x] Exact normal form and force ratios sin(theta),cos(theta), with angular endpoints in P.
- [x] A nonaligned five-body stress really exists; no false core exclusion.
- [ ] Whole-family physical region routing and capacity, including all oblique separators. Neither existing screened sectors nor QCAP yet supplies the needed global implication.

## 5. NEW QCAP [CLOSED hand tool; applicability open]

Source: QUADRANT_UNAVOIDABLE_POINT.md, commit c02fa61.

- [x] Every arbitrary unit square wholly in the first quadrant of D_(17/4) contains (1,1). The point is strictly interior for tilted squares; aligned boundary squares contain the common inward perturbation (1,1)-epsilon*(1,1).
- [x] Therefore one origin-centered closed quadrant holds at most one physical square, without radial terminal obstacles.
- [x] Every hypothetical nine-square packing in that disk has at least five squares whose open interiors meet one of the two axes, for every perpendicular frame.
- [ ] Route all P/Y extras through suitable whole-square cone/crossing classes with a complete capacity inequality. A square may cross both proposed region boundaries; assigning it by center quadrant is invalid.
- [ ] Derive an unrestricted sharp invariant from QCAP and CAP.3 or from contacts. These necessary conditions alone are not contradictory.

## 6. NEW cyclic coarse inventory and load rules

Sources: CYCLIC_BLOCK_INVENTORY.md and CYCLIC_CELL_LEDGER.md.

### CY.B1–B4 [CLOSED coverage]

For a selected connected cyclic simple positive component with cyclic block sizes k_i>=3 and b bridges,

    n=1+b+sum(k_i-1)<=9.

The elementary block-cut tree proof yields exactly **21 sorted profiles and 58 bridge-count cells**. Every cell retains all 9-n other physical squares. Distinct square orientations, contacts, circle-atom locations and within-block graph adjacencies remain continuous/combinatorial variables, not implicitly resolved by this identity.

### CY.LOAD.1–3 [CLOSED necessary/exclusion]

- [x] Summing unloaded force equations dotted with c_i-c_b excludes an unloaded positive subgraph attached only through body b.
- [x] Each endblock has a circle-loaded nonarticulation body. Intermediate blocks with multiple articulations are not covered by that private-load rule.
- [x] If every pair of loaded bodies physically touches, their center centroid and normalized circle-force balance imply R^2<=625/162<(79/40)^2. Thus this loaded-clique pattern is excluded in the declared window.

### CY sharp cells

- [x] **C1.3.b0:** a selected triangle component without bridges has a pairwise-touching loaded subset and is excluded, independent of all six extra squares.
- [ ] **C1.3.b1–b6:** still open; loads can lie in attached bodies.
- [ ] **Other single-block profiles (4)–(9), all admissible b:** open.
- [ ] **All two-, three- and four-cyclic-block profiles:** open.

The 58 individual checkboxes and 57 remaining full-cell contracts are in CYCLIC_CELL_LEDGER.md. No raw graph or angle enumeration is treated as the sharp proof. A universal theorem closing many cells simultaneously is preferred.

## 7. Global closure contracts [OPEN]

- [x] Coarse TREE/CYCLIC alternatives are exhaustive for the selected stress.
- [x] Tree survivors are P/Y; cyclic survivors enter the exact coarse ledger.
- [ ] **O3.3.SHARP:** prove the actual physical completion inequalities for P.ALL, Y.ALL and every unchecked cyclic cell, or one global replacement theorem.
- [ ] **O4:** uniform orientation/equality bounds using all nine physical squares. Existence of stress weights certifies q0, not q0>=Q.
- [ ] **O5 / G2.X / G4:** include the lower-window dependency and combine minimizer reduction, sharpness and attainment.
- [ ] **G5.U:** all unrestricted equality packings, not just the signed/stratified families.
- [ ] **G6–G8:** independent full audit, standard-kernel Lean and final integration.

## 8. Exact execution and progress discipline

check_quadrant_blocks.py at commit fed5a888 was matched to Git blob fdb7d5ef123b8018601c3661b5451c4346672ba5 and SHA-256 before execution. QUADRANT_BLOCK_EXACT_CHECK.json records a PASS under Python 3.13.5 at 2026-10-23 16:27:18–16:27:19 UTC, exit 0: 104 identity checks, 2,254 admissible rational quadrant squares, 1,772 finite graph checks spanning every coarse cell, and exact relaxation/angle negative controls.

These finite checks are not the symbolic proofs, physical graph feasibility, independent audit or Lean verification. No CI ran. QUADRANT_BLOCK_PROGRESS.md records source times and theorem scope.

Tick only the full stated implication. Do not attach a completion percentage to the number of cells or lemmas. A new conditional tool cannot close P/Y or a cyclic parent until its hypotheses are derived throughout that entire physical completion family. The unrestricted proof remains unfinished.