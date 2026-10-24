# n=9 — finite tree-case ledger: all six profiles closed

**Checkpoint:** 2026-10-24, complete P/Y continuation. **Global theorem remains OPEN.**
All six original tree profiles now have full physical completion exclusions. P_ALL_COMPLETION.md and Y_ALL_COMPLETION.md close the two remaining continuous families, with independent extra-square orientations and all boundaries retained. The separate cyclic branch remains open. The conditional tree assembly keeps 79/40<=R<=sqrt(Q) explicit; LOWER_WINDOW_FROM_EIGHT.md now supplies its explicit n=8 import.

## 1. Exact outer split and dependencies

At a hypothetical unrestricted minimizing packing, choose the physical force-and-torque certificate from PHYSICAL_CONTACT_STRESS.md, with a **strictly exposing common normal at every point-only vertex/vertex contact**, and the earlier nonradial choice at off-origin contacts of that type.

In the declared window 79/40<=R<=sqrt(1105)/16:

1. If some positive body-pair component is a **tree**, select one and apply TREE.F1/F2 and this ledger. Keep **all nine physical squares**, including other components and zero-weight bodies, in every completion problem.
2. If every positive component has a **cycle**, the separate CYCLIC branch applies and remains open. A tree argument does not make nonbridge forces radial.

LOWER_WINDOW_FROM_EIGHT.md explicitly imports the established n=8 theorem and proves the deletion implication. Its arithmetic-table dependencies remain; a fully independent table-free hand proof would replace that import. The tree capacities do not themselves establish the coarse lower bound.

## 2. Completed universal tree reductions

- [x] **TREE.F1** Every unloaded tree body is central and circle-clear; loaded bodies have radial S/D geometry even at degree two; every origin-avoiding unloaded body is a one-step side-normal transmitter to an S terminal. Source: TREE_BODY_LOCALIZATION.md.
- [x] **TREE.F2.I** Origin-interior roots are excluded by an exhaustive short-arm side/vertex analysis and the prior star theorem.
- [x] **TREE.F2.R** Every positive tree in the window has **R^2=17/4**. All unloaded bodies contain zero on their boundaries; all loaded bodies are radial S terminals centered at (3/2)e, inward contact e.
- [x] **TREE.F2.C** If s and v count side-interior-origin and vertex-origin unloaded component bodies, disjoint tangent cones give 2s+v<=4, while star exclusion gives s+v>=2. Exactly six incidence profiles result. Source: TREE_RADIUS_QUANTIZATION.md.

## 3. All six original cases, with exact updated status

| ID | (s,v) | Full physical family | Completion status |
|---|---|---|---|
| TREE.20 | (2,0) | Opposed side-origin roots; all interior slider positions in the four-square path | [x] CLOSED by **P.ALL** |
| TREE.11 | (1,1) | Side-origin plus vertex-origin root, all compatible angles and side offsets | [x] CLOSED by **Y.ALL**, with aligned endpoints covered by P |
| TREE.12 | (1,2) | A side root and two vertex roots fill the origin angle | [x] CLOSED hand: cardinal cage, at most eight total squares |
| TREE.02 | (0,2) | Two vertex-origin roots | [x] CLOSED: point-only **TREE.02.P**, and shared-edge **TREE.02.E** by the full P capacity |
| TREE.03 | (0,3) | Three vertex-origin roots, all continuous cone-gap choices | [x] **NEW CLOSED hand:** angular annulus capacity, at most eight total squares |
| TREE.04 | (0,4) | Four origin quadrants form a central 2x2 block | [x] CLOSED hand: central-block capacity, at most eight total squares |

Slider endpoints migrate into the appropriate vertex rows; no boundary is discarded. Profiles count bodies of the selected stressed component only. All unstressed squares remain in the physical completion premise.

## 4. Full-case closure sources

### TREE.12 and TREE.04 [previously closed]

[TREE_FINITE_COMPLETIONS.md](TREE_FINITE_COMPLETIONS.md) proves the cardinal-cage and central-block capacity theorems at q=17/4. Both allow arbitrary orientations and oblique separators of the added squares. The capacity bounds concern the **whole physical packing**, not merely the stressed core.

### TREE.03 [new whole-profile closure]

[THREE_VERTEX_ORIGIN_CAPACITY.md](THREE_VERTEX_ORIGIN_CAPACITY.md) proves that any three origin-vertex unit squares in D_(17/4) permit at most five additional physical squares. Their right-angle cones leave three gaps totaling pi/2; every additional center lies in those gaps and in the annulus [1/sqrt(2),3/2]. Distinct center angles within a gap must differ by more than pi/6. Six extra centers would consume more than the available angle.

No stress, shared frame or restriction on extra-square orientations is assumed by this capacity theorem. The eight-square cross is a sharp attainment witness.

### TREE.02.P [new whole contact-type closure]

[TREE02_POINT_CONTACT_COMPLETION.md](TREE02_POINT_CONTACT_COMPLETION.md) gives the finite split **point-only / shared-edge** of the two central roots. In the point-only case, the selected strict common normal forces both side loads on both roots, hence four distinct S terminals. The radial screens trap every added square in one of two complementary gaps.

[RADIAL_SECTOR_POCKET_CAPACITY.md](RADIAL_SECTOR_POCKET_CAPACITY.md) proves: acute screened pockets hold no square; right-angle pockets hold a unique one; pockets up to angle 2 arctan(2) hold at most two. The terminal nonoverlap bound makes these ranges exhaustive for the point-contact core. At most two squares can be added to its six-body skeleton, giving <=8 total.

**Strict-normal distinction:** a non-strict zero-point normal can support a different arbitrary physical equilibrium. The opposite-slider path negative control is retained; the theorem uses the specific strictly exposing contact certificate, not every possible stress.

## 5. The two remaining master families now have complete capacities

Source: [REMAINING_TREE_TWO_FAMILY_REDUCTION.md](REMAINING_TREE_TWO_FAMILY_REDUCTION.md).

### P.ALL — staggered four-square path [CLOSED hand]

Four fixed axis-aligned centers:

    (-3/2,0), (-1/2,tau_1), (1/2,tau_2), (3/2,0),
    -1/2 <= tau_1,tau_2 <= 1/2.

**Proved theorem:** P_ALL_COMPLETION.md excludes FIVE additional arbitrarily oriented unit squares throughout this entire closed parameter square. This includes TREE.20, shared-edge TREE.02.E (tau_1=tau_2=+/-1/2), and aligned TREE.11 limits. Its quantitative proof couples the two sides through the lower vertical-axis section of an inner square and the sharp high-center common-point theorem.

Do not use an independent two-per-side capacity: three squares can fit above a staggered path, as recorded in TREE_FINITE_VALIDATION.md.

### Y.ALL — nonaligned side-plus-vertex fan [CLOSED hand]

For 0<alpha<1 and 0<theta<pi/2, set

    H=[-alpha,1-alpha] x [0,1],
    u=(cos(theta),-sin(theta)), v=(-sin(theta),-cos(theta)),
    K={a u+b v:0<=a,b<=1}.

The five-body skeleton is H,K,S((0,1)),S(u),S(v), where S(e) is the radial unit square centered at (3/2)e. Exact equilibrium forces the two downward terminal weights in ratios sin(theta),cos(theta); there is no other TREE.11 positive core type. At theta=0 or pi/2, the skeleton reduces to an aligned member of P.

**Proved theorem:** Y_ALL_COMPLETION.md excludes FOUR additional arbitrary physical unit squares throughout this entire alpha/theta domain. Three actual ray screens leave two pockets with capacities one and two. HALF_POCKET_TRIPLE_RIGIDITY.md supplies the strict-half-pocket bound. The nonaligned core remains feasible; its completion is excluded.

**Coverage:** every formerly surviving candidate in the six original tree profiles contains P or Y. Both full capacities are now proved, so TREE.ALL is CLOSED hand in the declared radius window. TREE_AND_TWO_LOAD_COMPLETION.md states the exact corollary and retains every remaining physical square.

## 6. UTC source/progress history

| GitHub UTC | Commit | Closed implication |
|---|---|---|
| 2026-10-23 12:56:07 | `4f8144d` | TREE.F1 all-body localization |
| 2026-10-23 12:58:52 | `4007bfc` | TREE.F2 all-tree radius quantization and six-case cover |
| 2026-10-23 13:05:27 | `5acabe7` | Entire TREE.12 and TREE.04 completion cases |
| 2026-10-23 13:51:19 | `463afde` | Entire TREE.03 completion case |
| 2026-10-23 14:20:23 | `4679c4a` | All-angle radial pocket capacities and physical screens |
| 2026-10-23 14:22:50 | `919cdbe` | Entire point-only TREE.02.P completion case |
| 2026-10-23 14:31:17 | `f5bb8e4` | Exhaustive remaining-tree reduction to P and Y |

[ORIGIN_POCKET_PROGRESS.md](ORIGIN_POCKET_PROGRESS.md) records this continuation's proof scope and actual exact regression execution. The older append-only [PROGRESS_LEDGER.md](PROGRESS_LEDGER.md) retains the preceding checkpoints.

## 7. Verification boundary and exact remaining global work

The committed script check_origin_pockets.py, matched to its Git blob and SHA-256, passed **1,716 exact rational checks** plus physical attainment/strict-normal and non-strict-normal controls. ORIGIN_POCKET_EXACT_CHECK.json contains the actual pinned run; these finite regressions are not all-angle proofs, independent audit or Lean verification.

All six original tree rows are CLOSED hand in the declared radius window. The remaining global obligations are the general boundary-only C7 and mixed cyclic completions, unrestricted radius assembly, complete equality necessity/converse, independent full audit and standard-kernel Lean integration. The tree closure is not a global completion percentage. No unrestricted proof is claimed.
