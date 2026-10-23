# n=9 — live G2 ledger: three tree profiles closed, two surviving master families

**Checkpoint:** 2026-10-23 origin-pocket continuation. **Unrestricted q>=Q=1105/256 is NOT proved.** The completed common-coordinate class remains closed at hand level. The six-case tree cover now has three complete profile exclusions, plus a complete point-contact subtype exclusion. Every remaining tree candidate has one of two explicit physical completion skeletons, P or Y. Their capacities and the cyclic branch remain open.

**Evidence status:** general results below are written hand arguments, pending independent full audit and Lean verification. Finite exact regression is not a universal proof. Historical versions and timestamps remain in Git.

See DEEP_GATED_ROADMAP.md for complete contracts, FINITE_TREE_CASE_LEDGER.md for the six profiles, and ORIGIN_POCKET_PROGRESS.md for this continuation's UTC commits and actual execution.

## 1. Existing closed branches and unrestricted reductions

- [x] **G2.C:** COORDINATE_SEPARABLE_NINE_COMPLETE.md proves the sharp bound for every nine-square packing separable in one common orthonormal frame, despite arbitrary individual rotations. The old zigzag and two-stack cases are all closed within this class.
- [x] **O3.0.2:** SPARSE_MINIMIZER_STRESS.md gives compact unrestricted attainment, true-contact selection, normalized nonnegative stress and exact dual attainment at q0.
- [x] **O3.1a–e:** PLANAR_STRESS_CORE.md gives <=19-term planar translational support; ROTATION_STATIONARY_STRESS.md gives separate <=27-atom angular stationarity.
- [x] **O3.1f:** PHYSICAL_CONTACT_STRESS.md gives actual shared force points, joint force/torque balance and a planar contact-point incidence network. Do not identify this with a planar body graph or the 19-term translational certificate.
- [x] **O3.1g:** RADIAL_BRIDGE_AND_LEAF_REDUCTION.md proves radial positive bridges, <=4 central circle-clear bridge-cover bodies, and exact side/diagonal loaded-leaf geometry.
- [x] **CAP/ROW:** sharp three-square cap, every-direction subcritical strip occupancy, solid-four-row completion and mixed seam terminals; these remain conditional tools or global necessary conditions, not unrestricted extraction.

**Selected certificate:** at a point-only vertex/vertex contact, the physical construction chooses a normal strictly exposing the point in both squares. At an off-origin contact of this type it can also be chosen nonradial. The TREE.02.P proof below requires this strict-normal choice; arbitrary non-strict force equilibria are not silently covered.

## 2. Complete tree reduction, with explicit radius premise

Assume 79/40<=R<=sqrt(Q), with the lower window imported explicitly from the established n=8 result or separately proved. The new fixed-radius capacity lemmas do not themselves prove this prerequisite.

- [x] **TREE.F1:** TREE_BODY_LOCALIZATION.md localizes every unloaded tree body; loaded bodies have radial S/D geometry even at higher degree; origin-avoiding unloaded bodies are single side-normal transmitters to S terminals.
- [x] **TREE.F2.I:** origin-interior roots are excluded by the exhaustive short-arm support-point alternatives and previous star exclusion.
- [x] **TREE.F2.R:** TREE_RADIUS_QUANTIZATION.md forces **R^2=17/4 for every positive tree component** in the window. Unloaded bodies meet zero only on side interiors or vertices, loaded bodies are S(e) at centers (3/2)e.
- [x] **TREE.F2.C:** tangent cones imply 2s+v<=4 and star exclusion s+v>=2, giving exactly six profiles. Every parameter and every unstressed physical square is retained.

## 3. Six original profiles: checked statuses

| Profile | Entire completion class | Status |
|---|---|---|
| TREE.20 (2,0) | Two side-origin roots, all staggered-path offsets | OPEN capacity, maps to P.ALL |
| TREE.11 (1,1) | Side-origin + vertex-origin roots, all compatible angles/offsets | Exact normal-form reduction CLOSED; capacity Y.ALL or P endpoints OPEN |
| TREE.12 (1,2) | Side root + two vertex roots | CLOSED hand: cardinal cage <=8 total |
| TREE.02 (0,2) | Two vertex roots | PARTIAL: point-only TREE.02.P CLOSED; shared-edge TREE.02.E maps to P.ALL |
| TREE.03 (0,3) | Three vertex roots | NEW CLOSED hand: annular angular capacity <=8 total |
| TREE.04 (0,4) | Four vertex roots | CLOSED hand: central block <=8 total |

Boundary slider positions migrate to vertex profiles; they are not discarded. The profiles refer to the selected positive component, while their capacity statements include every other physical square.

### Previously closed TREE.12 and TREE.04

TREE_FINITE_COMPLETIONS.md proves that a cardinal cage of four radial outer squares and a central solid 2x2 block each permit at most four additional unit squares at q=17/4, even when those additions rotate or have oblique separators. TREE.12 forces the cage by equilibrium, and TREE.04 forces the block by origin-angle saturation.

### New TREE.03: complete whole-profile capacity

THREE_VERTEX_ORIGIN_CAPACITY.md has no stress premise. Three vertex-origin squares leave three angular center-direction gaps totaling pi/2. Other centers lie in those gaps and have radii in [1/sqrt(2),3/2]. Two such centers with angular separation <=pi/6 are strictly closer than one. Six extra centers distributed among <=3 gaps would require >pi/2. Therefore at most five extras fit, eight total.

- [x] Entire TREE.03 profile, all cone gaps and arbitrary extra orientations.
- [x] All equality/boundary cone-gap points included.
- [x] The eight-square cardinal cross attains the capacity bound; a smaller core is not falsely declared impossible.

### New TREE.02.P: complete point-only central-contact branch

TREE02_POINT_CONTACT_COMPLETION.md gives exactly two central contact types. With point-only contact, the selected strictly exposing normal requires two positive side-direction terminal loads at each root. Four distinct S terminals are present.

RADIAL_SECTOR_POCKET_CAPACITY.md proves that the central sides plus terminals screen their rays and trap every extra square wholly in a complementary wedge. The smaller gap is >=2 arctan(1/2), so the larger is <=2 arctan(2). Acute pockets are empty; right pockets hold a unique square; moderately obtuse pockets in the stated complete range hold <=2. Six core bodies therefore admit <=2 more squares, eight total.

- [x] Entire positive-angle point-contact family, not a sampled tilt range.
- [x] Right/right boundary g=h=pi/2 included.
- [x] Non-strict-normal negative control retained explicitly.

### TREE.02.E: exact shared-edge boundary

The roots share a full side and form a 2x1 half-block. Their possible loaded directions are E,N,W; component circle-force balance forbids positive N, leaving the two opposite E/W terminals. The component is exactly the four-square path with both inner offsets +1/2 (or reflection).

- [x] Exact shared-edge normal form.
- [ ] Its five-square completion, included in P.ALL.
- A zero-weight physical N square is still allowed; zero load is not absence of a physical body.

## 4. All remaining tree completions: exactly P and Y

REMAINING_TREE_TWO_FAMILY_REDUCTION.md proves exhaustive coverage after the completed exclusions.

### P.ALL — four-square staggered path plus FIVE arbitrary squares [OPEN]

Fixed aligned centers:

    (-3/2,0), (-1/2,tau_1), (1/2,tau_2), (3/2,0),
    -1/2 <= tau_1,tau_2 <= 1/2.

The theorem needed is no five additional physical unit squares in D_(17/4), for the whole parameter square. This includes all TREE.20, TREE.02.E and aligned TREE.11 boundaries. The flat row is already excluded, but the two-slider family is not. The known three-above-staggered-row witness rejects independent two-per-side capacities.

### Y.ALL — side/vertex fan plus FOUR arbitrary squares [OPEN]

Parameters 0<alpha<1, 0<theta<pi/2:

    H=[-alpha,1-alpha]x[0,1],
    u=(cos(theta),-sin(theta)), v=(-sin(theta),-cos(theta)),
    K={a u+b v:0<=a,b<=1},
    loaded squares S((0,1)), S(u), S(v).

Exact equilibrium of TREE.11 gives the two downward loads in ratios sin(theta),cos(theta). For interior theta both are positive; at theta=0 or pi/2 one disappears and the geometry becomes P after exchanging axes.

- [x] All TREE.11 positive cores classified, including aligned boundary limits.
- [ ] No four additional arbitrary squares for the entire fan parameter range.
- The nonaligned five-body fan really exists and must not be excluded without its completion capacity.

**TREE.ALL remains OPEN** until P.ALL and Y.ALL are both proved, with the stated lower-window prerequisite. This two-family cover is a necessary reduction, not a sharp inequality.

## 5. CYCLIC and global assembly [OPEN]

Either some selected positive component is a tree, or every positive component contains a cycle. The latter branch is not in the tree table.

- [ ] **CY.1:** a human-sized exhaustive physical inventory including loaded bodies, bridges, junctions and all unstressed completions, or one universal alternative inequality.
- [ ] **CY.2:** orientation-uniform sharp bound q0>=Q for every surviving full nine-square realization.
- [ ] **CY.3:** equality, zero-weight and contact-tie limits. Nonbridge edges need not be radial.
- [ ] **O3.3/O4:** P.ALL, Y.ALL and CYCLIC covered sharply, or bypassed by one global completion-aware theorem.
- [ ] **O5/G2.X/G4:** exclude unrestricted q<Q minimizers, combine with attainment and match the public theorem.
- [ ] **G5.U:** complete unrestricted equality necessity and parameter converse; the current signed/stratified families are conditional.
- [ ] **G6–G8:** independent full audit, standard-kernel Lean proof and integration.

## 6. Actual execution, source provenance and limits

check_origin_pockets.py at source commit `607d51b10bb9c96de47d17f984b1632282101b79` was matched to Git blob `6fad0c16edb6ddeaac21d13f3369ab1b6a6f01f7` and SHA-256 `b10302b888b9f1db3effdf9207c2ea7785b8e4b44da1551e9bd9eafec6d9974c`. The pinned run passed at **2026-10-23 14:29:10.989302–14:29:11.004341 UTC**, Python 3.13.5, exit 0; an identical rerun also passed at 14:44:50 UTC.

ORIGIN_POCKET_EXACT_CHECK.json records **1,716 exact rational checks**, sharp eight-square origin-capacity attainment, the unique right-pocket square, a six-body strict-normal stress, and shared-edge/non-strict-normal controls with all corners, SAT pairs, real force points and force/torque equations checked.

These finite checks are not the all-angle proofs or independent audit. ORIGIN_POCKET_PROGRESS.md records the exact analytic scope and UTC proof commits. The older finite-tree and cap checks retain their original scope and are not counted as new results.

**Progress rule:** tick only a whole quantified profile, an exhaustive contact type, or a proved necessary reduction. Do not equate a count of checked tree rows with a percentage of global proof completion, and do not replace true square completion geometry by center-only numerical tests.
