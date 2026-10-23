# n=9 — origin-pocket continuation progress and exact execution

**Checkpoint:** 2026-10-23. **Read base:** `901678d95a5197017db81343c7d0182661cc92fc`.
**Global result:** unrestricted q>=1105/256 remains OPEN. This continuation closes one entire former tree profile and one full contact-type branch, then gives an exhaustive two-family description of the remaining tree completions. The cyclic branch is not closed.

This is an append-only continuation checkpoint supplementing PROGRESS_LEDGER.md. The source proofs, exact scripts and report are committed through the connected GitHub app; no Lean build or CI was run. All new general arguments remain pending independent mathematical audit.

## 1. Finished mathematical work, committed as it was completed

| GitHub UTC | Commit | Source | Exact closure or reduction |
|---|---|---|---|
| 2026-10-23 13:51:19 | `463afde22f99d4d1d1251a706ff1dd74d3e4269e` | THREE_VERTEX_ORIGIN_CAPACITY.md | **TREE.03 CLOSED:** any three vertex-origin squares at q=17/4 permit at most five additional arbitrary unit squares, hence <=8 total |
| 2026-10-23 14:20:23 | `4679c4a9efb8792cb451b32a2ed26669dc968f8d` | RADIAL_SECTOR_POCKET_CAPACITY.md | All-angle screen, acute/right pocket, moderately obtuse pocket and radial-terminal gap lemmas; no tilt grid |
| 2026-10-23 14:22:50 | `919cdbe939d83c270bd2959ca9f831b21a9c1b22` | TREE02_POINT_CONTACT_COMPLETION.md | **TREE.02.P CLOSED:** every point-only central-contact case has four distinct radial terminals and <=2 additional squares, hence <=8 total; shared-edge type isolated exactly |
| 2026-10-23 14:31:17 | `f5bb8e47be500ececa5c2324c69d32d8108759fe` | REMAINING_TREE_TWO_FAMILY_REDUCTION.md | **Exhaustive remaining-tree normal form:** only family P (staggered four-square path + five extras) or family Y (side/vertex fan + four extras) remains |

### TREE.03 is a full angular family, not a sample

Three disjoint right-angle origin cones leave angular gaps totaling pi/2. Actual-square/inscribed-disk geometry places every other center in those gaps at radii in [1/sqrt(2),3/2]. Any two such centers whose angular separation is <=pi/6 are strictly closer than one. Six extra centers in at most three gaps would require total angular length >pi/2. This covers all cone gaps and all orientations of extra squares.

### TREE.02.P is a full contact type, not a small angle range

For two central vertex squares intersecting only at 0, the physical certificate's strictly exposing common normal forces both side loads on each root. Hence all four distinct radial S terminals are present. Their actual central-side/terminal screens trap every additional square in one of the two full angular gaps.

If the smaller gap is acute, it holds no square; the larger gap is at most 2 arctan(2) and holds at most two. If both gaps are right angles, each holds at most one. No angle range remains untreated in this point-contact case.

**Important certificate premise:** this uses the strictly exposing normal provided by PHYSICAL_CONTACT_STRESS.md at point-only contacts. An arbitrary physical equilibrium with a non-strict normal is a different certificate. The explicit opposite-slider four-body stress is retained as a negative control; it is not silently ruled out.

### Remaining-tree coverage is exact but not a completion theorem

- **P.ALL OPEN:** four aligned centers (-3/2,0),(-1/2,tau_1),(1/2,tau_2),(3/2,0), with both tau_i in [-1/2,1/2], and FIVE further arbitrary squares in D_(17/4). This contains TREE.20, the shared-edge boundary TREE.02.E, and aligned TREE.11 boundaries. The flat row alone is closed.
- **Y.ALL OPEN:** H=[-alpha,1-alpha]x[0,1], 0<alpha<1; K has vertex 0 and orthonormal rays u=(cos(theta),-sin(theta)), v=(-sin(theta),-cos(theta)), 0<theta<pi/2; radial loaded terminals S(up),S(u),S(v); FOUR further arbitrary squares. Exact force balance gives load ratios sin(theta),cos(theta), showing there are no other TREE.11 core forms. Its theta endpoints lie in P.
- All prior six profiles are either excluded, assigned to P, or assigned to Y. Continuous parameters and every unstressed square are retained. **Neither P.ALL nor Y.ALL is yet proved.**

## 2. Actual exact regression execution

Committed script: [check_origin_pockets.py](check_origin_pockets.py), source commit
`607d51b10bb9c96de47d17f984b1632282101b79`.

- Local bytes matched GitHub blob SHA-1 `6fad0c16edb6ddeaac21d13f3369ab1b6a6f01f7`.
- Source SHA-256 `b10302b888b9f1db3effdf9207c2ea7785b8e4b44da1551e9bd9eafec6d9974c`.
- Pinned execution: **2026-10-23 14:29:10.989302–14:29:11.004341 UTC**, Python **3.13.5**, exit **0**.
- Committed report: [ORIGIN_POCKET_EXACT_CHECK.json](ORIGIN_POCKET_EXACT_CHECK.json), commit `9d6a9d63236bc196f17de0a91e26df6ccb257031`.
- A second direct run of the identical source also passed at **14:44:50.458055–14:44:50.473301 UTC**. Its stdout and rerun JSON are local; the committed report intentionally retains the first pinned execution timestamps.

**Passed finite checks:** 1,716 rational comparisons/identities; sharp eight-square attainment of the three-vertex capacity; right-angle-pocket attainment; every corner, SAT pair, actual contact point and force/torque balance of a strictly-normal six-body point-contact core; a shared-edge four-body core; and an opposite-slider non-strict-normal counterexample to dropping the strict-normal premise.

The exact six-body point-contact witness uses root frames (1,0),(0,1) and u=(-4/5,3/5),v=(-3/5,-4/5). The root contact-force vector is (-7/5,-1/5), strict in both normal cones. The terminal raw force magnitudes are 7/5,1/5,1,1. The smaller radial gap is exactly 2 arctan(1/2). All checks use Fraction arithmetic, not numerical tolerances.

**Verification limit:** the finite rational-orientation tests are regressions, not universal all-angle certificates or an independent audit. The general arguments are the symbolic convexity, angular counting, support and physical-barrier proofs in the manuscripts. No mathematical gate is closed solely because sampled optimizations or these regressions passed.

## 3. Exploratory work not promoted to proof

Small numerical searches were used to investigate possible semicage/path/fan capacities. No numerical failure to find a ninth square, no center-only relaxation and no hypothesized rigidity of three squares above a semicage is used as a premise of any committed theorem. The P/Y capacity gates remain open for precisely this reason.

## 4. Updated exact status

- [x] TREE.12, TREE.03, TREE.04: complete whole-profile capacity exclusions at hand level.
- [x] TREE.02.P: complete point-only central-contact exclusion, with strict-normal certificate premise explicit.
- [x] Remaining-tree normal form: all survivors lie in exactly two explicit master completion families P or Y (families may meet at parameter boundaries; nothing is omitted).
- [ ] P.ALL and Y.ALL: full physical completion capacities.
- [ ] CYCLIC: unrestricted cyclic-core sharp classification or universal inequality.
- [ ] Declared lower-radius input, unrestricted radius assembly, complete equality theorem, independent audit and Lean/kernel integration.

Three of six original tree rows are now closed, with a full contact-type subcase of another closed. This is not a completion percentage for the unrestricted theorem. The remaining two master families and the cyclic branch contain substantial open mathematical obligations.