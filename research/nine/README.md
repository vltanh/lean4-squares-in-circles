# Nine unit squares in a circle — current research handoff

**Branch:** `research/nine-tablefree-hand` · **PR:** #11, draft.
**Target:** unrestricted sharp squared radius Q=1105/256 and every attaining packing. The exact construction attains Q; **the unrestricted matching lower bound and complete equality necessity are NOT proved**.

**Latest hand-proof progress:** TREE.03 is excluded in full, and the entire point-only contact branch TREE.02.P is excluded in full. Together with earlier TREE.12/TREE.04 closures, every remaining positive-tree candidate now has one of **two explicit completion skeletons P or Y**. Neither remaining capacity theorem nor the separate cyclic branch is closed. Independent full audit and Lean verification remain outstanding.

## Current roadmaps and progress logs

- [ROADMAP.md](ROADMAP.md): short live status.
- [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): G0–G8 theorem-level dependencies and current P.ALL/Y.ALL/CYCLIC contracts.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): original six exhaustive profiles, contact-type split and checked gates.
- [G2_SUBGATES.md](G2_SUBGATES.md): live mathematical branch ledger.
- [ORIGIN_POCKET_PROGRESS.md](ORIGIN_POCKET_PROGRESS.md): newest UTC commits, exact proof scope and executed regression evidence.
- [PROGRESS_LEDGER.md](PROGRESS_LEDGER.md): preceding append-only checkpoints, retained unchanged as history.

## New whole-case hand proofs

### 1. Three origin-vertex squares: at most eight total squares

[THREE_VERTEX_ORIGIN_CAPACITY.md](THREE_VERTEX_ORIGIN_CAPACITY.md), commit 463afde, assumes only physical unit-square packing at squared radius 17/4 and three squares with the disk center as a vertex. No common frame or stress hypothesis is needed.

The three right-angle cones leave angular center-direction gaps totaling pi/2. Every additional center is confined to those gaps and to radii in [1/sqrt(2),3/2]. Any two such centers at angular distance <=pi/6 are strictly closer than one. Six extra centers among at most three gaps would require more than pi/2. Therefore no ninth square fits: **the entire TREE.03 profile is closed by hand**.

### 2. Physical radial-pocket capacity lemmas

[RADIAL_SECTOR_POCKET_CAPACITY.md](RADIAL_SECTOR_POCKET_CAPACITY.md), commit 4679c4a, defines a radial S terminal as the unit square centered at (3/2)e, with radial coordinates [1,2] and tangential halfwidth 1/2. At q=17/4:

- an outer-face screen prevents any other square from passing beyond its radial face at radius two;
- a central side plus its terminal screens an entire ray, so an additional center in a wedge forces its **whole square** into that wedge;
- acute screened wedges hold no unit square;
- a right-angle screened wedge holds exactly the one origin-vertex square filling it;
- a screened wedge of angle between pi/2 and 2 arctan(2) holds at most two squares;
- distinct S terminal directions must differ by at least 2 arctan(1/2).

These are all-angle geometric proofs with exact convexity/support bounds, not numerical orientation meshes. The screen hypothesis is derived when applied; a center direction alone is not enough.

### 3. All point-only TREE.02 completions excluded

[TREE02_POINT_CONTACT_COMPLETION.md](TREE02_POINT_CONTACT_COMPLETION.md), commit 919cdbe, splits the two central roots into **point-only** or **shared-edge** contact, an exhaustive geometric split.

At point-only contact, the physical minimizing certificate's **strictly exposing common normal** forces two positive terminal loads on each root, yielding four distinct radial S terminals. Their screened complementary gaps fall exactly into the pocket capacity ranges above. At most two squares can be added to the six-body core, hence <=8 total. This closes **all TREE.02.P**, including the equal-right-angle endpoint.

The shared-edge branch **TREE.02.E is not falsely excluded**: it is precisely the four-square path whose two inner heights both equal +1/2, or its reflection. It remains in P.ALL below. Non-strict arbitrary physical equilibria are retained as negative controls; they are not the strict-normal selected certificate used by the theorem.

## All surviving trees reduce to exactly two explicit completion families

[REMAINING_TREE_TWO_FAMILY_REDUCTION.md](REMAINING_TREE_TWO_FAMILY_REDUCTION.md), commit f5bb8e4, proves exhaustive coverage after the closed profiles and point-contact case. It is a necessary normal form, not a capacity proof.

### P.ALL — staggered four-square path [OPEN]

Four aligned square centers:

    (-3/2,0), (-1/2,tau_1), (1/2,tau_2), (3/2,0),
    -1/2 <= tau_1,tau_2 <= 1/2.

Prove that no **five additional** arbitrary unit squares can fit D_(17/4) with this skeleton. This includes TREE.20, TREE.02.E and aligned TREE.11 endpoints. The flat row is excluded already; the full two-slider domain is not. The exact three-above-staggered-row witness shows why independent two-per-side capacities are false.

### Y.ALL — nonaligned side/vertex fan [OPEN]

For 0<alpha<1 and 0<theta<pi/2, take

    H=[-alpha,1-alpha]x[0,1],
    u=(cos(theta),-sin(theta)), v=(-sin(theta),-cos(theta)),
    K={a u+b v:0<=a,b<=1},

plus radial terminals S(up),S(u),S(v). Prove that no **four additional** arbitrary unit squares fit D_(17/4). Exact equilibrium forces the terminal load ratios sin(theta),cos(theta), so this is the entire nonaligned TREE.11 core family. At theta=0 or pi/2 it reduces to P. A genuine nonaligned five-body core exists, so the missing obligation concerns completion to nine, not core impossibility.

## Original six-case tree ledger

| Case | Current state |
|---|---|
| TREE.20: two side-origin roots | OPEN capacity; P.ALL |
| TREE.11: side + vertex | Exact normal form CLOSED; Y.ALL or P endpoint capacity OPEN |
| TREE.12: side + two vertices | CLOSED hand: cardinal cage <=8 total |
| TREE.02: two vertices | Point-only .P CLOSED; shared-edge .E -> P.ALL |
| TREE.03: three vertices | NEW CLOSED hand: angular capacity <=8 total |
| TREE.04: four vertices | CLOSED hand: central 2x2 block <=8 total |

[TREE_BODY_LOCALIZATION.md](TREE_BODY_LOCALIZATION.md) and [TREE_RADIUS_QUANTIZATION.md](TREE_RADIUS_QUANTIZATION.md) prove that every selected positive tree component in **79/40<=R<=sqrt(Q)** has R^2=17/4 and exactly one of these profiles. Disjoint cones give 2s+v<=4, while prior star exclusion gives s+v>=2. Slider endpoints move into vertex rows; they are not lost.

**Window dependency:** the established n=8 theorem can supply the coarse lower bound, with its existing proof dependencies. This continuation does not independently prove that lower window without computation.

The earlier two completion cases are in [TREE_FINITE_COMPLETIONS.md](TREE_FINITE_COMPLETIONS.md): actual-square cardinal-cage and central-block bounds allow arbitrary orientations of all remaining squares.

## Actual exact regression execution

[check_origin_pockets.py](check_origin_pockets.py), source `607d51b10bb9c96de47d17f984b1632282101b79`, was matched to Git blob `6fad0c16edb6ddeaac21d13f3369ab1b6a6f01f7` and SHA-256 `b10302b888b9f1db3effdf9207c2ea7785b8e4b44da1551e9bd9eafec6d9974c` before execution.

The pinned run at **2026-10-23 14:29:10–14:29:11 UTC**, Python 3.13.5, returned exit 0. [ORIGIN_POCKET_EXACT_CHECK.json](ORIGIN_POCKET_EXACT_CHECK.json) records **1,716 exact rational checks**, sharp eight-square attainment, a strict-normal six-body point-contact stress, and shared-edge/non-strict-normal controls. Every corner, true SAT pair, actual application point and force/torque equation is checked in Fraction arithmetic. An identical direct rerun passed at 14:44:50 UTC; the committed report keeps its original execution timestamps.

These finite tests are regressions, **not** universal all-angle proofs, independent audit or Lean certificates. The general arguments are the analytic manuscripts. Earlier check_finite_tree_cases.py / FINITE_TREE_EXACT_CHECK.json and TREE_FINITE_VALIDATION.md retain their original exact scope, including the nonaligned five-body and seven-body branching cores and the false two-per-side control.

## Previously completed global necessary reductions and terminals

SPARSE_MINIMIZER_STRESS.md proves compact unrestricted attainment and exact actual-contact stresses. PLANAR_STRESS_CORE.md gives a <=19-term planar translational support; ROTATION_STATIONARY_STRESS.md gives separate angular stationarity. PHYSICAL_CONTACT_STRESS.md gives a <=27-atom true-point force/torque certificate with planar **incidence** network. RADIAL_BRIDGE_AND_LEAF_REDUCTION.md gives radial bridges, <=4 central bridge-cover bodies and S/D loaded geometry.

Do not identify these distinct graph/certificate representations. A body's actual physical contacts may carry zero stress and remain completion obstacles. Nonbridge cycle forces need not be radial.

COORDINATE_SEPARABLE_NINE_COMPLETE.md closes the entire common-coordinate class; do not reopen its two-stack or zigzag cases for small refinements. The global-frame counterexample prevents promoting it to unrestricted Packing.

UNRESTRICTED_THREE_SQUARE_CAP.md gives the sharp oblique-safe cap and every-direction central-strip necessary condition below Q. SOLID_FOUR_ROW_UNRESTRICTED_NINE.md handles full physical completions of a SOLID row and mixed seam. A staggered path is not solid, and a capless Q example rules out universal triple-cap equality extraction.

Existing signed/grid stresses and conditional equality families remain valid at their stated scopes. Global equality necessity has not been established.

## Exact remaining global work

1. Prove the whole **P.ALL** and **Y.ALL** capacity statements, with all parameter values and all additional physical squares.
2. Prove a sharp exhaustive **CYCLIC** classification or one universal contact/strip/capacity inequality when every selected positive component contains a cycle.
3. Include the explicit lower-window dependency, assemble unrestricted T9, classify all equality packings, independently audit and formalize in standard-kernel Lean before public integration.

All completed work is committed and logged. The unfinished capacity implications are explicit; no unrestricted completion or proof percentage is claimed. PR #11 remains draft.