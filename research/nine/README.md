# Nine unit squares in a circle — current research handoff

**Branch:** `research/nine-tablefree-hand` · **PR:** #11, draft.
**Target:** unrestricted sharp squared radius Q=1105/256 and all attaining packings. The exact construction attains Q; **unrestricted lower bound and complete global equality necessity remain OPEN**.

**Latest continuation, 2026-10-23:** the entire positive-tree stress branch in the explicitly stated radius window has been reduced to **R^2=17/4 and six exhaustive origin-incidence cases**. Two complete nine-square completion cases are excluded by hand; four tree cases and the cyclic branch remain open. New arguments are pending independent mathematical audit. No Lean build or CI is claimed.

## Read these first

1. [ROADMAP.md](ROADMAP.md): short current status.
2. [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): full G0–G8 proof dependency contracts, with the new tree subgates checked individually.
3. [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): exactly six tree cases, precise remaining completion obligations and UTC source commits.
4. [G2_SUBGATES.md](G2_SUBGATES.md): current mathematical ledger.
5. [PROGRESS_LEDGER.md](PROGRESS_LEDGER.md): append-only progress and validation log.

## New finite-tree work

### TREE.F1: every positive tree body is localized

[TREE_BODY_LOCALIZATION.md](TREE_BODY_LOCALIZATION.md), commit 4f8144d, uses the existing physical radial bridge theorem. Every unloaded tree body is central and circle-clear, so at most four occur. Every loaded tree body has exact radial S/D geometry even if not a graph leaf. An unloaded body avoiding zero can only be one side-normal transmitter leading to a single S terminal; its incoming neighbor(s) contain zero. This eliminates arbitrary long off-origin arms without enumerating angle windows.

### TREE.F2: every tree radius is 17/4, with exactly six cases

[TREE_RADIUS_QUANTIZATION.md](TREE_RADIUS_QUANTIZATION.md), commit 4007bfc, proves:

> In 79/40 <= R <= sqrt(Q), any selected positive physical tree component has **R^2=17/4**. All its unloaded bodies contain zero on their boundaries; all loaded bodies are radial S terminals centered at (3/2)e with inward contact e.

The proof first excludes an origin-interior root via an exhaustive side/vertex short-arm contact split, then forces the radius from either side-interior or vertex incidence. If s and v count those two incidence types of unloaded component bodies, disjoint tangent cones give 2s+v<=4, while star exclusion gives s+v>=2. Thus the following six rows are **exhaustive**, retaining continuous parameters and all physical completion squares.

| Case | (s,v) | Nine-square completion |
|---|---|---|
| TREE.20 | (2,0) | OPEN: full two-slider staggered path; flat row already excluded |
| TREE.11 | (1,1) | OPEN: side-plus-vertex family, including genuinely nonaligned cores |
| **TREE.12** | **(1,2)** | **CLOSED hand: total capacity <=8** |
| TREE.02 | (0,2) | OPEN: all compatible two-vertex cone angles |
| TREE.03 | (0,3) | OPEN: all compatible three-vertex angular gaps |
| **TREE.04** | **(0,4)** | **CLOSED hand: total capacity <=8** |

Slider endpoints migrate into vertex-incidence rows; no boundary case is discarded. A finite tree inventory is **not** a completed cyclic-graph inventory.

**Window dependency:** the lower radius 79/40 is an explicit premise, supplied for a global n=9 application by the established n=8 lower bound or a separate proof. The current n=8 source has computational dependencies. This continuation does not claim a new independent table-free lower-window proof.

### TREE.12 and TREE.04: complete physical capacity bounds

[TREE_FINITE_COMPLETIONS.md](TREE_FINITE_COMPLETIONS.md), commit 5acabe7, proves two reusable exact capacity theorems at squared radius 17/4:

- **Cardinal cage:** the four outer squares centered at (+/-3/2,0),(0,+/-3/2) leave space for at most four other unit squares, **without any shared-orientation or coordinate-separation assumption on those others**. Inscribed-disk distances leave central or diagonal center regions; an exact all-angle square-corner inequality rules out the diagonal pockets.
- **Central block:** four central squares filling [-1,1]^2 permit only the four outer cardinal centers, whose frames must align. Hence at most eight squares total.

TREE.12 forces the cardinal cage by central-angle geometry and circle-force balance. TREE.04 forces the central block by full origin-angle saturation. Both exclusions cover every physical completion to nine, not merely the stressed subconfiguration.

## Executed exact regressions, not a universal proof

[check_finite_tree_cases.py](check_finite_tree_cases.py), source commit 8a6eea1, was matched to the committed Git blob and SHA-256 before an actual run at **2026-10-23 13:20:52 UTC**, Python 3.13.5, exit 0. The script uses exact Fraction arithmetic and Q(sqrt(2)), not floats or an optimizer.

[FINITE_TREE_EXACT_CHECK.json](FINITE_TREE_EXACT_CHECK.json) records:

- 909 rational checks of displayed identities/constants and the six integer profiles;
- seven exact physical tree stresses, checking every corner, every true SAT pair, every shared force point, all center/angle balances and normalized positive loads;
- cardinal-cage eight-square attainment and explicit failed-shortcut controls.

[TREE_FINITE_VALIDATION.md](TREE_FINITE_VALIDATION.md) documents important witnesses:

1. A genuinely nonaligned five-body TREE.11 at 17/4 exists. The missing theorem must use the four other physical squares, not falsely exclude that core.
2. A seven-body TREE.12 exists even though its completion to nine is impossible.
3. Three squares fit on one side of a staggered four-chain at 17/4. An independent two-per-side capacity argument would be false.
4. A positive star below the lower-radius window is retained as a premise check.

The general hand theorems are proved symbolically, not by these finite examples. Independent audit and Lean verification remain separate outstanding tasks.

## Previously completed unrestricted necessary reductions

[SPARSE_MINIMIZER_STRESS.md](SPARSE_MINIMIZER_STRESS.md) gives compact attainment and a normalized exact stress on actual contacts at an unrestricted minimizer. At most 19 positive fixed-frame terms suffice, and the center dual attains the unknown radius q0. This does not establish q0>=Q.

[PLANAR_STRESS_CORE.md](PLANAR_STRESS_CORE.md) produces a planar outer-loaded translational support; [ROTATION_STATIONARY_STRESS.md](ROTATION_STATIONARY_STRESS.md) supplies separate angular balance with <=27 atoms.

[PHYSICAL_CONTACT_STRESS.md](PHYSICAL_CONTACT_STRESS.md) supplies force and torque at genuine shared points in one <=27-atom physical certificate, with a planar **contact-point incidence** representation. Its body-pair graph is not asserted planar. Do not silently identify this certificate with the <=19 planar translational one.

[RADIAL_BRIDGE_AND_LEAF_REDUCTION.md](RADIAL_BRIDGE_AND_LEAF_REDUCTION.md), prior commit 028a63b, supplies radial bridge cuts, the <=4 central bridge-cover bodies and exact loaded S/D leaves. These are credited as pre-existing inputs to the new tree work.

The earlier exact scripts/check records remain scoped to the examples and identities they actually execute: check_sparse_stress.py / SPARSE_STRESS_EXACT_CHECK.json and check_physical_contact_stress.py / PHYSICAL_STRESS_EXACT_CHECK.json. Finite regression is not universal optimality.

## Cap, row and coordinate-separable tools

[UNRESTRICTED_THREE_SQUARE_CAP.md](UNRESTRICTED_THREE_SQUARE_CAP.md) proves the sharp arbitrary-angle cap theorem and the unrestricted necessary condition that every q<Q packing has at least five squares meeting |y|<7/16 in every direction. A capless q=Q witness prohibits a mandatory triple-cap equality normal form.

[SOLID_FOUR_ROW_UNRESTRICTED_NINE.md](SOLID_FOUR_ROW_UNRESTRICTED_NINE.md) covers all five-square completions of a **solid** four-row, including oblique separators among the free squares. The flat q=17/4 tree path is excluded through it; staggered paths are not silently called solid.

[COORDINATE_SEPARABLE_NINE_COMPLETE.md](COORDINATE_SEPARABLE_NINE_COMPLETE.md) closes the whole common-coordinate-separable class, including its former (4,1) and (3,2) complement cases. Do not reopen those two-stack or zigzag branches for minor constant improvements. The exact global-frame counterexample prevents promoting this result to all packings.

Existing analytic sources remain valid within their stated scopes: ORIENTATION_STABLE_SEVEN_ANCHOR.md, FOUR_ANCHOR_STRESS.md, PAIRED_FOUR_ANCHOR_STRESS.md, SIGNED_MATCHED_CHAIN_STRESS.md, GRID_FOUR_CORNER_STRESS.md and SEPARATOR_GRAPH_CONVEX_DUAL.md. The signed and stratified equality-family manuscripts remain conditional, not globally exhaustive.

## Mandatory negative controls

- NO_GLOBAL_ORTHOGONAL_FRAME.md: true oblique-only pair separation occurs at q=Q.
- TWO_STACK_SHARP_EQUALITY_WITNESS.md: the residual two-column class is attained at equality; a blanket exclusion was false.
- NONSTRATIFIED_PARALLEL_NINE.md: even all-parallel equality configurations can lack stratification in every frame.
- CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md and CENTER_RELAXATION_COUNTEREXAMPLE.md: the ninth physical square and actual support widths matter.
- TREE_FINITE_VALIDATION.md: nonaligned/branching tree cores and three-above-staggered-row examples forbid new overstrong shortcuts.

## Exact next work and no false completion metric

**First:** close TREE.20, TREE.11, TREE.02 and TREE.03 as whole continuous geometric completion classes, or find a single capacity theorem covering several of them. These are the four unchecked rows of a proven finite six-case tree partition.

**Separately:** derive the sharp exhaustive cover or global inequality for selected positive components with cycles. Tree radiality is not a rule for all cycle edges. A finite combinatorial syntax alone is not a finished sharp inequality.

**Then:** include the explicit lower-window dependency, assemble unrestricted T9, classify every equality packing, perform an independent mathematical audit, formalize in standard-kernel Lean and integrate the public interfaces. No full theorem or kernel verification is claimed now.

**Progress metric:** two entire cases in an exhaustive six-case tree inventory are closed at hand level. That is a precise finite-case advance, not a claim that one third of the unrestricted problem is solved. Commit completed arguments promptly and log their exact scope and remaining blockers.
