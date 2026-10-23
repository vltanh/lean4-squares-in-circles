# n=9 — current roadmap: deep P/Y obligations and coarse cyclic cell ledger

**Checkpoint:** 2026-10-23 quadrant/block continuation. **The unrestricted n=9 proof is NOT finished.** The new hand work proves an all-orientation quadrant capacity theorem, necessary cyclic load restrictions, an exhaustive coarse cyclic block/bridge partition, and exclusion of its isolated-triangle cell. P.ALL and Y.ALL have not been closed. Of the 58 coarse cyclic cells, 57 sharp physical completion theorems remain open. Independent full audit and Lean verification are outstanding.

## Authoritative deep roadmap and logs

- [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): full G0–G8 gates/subgates/subsubgates, with checked proof implications and unchecked parent obligations.
- [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md): all 58 cyclic coarse cells individually ticked; definitions and full completion contracts.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): original six tree profiles and P/Y survivor cover.
- [G2_SUBGATES.md](G2_SUBGATES.md): live mathematical status.
- [QUADRANT_BLOCK_PROGRESS.md](QUADRANT_BLOCK_PROGRESS.md): current UTC commits, exact execution and negative controls; continues ORIGIN_POCKET_PROGRESS.md and PROGRESS_LEDGER.md.

## Target and existing completed work

Q=1105/256. An exact construction gives R9<=sqrt(Q); the missing theorem is R^2>=Q for every nine-square packing with independent orientations and pairwise disjoint open interiors.

The whole common-coordinate-separable class is closed by hand. The unrestricted minimizer/physical-stress reductions are necessary theorems, not the lower bound itself. The positive tree branch, in the explicit 79/40<=R<=sqrt(Q) window, is quantized to R^2=17/4 and six exhaustive central-incidence profiles. TREE.12, TREE.03 and TREE.04 are excluded in full; the strict-normal point-only subtype TREE.02.P is excluded. All remaining tree candidates are exactly the P or Y families below.

The lower window remains an explicit imported n=8 prerequisite or an independent missing coarse hand bound. It is not proved by the capacity results themselves.

## New hand theorem: quadrant capacity one

[QUADRANT_UNAVOIDABLE_POINT.md](QUADRANT_UNAVOIDABLE_POINT.md) proves:

> Every arbitrary unit square wholly in the first quadrant of D_(17/4) contains (1,1). A tilted square contains it in its open interior; an aligned boundary square contains a common small southwest perturbation. Therefore a quadrant holds at most ONE physically interior-disjoint square.

No radial terminal obstacles, individual frame alignment or common pairwise separators are assumed. The proof uses four exact side-coordinate inequalities and a strict interior-point argument; a mere shared boundary point would not suffice.

Consequently, in every perpendicular frame, any hypothetical nine-square packing in D_(17/4) has at least five squares whose open interiors meet at least one axis. This is necessary, not contradictory by itself. It does NOT prove every extra square of P/Y lies in a chosen quadrant; their whole-family capacities remain open.

## New finite cyclic bookkeeping and one closed cell

[CYCLIC_BLOCK_INVENTORY.md](CYCLIC_BLOCK_INVENTORY.md) proves that, for a selected connected cyclic positive body component, if its maximal cyclic block sizes are k_i>=3 and it has b bridges, then

    n = 1 + b + sum(k_i-1) <= 9.

The solutions are exactly **21 sorted profiles and 58 bridge-count cells**. The individual ledger retains all graphs, contact choices, orientations, loads and 9-n remaining physical squares. This is a **coarse exhaustive partition**, NOT a solved geometric classification or a small sharp proof.

Two necessary physical force rules are established:

- an unloaded positive appendage cannot be attached through only one external body; every endblock therefore has a loaded nonarticulation body;
- the loaded body subset cannot all pairwise physically touch in the declared window. Their center centroid and normalized circle-force balance would give R^2<=625/162<(79/40)^2.

The complete cell **C1.3.b0**, one selected triangle component without bridges, is thereby excluded. Triangle blocks with attached bodies and all other cells remain open.

## Ticked remaining-work summary

| Gate | Current state |
|---|---|
| G2.C entire common-coordinate-separable theorem | [x] CLOSED hand |
| TREE six-profile cover and surviving P/Y normal forms | [x] CLOSED hand reduction |
| TREE.12, TREE.03, TREE.04 and TREE.02.P completion bounds | [x] CLOSED hand |
| QCAP unavoidable point/capacity one | [x] NEW CLOSED hand tool |
| CY.BLOCK 21 profiles / 58 coarse cells | [x] NEW CLOSED hand coverage only |
| CY.LOAD endblock and loaded-clique restrictions | [x] NEW CLOSED hand necessary/exclusion |
| C1.3.b0 | [x] NEW excluded in window |
| **P.ALL** | [ ] OPEN full physical capacity |
| **Y.ALL** | [ ] OPEN full physical capacity |
| **Remaining 57 cyclic cells** | [ ] OPEN uniform sharpness |
| G4 unrestricted sharp radius | [ ] BLOCKED |
| G5 unrestricted equality classification | [ ] OPEN/BLOCKED |
| G6 independent full audit | [ ] NOT COMPLETED |
| G7–G8 Lean kernel proof and integration | [ ] NOT STARTED |

### P.ALL exact contract

The four fixed aligned centers are (-3/2,0),(-1/2,tau1),(1/2,tau2),(3/2,0), with both tau in [-1/2,1/2]. Prove no FIVE additional independently oriented physical unit squares fit D_(17/4). The flat row is closed; the entire two-slider family is not.

### Y.ALL exact contract

H=[-alpha,1-alpha]x[0,1], K=[0,u]+[0,v], u=(cos(theta),-sin(theta)), v=(-sin(theta),-cos(theta)), with alpha in (0,1), theta in (0,pi/2), plus radial terminals S(north),S(u),S(v). Prove no FOUR additional arbitrary squares fit D_(17/4). Its physical five-body core really exists; the theorem must use the remaining four squares.

### CY.SHARP exact contract

For each unchecked cell, prove q>=Q for EVERY nine-square realization with its selected component, or exclude every such component in the radius window. All intra-block adjacencies, actual contacts, independent angles, loaded vertices and other physical squares are quantified. One global invariant closing many cells is preferable to 57 angle-grid searches.

## Exact execution and rejected relaxations

[check_quadrant_blocks.py](check_quadrant_blocks.py), source commit fed5a888, was matched to its Git blob and SHA-256 before execution at **2026-10-23 16:27:18–16:27:19 UTC**, Python 3.13.5, exit 0. [QUADRANT_BLOCK_EXACT_CHECK.json](QUADRANT_BLOCK_EXACT_CHECK.json) records 104 rational identity checks, 2,254 admissible quadrant square samples and 1,772 finite graph checks exercising all 58 cells.

The report also retains an exact FIVE-center feasible relaxation for P: all centers are inside radius 3/2, pairwise separated by more than one, with half-radius disk clearance from every root square. This is NOT a physical square packing. It proves that these center constraints alone are too weak; successful P proof must use actual square supports/corners or stronger physical geometry.

A separate exact two-square witness at centers (5/4,+/-1/2) rejects a universal 45-degree center-angle separation rule. Do not replace the proven annular pi/6 lemma by that false stronger statement.

Finite checks are regressions, not the all-angle/block proofs, physical feasibility of abstract cells, independent audit, Lean certificates or CI. The hand arguments still require independent review.

## Completion discipline

The proof remains unfinished: new tools and finite bookkeeping do not resolve the missing P/Y capacities or 57 sharp cyclic cells. Tick only whole quantified implications, retain all unstressed completion squares, and log the exact evidence and unchanged parent blockers. Counts are not proof-completion percentages. PR #11 remains draft.