> **HISTORICAL CHANGELOG — not current status.** For reconciled current PR #11 coarse/fine/exterior counts, all 58 original cell statuses, 140 open detailed obligations and closure policy, see [PROGRESS.md](PROGRESS.md). Entries below preserve their original dated provenance and may have superseded counts.

# n=9 research progress ledger (append-only checkpoints)

**Scope:** PR #11, `research/nine-tablefree-hand`. This file tracks meaningful changes in the **quantified** proof obligations. It is distinct from [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md), which states the full dependencies and closure tests, and [G2_SUBGATES.md](G2_SUBGATES.md), which records the detailed gate statuses.

**Status vocabulary:**
- **CLOSED (hand, conditional)**: a manuscript argues the exact stated implication, including its own hypotheses; no independent audit or Lean kernel check implied.
- **CLOSED (global necessary reduction)**: a manuscript starts from arbitrary unrestricted Packing/minimizers but concludes only a necessary property, not the radius lower bound.
- **DRAFT / NEEDS AUDIT**: new imported manuscript or computational check, whose general argument has not received an independent complete review.
- **REJECTED**: an explicit exact counterexample disproves the proposed normalization.
- **OPEN**: quantified class or sharp inequality not proved.
- **BLOCKED**: requires preceding open gate.

**Permanent global status:** the unrestricted \(n=9\) lower bound \(q\ge Q=1105/256\) is **OPEN**. Construction of a packing at \(Q\) is proved; full equality necessity, independent audit, Lean kernel proof, and final integration are not delivered.

## 2026-10-23 — Baseline reconciliation (UTC)

**Repository state read:** GitHub branch head [028a63b](https://github.com/vltanh/lean4-squares-in-circles/commit/028a63b4fc963eb78d776a7f42ff3606e651e816), recorded by GitHub at **2026-10-23 11:35:37 UTC**. Its file `RADIAL_BRIDGE_AND_LEAF_REDUCTION.md` precedes the local cap/tree continuation; it is not counted as new in this checkpoint.

**Already completed on branch (hand level):**
1. **G2.C:** entire common-coordinate-separable nine-square class has the sharp lower bound, allowing individual square rotations. Source: [COORDINATE_SEPARABLE_NINE_COMPLETE.md](COORDINATE_SEPARABLE_NINE_COMPLETE.md). This does **not** cover packs with oblique-only separating pairs.
2. **G2.O3.0–O3.1:** compact minimizer, actual-contact nonnegative stress (<=19 fixed-frame terms), sparse planar outer-loaded translational core, separate <=27-atom angular certificate, and a **physical** force/torque incidence network with its own planar representation. Sources: [SPARSE_MINIMIZER_STRESS.md](SPARSE_MINIMIZER_STRESS.md), [PLANAR_STRESS_CORE.md](PLANAR_STRESS_CORE.md), [PHYSICAL_CONTACT_STRESS.md](PHYSICAL_CONTACT_STRESS.md), [RADIAL_BRIDGE_AND_LEAF_REDUCTION.md](RADIAL_BRIDGE_AND_LEAF_REDUCTION.md). **Do not silently identify** the separate 19-term planar body certificate with the 27-atom physical torque-balanced one.
3. **G1:** short conditional signed 4+3, four-anchor and four-corner terminal inequalities, with conditional equality families. These are tools, not universal extraction.

**At this baseline (before later GitHub imports), local continuation received:** cap/tree proof package prepared **2026-10-23 12:06–12:11 UTC**, including `UNRESTRICTED_THREE_SQUARE_CAP.md`, `SOLID_FOUR_ROW_UNRESTRICTED_NINE.md`, `SMALL_TREE_STRESS_CORES.md`, `CAP_AND_BRIDGE_GATE_UPDATE.md`, `check_three_square_cap.py`, `THREE_SQUARE_CAP_EXACT_CHECK.json`. The last two remain local regression artifacts unless separately committed. The report records 101 exact algebra checks, 3,174 admissible rational cap-square witnesses, four cap-equality triples, and exact physical stress negative controls. **These finite tests do not certify the universal theorems.**

**Assessment:** New cap and solid-row manuscripts provide terminal inequalities that tolerate oblique separators. The tree manuscript excludes all stressed stars in the stated \(79/40\le R\le\sqrt Q\) window and classifies two-circle-loaded trees there, but its staggered-path completion and all branching/cyclic cores remain open. No finite exhaustive global core/completion classification has been proved. The result is meaningful reduction, **not** global proof closure.

**Critical next milestone:** a single theorem covering **all remaining** physically realizable core + unstressed-square completions (or a new global invariant valid for every minimizing packing), rather than accumulating one more restricted core. Require a finite exhaustive list *with* nine-square packing capacity, or a uniform sharp inequality; labels alone do not count.

## 2026-10-23 12:22–12:28 UTC — Imported research and synchronized deep gates

**Source and exact commit provenance:**

| UTC timestamp | Commit | Change | Quantified impact |
|---|---|---|---|
| 12:22:22 | [415283d](https://github.com/vltanh/lean4-squares-in-circles/commit/415283d3e581f35f7db687ca7d710b0d9eae4b89) | Initial timestamped progress ledger | Logging infrastructure, not a theorem |
| 12:22:51 | [8d92e8f](https://github.com/vltanh/lean4-squares-in-circles/commit/8d92e8f0666dd877bd4248971c8c51e2d2a70c66) | UNRESTRICTED_THREE_SQUARE_CAP.md | Sharp cap terminal, all-direction strip necessary condition; **hand draft, independent audit pending** |
| 12:23:03 | [86ea127](https://github.com/vltanh/lean4-squares-in-circles/commit/86ea127dff34f4f1ad7ad736c1fa8958319d8536) | SOLID_FOUR_ROW_UNRESTRICTED_NINE.md | All five-square completions of a **solid** four-row at q<=Q sharply bounded, oblique separators allowed; **hand draft** |
| 12:23:16 | [48d3b8a](https://github.com/vltanh/lean4-squares-in-circles/commit/48d3b8a4031ddf50622e336d69fb154ee45aeaf0) | SMALL_TREE_STRESS_CORES.md | Two-circle-loaded tree path at R^2=17/4 and full star-core exclusion, **only in 79/40<=R<=sqrt(Q)**; **hand draft** |
| 12:23:28 | [8cc3a37](https://github.com/vltanh/lean4-squares-in-circles/commit/8cc3a37728265a3791c65aa2c48943b8425fecae) | Correct tree provenance | Metadata correction, no mathematical novelty |
| 12:23:44 | [c8db03e](https://github.com/vltanh/lean4-squares-in-circles/commit/c8db03e81e707c6da055d515227ebecb726733b9) | CAP_AND_BRIDGE_GATE_UPDATE.md | Scope-and-blocker handoff, no new theorem |
| 12:27:46 | [102dfae](https://github.com/vltanh/lean4-squares-in-circles/commit/102dfaed077fac4965858a67aa1a426af21a7fe7) | DEEP_GATED_ROADMAP.md updated | Credited O3.1f/g prior global reductions and O3.1h/i/j new conditional results, split O3.2 into completion-aware subgates |

**Proof status and evidence boundary:** the first three imported mathematical manuscripts contain analytic hand arguments, not universally executed certificates. The cap one-square clipped-section proof treats both sign cases and strict rotation, yielding the q<Q **every-direction** strip count (at least five squares meeting |y|<7/16). The solid-row theorem is a complete **conditional** completion. The star theorem excludes an entire graph topology, but only in its declared radius window; the two-loaded staggered path remains a live completion branch. An independent line-by-line audit has **not** been performed.

**Local regression artifacts (not GitHub files):**
`check_three_square_cap.py` SHA-256
`3cf9a5d044609c486dde82133bfe74dfdbf3e3c190a7b34098db03287cec5151`.
`THREE_SQUARE_CAP_EXACT_CHECK.json` SHA-256
`7d43b930af9d8d89a4dd5ee4414f7e4b0e6bdd499e0a4add68ce467f06d785f2`.
The report records 101 algebra checks, 3,174 rational admissible square examples, four cap equality triples and exact stress examples. These do **not** establish the general inequalities; the hand proofs stand or fall independently.

**Unchanged global blocker:** **G2.O3.2 + O3.3 + O4**. No finite exhaustive sharp terminal classification of *every* physically possible stressed nine-square minimizer **with its other unstressed squares** exists. The star exclusion and solid-row theorem do not imply such an enumeration. In particular, general staggered four-square path completions, branching trees and cyclic cores remain open.

**Next research completion criterion:** produce either (a) a short exhaustive diagram of the **entire remaining physical core/completion universe** with a sharp inequality for each leaf, or (b) one all-direction strip/contact-capacity invariant implying \(q_0\ge Q\) in every unrestricted minimizing packing. No count of hand-lemma subcases qualifies as completion.

## 2026-10-23 12:29–12:33 UTC — Roadmap synchronization and finite replay

| UTC | Commit / execution | Completed action | Proof impact |
|---|---|---|---|
| 12:29:11 | [0b26f7f](https://github.com/vltanh/lean4-squares-in-circles/commit/0b26f7f21e99b048e6207cc99e7b0e0bd86ea467) | Added exact UTC/import source provenance to this ledger | Logging only |
| 12:30:48 | [2be1970](https://github.com/vltanh/lean4-squares-in-circles/commit/2be1970b4796c88e9ea0723dc83e52a043e2ccd0) | Updated G2_SUBGATES with old physical/radial reductions and new CAP, ROW, TREE subgates | Closed-vs-open scope reconciliation |
| 12:32:05 | [879b43f](https://github.com/vltanh/lean4-squares-in-circles/commit/879b43fbb671fc135a7949dd23bf32408fff896f) | Updated ROADMAP.md short status | Dependency summary |
| 12:32:48 | [9d16de7](https://github.com/vltanh/lean4-squares-in-circles/commit/9d16de7de0b8ab14a599eea2d7a55afe1e64656b) | Updated README handoff / reading order | No newly proved theorem |
| 12:33:08–12:33:09 | local exact Python rerun, exit 0 | Reran check_three_square_cap.py using Python 3.13.5 | 101 exact algebra checks; 3,174 admissible rational cap squares (3,154 rotated), four cap-equality triples; all displayed finite stress controls passed. **Not a universal proof.** |

**Exact replay caveat:** the locally available
THREE_SQUARE_CAP_EXACT_CHECK.json retains its prior 12:06 UTC
execution timestamps, while the 12:33 UTC direct script stdout
reports a fresh successful run. The script SHA-256 is still
3cf9a5d044609c486dde82133bfe74dfdbf3e3c190a7b34098db03287cec5151;
the local JSON SHA-256 is
7d43b930af9d8d89a4dd5ee4414f7e4b0e6bdd499e0a4add68ce467f06d785f2.
These files remain local, not committed on the GitHub research branch.

**PR metadata:** PR #11 description and title were updated after
the documentation commits, retaining **draft** status and making
G2.O3.2–O4 the only live global structural mathematical frontier.

**Current gate state:** G0–G1 and G2.C closed at hand level;
O3.0–O3.1g closed as global necessary reductions;
O3.1h/i hand manuscripts pending independent audit;
O3.1j partly closed **conditional on the radius window**;
O3.2–O4 still OPEN; unrestricted G4/G5.U and G6–G8 NOT completed.
No candidate value for the *unrestricted* optimum has changed.
Future progress must eliminate an entire remaining full
core/completion class or prove a global sharp invariant.

## How to append future entries

For each substantive research turn, append:
1. **UTC timestamp** and precise GitHub commit(s) (or explicit `LOCAL/UNPUSHED` designation).
2. **Named gate** and exact quantified hypothesis/conclusion.
3. **Evidence**: source path, hand proof/replay scope, any exact counterexample, optional source SHA-256 of regression script.
4. **Closure impact**: does it close a whole structural class, a global necessary reduction, a negative test, or *merely* a special subcase?
5. **Remaining decisive obligation** and pivot trigger. No numerical count of lemmas is a substitute for coverage.

Never log a simulated result, partial computational search, or theorem within a strengthened normalization as closure of unrestricted G2.X/G4. Do not record CI/Lean/audit success until actually executed and reproducible.

## 2026-10-23 12:56–13:21 UTC — Exhaustive tree cover and first two complete cases

**Read base:** `c27384b8112b553c26c6474a8c5bb3fd3ebd02c4`. The older statements above are historical checkpoints; the following is the new current tree status.

| UTC (GitHub-reported unless marked execution) | Commit | Deliverable | Closure impact |
|---|---|---|---|
| 12:56:07 | [4f8144d](https://github.com/vltanh/lean4-squares-in-circles/commit/4f8144db1ff9d6b1ac0388aa1cb9413c5120e997) | TREE_BODY_LOCALIZATION.md | **All** unloaded tree bodies are central; all loaded bodies have S/D radial geometry; all origin-avoiding unloaded bodies are one-step side transmitters |
| 12:58:52 | [4007bfc](https://github.com/vltanh/lean4-squares-in-circles/commit/4007bfcc108d42977202d0bb4cb329ea58c56593) | TREE_RADIUS_QUANTIZATION.md | **Every** positive tree in the stated window has R^2=17/4; exactly six exhaustive origin-incidence completion cases |
| 13:05:27 | [5acabe7](https://github.com/vltanh/lean4-squares-in-circles/commit/5acabe75e3e0b729c6a6279555cffdb6e4fdce05) | TREE_FINITE_COMPLETIONS.md | Whole **TREE.12** and **TREE.04** completion cases excluded: at most eight total squares, arbitrary free rotations allowed |
| Source committed before the pinned run | [8a6eea1](https://github.com/vltanh/lean4-squares-in-circles/commit/8a6eea10cd83379e11190a81309248537d5c6cc8) | check_finite_tree_cases.py | Reproducible exact Q(sqrt(2)) stress and algebra regression source, not a universal proof |
| 13:20:52.173306–13:20:52.299435 (execution) | [dad17ae report](https://github.com/vltanh/lean4-squares-in-circles/commit/dad17aec9e8b6f2729db7c78044e85782f22c144) | FINITE_TREE_EXACT_CHECK.json | Actual run PASS, Python 3.13.5, exit 0; source matched to Git blob before execution |

**Precise finite cover:** let s count unloaded tree bodies with zero in a side's relative interior and v count those with zero at a vertex. The analytic proof first eliminates all origin-interior roots and all radii other than 17/4, then proves 2s+v<=4 and s+v>=2. The six cases are **(2,0),(1,1),(1,2),(0,2),(0,3),(0,4)**. They retain continuous side offsets, relative cone angles and every unstressed physical square. Slider endpoints migrate to the correct vertex case rather than being discarded.

**Closed full cases:**
- **TREE.12 (1,2):** force balance and origin cones require all four cardinal S terminals; the cardinal-cage theorem permits at most four additional squares, hence at most eight total.
- **TREE.04 (0,4):** the four origin quadrants force a solid central 2x2 block; its arbitrary-orientation completion capacity is four more squares, hence at most eight total.

**Still open tree rows:** **TREE.20, TREE.11, TREE.02, TREE.03**. These are four complete geometric families, not a list of sampled angles. The separate **CYCLIC** branch remains open. Therefore two of six tree cases closed is NOT a global completion percentage.

**Exact executed scope:** 909 rational checks; all six integer profiles; seven physical force-and-torque tree examples with every square corner, all pairwise SAT conditions, all genuine application points and force/torque balances checked exactly. Source blob SHA-1 `4262f357214c9067124212dbeb2d2a2d2cd9ec34`; source SHA-256 `5501e227abf47b5c2f9a714dec8a69113c22f59717b4f7d552096c9e59570c9a`. No floating-point comparison or external solver is used in this checker. Finite checks remain regression evidence, not a proof of universal geometry.

**Negative controls preserved:**
1. A genuinely nonaligned five-body TREE.11 at 17/4 exists with positive physical force/torque stress. The missing obligation is its completion to nine, not an invalid core exclusion.
2. TREE.12 has a valid seven-body core despite its ninth-square completion being excluded.
3. Three squares can lie above a staggered four-chain at 17/4; a two-per-side argument is false.
4. A five-square star at q=5/2 is below the theorem window, showing why the lower premise cannot be dropped.
5. A cardinal cage plus a diagonal-center square fits q=9/2, showing why the cage's exact radius matters.

**Sources and state tracking:** [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md), commit `b3538b119cfbd826fcf43d84dce18bd10fc093e9`; [TREE_FINITE_VALIDATION.md](TREE_FINITE_VALIDATION.md), commit `437908477d1eaef831fa41d058b74b07d331deef`; detailed roadmap reconciled in `b329785e3ad4579069daee7314d86357287e54df`.

**Remaining global implication:** prove all four unsolved tree completion rows and the cyclic branch sharply, with the explicit 79/40 lower-window dependency, or find one universal completion-aware inequality. Unrestricted G4/G5, independent full audit and Lean verification remain open. All new general results are hand manuscripts pending independent audit; no CI or Lean run is claimed.
