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

## How to append future entries

For each substantive research turn, append:
1. **UTC timestamp** and precise GitHub commit(s) (or explicit `LOCAL/UNPUSHED` designation).
2. **Named gate** and exact quantified hypothesis/conclusion.
3. **Evidence**: source path, hand proof/replay scope, any exact counterexample, optional source SHA-256 of regression script.
4. **Closure impact**: does it close a whole structural class, a global necessary reduction, a negative test, or *merely* a special subcase?
5. **Remaining decisive obligation** and pivot trigger. No numerical count of lemmas is a substitute for coverage.

Never log a simulated result, partial computational search, or theorem within a strengthened normalization as closure of unrestricted G2.X/G4. Do not record CI/Lean/audit success until actually executed and reproducible.
