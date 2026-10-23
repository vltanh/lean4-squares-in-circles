# n=9 research progress ledger (append-only checkpoints)

**Scope:** PR #11, \`research/nine-tablefree-hand\`. This file tracks meaningful changes in the **quantified** proof obligations. It is distinct from [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md), which states the full dependencies and closure tests, and [G2_SUBGATES.md](G2_SUBGATES.md), which records the detailed gate statuses.

**Status vocabulary:**
- **CLOSED (hand, conditional)**: a manuscript argues the exact stated implication, including its own hypotheses; no independent audit or Lean kernel check implied.
- **CLOSED (global necessary reduction)**: a manuscript starts from arbitrary unrestricted Packing/minimizers but concludes only a necessary property, not the radius lower bound.
- **DRAFT / NEEDS AUDIT**: new imported manuscript or computational check, whose general argument has not received an independent complete review.
- **REJECTED**: an explicit exact counterexample disproves the proposed normalization.
- **OPEN**: quantified class or sharp inequality not proved.
- **BLOCKED**: requires preceding open gate.

**Permanent global status:** the unrestricted \(n=9\) lower bound \(q\ge Q=1105/256\) is **OPEN**. Construction of a packing at \(Q\) is proved; full equality necessity, independent audit, Lean kernel proof, and final integration are not delivered.

## 2026-10-23 — Baseline reconciliation (UTC)

**Repository state read:** GitHub branch head [028a63b](https://github.com/vltanh/lean4-squares-in-circles/commit/028a63b4fc963eb78d776a7f42ff3606e651e816), recorded by GitHub at **2026-10-23 11:35:37 UTC**. Its file \`RADIAL_BRIDGE_AND_LEAF_REDUCTION.md\` precedes the local cap/tree continuation; it is not counted as new in this checkpoint.

**Already completed on branch (hand level):**
1. **G2.C:** entire common-coordinate-separable nine-square class has the sharp lower bound, allowing individual square rotations. Source: [COORDINATE_SEPARABLE_NINE_COMPLETE.md](COORDINATE_SEPARABLE_NINE_COMPLETE.md). This does **not** cover packs with oblique-only separating pairs.
2. **G2.O3.0–O3.1:** compact minimizer, actual-contact nonnegative stress (<=19 fixed-frame terms), sparse planar outer-loaded translational core, separate <=27-atom angular certificate, and a **physical** force/torque incidence network with its own planar representation. Sources: [SPARSE_MINIMIZER_STRESS.md](SPARSE_MINIMIZER_STRESS.md), [PLANAR_STRESS_CORE.md](PLANAR_STRESS_CORE.md), [PHYSICAL_CONTACT_STRESS.md](PHYSICAL_CONTACT_STRESS.md), [RADIAL_BRIDGE_AND_LEAF_REDUCTION.md](RADIAL_BRIDGE_AND_LEAF_REDUCTION.md). **Do not silently identify** the separate 19-term planar body certificate with the 27-atom physical torque-balanced one.
3. **G1:** short conditional signed 4+3, four-anchor and four-corner terminal inequalities, with conditional equality families. These are tools, not universal extraction.

**Unpushed local continuation received:** [cap/tree proof package](sandbox:/mnt/data/n9_cap_and_tree_proofs.zip) prepared **2026-10-23 12:06–12:11 UTC**, including \`UNRESTRICTED_THREE_SQUARE_CAP.md\`, \`SOLID_FOUR_ROW_UNRESTRICTED_NINE.md\`, \`SMALL_TREE_STRESS_CORES.md\`, \`CAP_AND_BRIDGE_GATE_UPDATE.md\`, \`check_three_square_cap.py\`, \`THREE_SQUARE_CAP_EXACT_CHECK.json\`. The last two remain local regression artifacts unless separately committed. The report records 101 exact algebra checks, 3,174 admissible rational cap-square witnesses, four cap-equality triples, and exact physical stress negative controls. **These finite tests do not certify the universal theorems.**

**Assessment:** New cap and solid-row manuscripts provide terminal inequalities that tolerate oblique separators. The tree manuscript excludes all stressed stars in the stated \(79/40\le R\le\sqrt Q\) window and classifies two-circle-loaded trees there, but its staggered-path completion and all branching/cyclic cores remain open. No finite exhaustive global core/completion classification has been proved. The result is meaningful reduction, **not** global proof closure.

**Critical next milestone:** a single theorem covering **all remaining** physically realizable core + unstressed-square completions (or a new global invariant valid for every minimizing packing), rather than accumulating one more restricted core. Require a finite exhaustive list *with* nine-square packing capacity, or a uniform sharp inequality; labels alone do not count.

## How to append future entries

For each substantive research turn, append:
1. **UTC timestamp** and precise GitHub commit(s) (or explicit \`LOCAL/UNPUSHED\` designation).
2. **Named gate** and exact quantified hypothesis/conclusion.
3. **Evidence**: source path, hand proof/replay scope, any exact counterexample, optional source SHA-256 of regression script.
4. **Closure impact**: does it close a whole structural class, a global necessary reduction, a negative test, or *merely* a special subcase?
5. **Remaining decisive obligation** and pivot trigger. No numerical count of lemmas is a substitute for coverage.

Never log a simulated result, partial computational search, or theorem within a strengthened normalization as closure of unrestricted G2.X/G4. Do not record CI/Lean/audit success until actually executed and reproducible.
