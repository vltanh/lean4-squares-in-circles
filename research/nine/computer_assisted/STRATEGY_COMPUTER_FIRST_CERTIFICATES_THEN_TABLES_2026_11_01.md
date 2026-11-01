# n=9 revised proof strategy — computer discovery, exact certificates, compact tables, then hand simplification

**Adopted research workflow, 2026-11-01 UTC.** The user has expressly superseded the former hand-only/no-mathematical-scripts restriction. Numerical computation, constraint programming, and exact proof scripts are now permitted. **Do not run Lean, Lake, or CI** in this workflow. This document supersedes the obsolete computational prohibition in older handoffs; it does not change any previously adopted mathematics or canonical case flags.

**Target.** Nine freely oriented closed unit squares with pairwise disjoint interiors in one disk. The known construction has radius squared Q = 1105/256. Prove R² >= Q for *all* nine-square packings, then classify equality, using the original compatible physical contact-force-and-torque certificate. A feasible equality witness already exists; it would be a logical error to ask a solver to prove all configurations at R² <= Q infeasible. Exclude only precisely defined *forbidden original stress/case branches*, and retain legitimate equality branches.

## 0. Authoritative baseline and evidence levels

The original full-nine-square counts at parent commit fa56efb9d0e4b2c95934199fcadedea064c1775f are unchanged:

| Canonical inventory | Closed | Open | Total |
| --- | ---: | ---: | ---: |
| Original coarse parents | 41 | 17 | 58 |
| Original uniquely labeled fine gates | 2,373 | 140 | 2,513 |
| Nested six-body exterior rows, included in the original workload | 18 | 20 | 38 |

The unrestricted lower bound, equality uniqueness/classification, and final same-selected-certificate G4.2.c audit remain OPEN. The old 296-record refinement is a coverage map, not 296 equally difficult gates; do not spend effort manufacturing more bookkeeping gates.

**Sources already on the branch:**

- Exact no-dependency checker: [verify_force_triangle.py](verify_force_triangle.py).
- Its analytic derivation, four chart summaries, proof coverage and run output: [FORCE_TRIANGLE_EXACT_INTERVAL_SCREEN_2026_11_01.md](FORCE_TRIANGLE_EXACT_INTERVAL_SCREEN_2026_11_01.md).
- Independently unreviewed, conditional application-coincidence hand exclusion: [ALL_COMMON_POINT_INTERNAL_APPLICATIONS_EQUAL_EXCLUSION_2026_11_01.md](../ALL_COMMON_POINT_INTERNAL_APPLICATIONS_EQUAL_EXCLUSION_2026_11_01.md).
- Prior full original parent inventory and geometry: [PROGRESS.md](../PROGRESS.md) and [gates/SESSION_CHECKPOINTS.md](../gates/SESSION_CHECKPOINTS.md).
- Prior hand-only physical frontier: [HANDOFF_DIRECT_TRIANGLE_AND_ORIGINAL_FRONTIER_2026_11_01.md](../HANDOFF_DIRECT_TRIANGLE_AND_ORIGINAL_FRONTIER_2026_11_01.md). Its *mathematics* remains; its *no computational scripts* policy is superseded here.

Distinguish **N** (numerical lead or candidate), **X** (machine-certified exhaustive implication with source, run output, and complete coverage argument), **H** (human manuscript at stated restricted domain), **V** (independent mathematical review), **J** (joined to all original nine-square callers), and **C** (all original subbranches closed). X does NOT automatically imply V, J or C. Every counted closure still needs a complete original domain, its compatibility assumptions and an independent check. Do not promote proposed hand exclusion from H to V without reconstruction.

## 1. What the first computation actually established

For the original fully circle-unloaded three-square direct triangle K={A,B,C}, with internal positive force vectors x, y, z and magnitudes a, b, c, and with exactly one original outside positive exit at each core square, the full-center-work inequality is

    C > (60/31) W,   W=a+b+c,
    C=|x-y|+|y-z|+|z-x|.

This retains ALL original cut edges, all nine real squares, arbitrary repeated outside neighbors and every support mean. A finite exact rational interval checker proves for *all* planar x,y,z with W=1 and min(a,b,c)>=1/12 that C<=60/31. Thus, necessarily,

    min(a,b,c) < W/12.

The certificate has four exhaustive half-angle orientation-chart roots; the recorded run used 175,382 interval nodes, 65,915 certified nonempty leaves and 21,778 provably empty leaves, with largest depth 25 and smallest nonempty rational margin 29/1,015,808. The table in the source is a **summary of exact interval coverage**, not four self-contained handwritten geometric cases. Independent scrutiny of the chart coverage, interval rules, square-work transfer and run is still needed. The actual Python source and asserted integer comparisons, not the printed counts alone, are the executable certificate.

A second limited hand argument excludes the common-point direct-triangle feature if ALL THREE *original internal force applications* coincide with that actual point (including the prior parallel-frame exclusion). It relies on the strict singleton original normal convention and the original full force/torque stars; independent review is pending. **A common physical junction alone is weaker**: a shared-side application can occur away from its endpoint. Distinct three contact points also remain open.

No fifth coarse parent or new canonical fine ID is closed by either proper-feature result.

## 2. Algorithmic architecture (discovery ≠ certification)

### Stage A — replay, cross-check and freeze the existing exact lemma

1. Run from the repository root: python research/nine/computer_assisted/verify_force_triangle.py. Confirm the four per-chart counts, 175,382 total nodes and nonnegative exact margins.
2. Independently rederive the full-cut work identity and the bound |center|<91/60 from the four actual corners; check every strict sign and that no cut edge or circle load was deleted.
3. Review all four rational orientation chart roots, the direction sign chart, the permutation a>=b>=c and the non-strict boundary a=b, b=c, c=1/12. Verify that every genuine configuration is enclosed.
4. Independently verify that every apparently empty magnitude box is genuinely empty; that interval component/squared-distance bounds are outward; and that sqrt_upper uses exact integer comparisons. The solver's split heuristic must never enter the trusted logic.
5. For portability, optionally emit a compact integer/rational split-tree certificate and write a separate **small, read-only verifier** that trusts only exact interval primitives and a proof of root coverage. An arithmetic script that reports success without emitted or independently reproducible terminal checks is insufficient.

**Exit:** exact reproducible arithmetic theorem plus complete written chart-to-original-proof audit; status X+V for this proper feature, no whole parent count change.

### Stage B — solve the weak-edge direct-triangle family FIRST, not every pose at once

Use original positive-edge labels A→B→C→A; x=a n_AB, y=b n_BC, z=c n_CA. By symmetry, choose a>=b>=c>0 and normalize W=1. Stage A makes c<1/12 a necessary condition. The THREE complete positive outside exit vectors are, with signs fixed,

    A: z−x,       B: x−y,       C: y−z.

Do not replace a small c by zero; instead use c in (0,1/12), and include c=0 only as an explicitly analyzed limit/closed enclosure with no missing boundary. The outside magnitudes are their actual positive norms; every original outside edge and its application remains present.

Maintain one exact original torque equation at **each** unloaded A,B,C, with the two unchanged internal applications and one unchanged outside application. For example, about an arbitrary point o_A in A,

    det(p_AB−o_A, x) + det(p_CA−o_A, −z)
      + det(q_A−o_A, z−x) = 0.

Analogous B,C equations are mandatory. Every edge application is simultaneously an actual common point of its two original squares and a maximum/minimum support point for its **selected** normal. A true common supporting normal and strict singleton convention must not be replaced by a convenient non-original normal.

First classify physically meaningful contact patterns, not arbitrary tiny angular bins:

- **T1, common physical junction:** separate all three original applications equal to P (existing limited H exclusion) from at least one actual shared-side application not equal to P. Include side means and both endpoints.
- **T2, no common physical junction:** three pairwise actual contacts can differ; distinguish point-only vertex contacts, shared-side face contacts, endpoints and supporting-normal-cone transitions.
- **T3, outside-terminal identities:** one outside square may be the selected terminal of multiple core hubs; separate identical from distinct actual terminals only if a proof really needs that split. Keep all nine real squares in every branch.
- **T4, frame/tie boundaries:** the complete parallel-core family is already reviewed and excluded; nonparallel and its frame-collision limits remain, with no artificial positive angular separation.

The labels above are thematic coverage families, **not** four pre-certified cases. A successful family exclusion must carry every relevant subfeature, force/moment equation, original mean and physical outside neighbor.

### Stage C — exact geometric encoding and solver exploration

For actual body i write S_i=c_i+[-1/2,1/2]u_i+[-1/2,1/2]v_i with u_i ⟂ v_i, |u_i|=|v_i|=1. Use exact rational half-angle charts for each orientation and for selected contact normals; split into finitely many charts to cover all angles and chart endpoints, including rotations and sign conventions. Within each chart, clear only strictly positive denominators before polynomial/rational reasoning.

For every one of the nine **actual** squares impose all four disk corner inequalities |corner−O|²<=Q. For every pair among nine impose genuine interior nonoverlap through the **disjunction** of the four square separating axes (two axes from each body), allowing exact boundary contact. For every originally positive pair additionally impose its true contact witness p in BOTH squares, support equalities in the given normal, and original strictness/mean variables; non-positive and zero-stress touching pairs are still geometrically nonoverlapping. Impose force, torque, positivity, every original circle multiplier and circle load where applicable; use ONE compatible selected stress, not unrelated branchwise stresses.

Use any practical numerical or interval optimizer to find approximate candidate contacts, helpful variable eliminations, and the strongest contradiction directions. Such search may guide pivots and branch order; a numerical infeasibility report or sampled angular grid is never a proof. Do **not** assume an uncertified solver has exhausted continuously variable orientations.

For proof, use exact rational branch-and-bound, real-algebraic sign certificates, SMT nonlinear arithmetic with checkable proof objects, or rigorous outward-rounded intervals plus verified transcendental enclosures. Make the rigorous checker independent of floating-point optimization; a terminating proof must cover every root chart and every legal contact and SAT disjunct, with the correct strict/non-strict boundaries. An unresolved box is a BLOCKER, not a contradictory box.

**Primary pruning inequalities:** original full-cut work and force-triangle screen; original point/support torque; actual outside unit points q+n; sharp square center bound; exact disk corner bounds; actual 9-square SAT and capacity; previously reviewed two-anchor, bypass, prism and parallel-frame theorems, only with their precise hypotheses.

### Stage D — convert the certified partition into a useful TABLE

Do not print thousands of unrelated pose boxes in the main proof. Merge leaves by a common **symbolic reason** and preserve a machine-checkable mapping from every original chart leaf to a table row.

A usable table row contains: original named parent/feature, all hypotheses including ties, a finite rational parameter region or a precise chart predicate, the original force/torque or disk/SAT inequality used to reject it, a rational *strict* margin where available, the exact checker/certificate identifier, and the original nine-body caller. A table is not a proof unless all rows cover the claimed parent and each rejection is verified without changing the original contact means.

Prefer 5–15 theorem-pattern rows over 100,000 handwritten leaves; the exact appendices may remain computational. A successful computer-assisted final proof is acceptable even when full hand elimination is impractical. Do not postpone parent closure merely to make a prettier table.

### Stage E — reintegrate all 17 remaining whole original cases

After closing the nonparallel direct triangle, use the common structural oracle against the **ten one-block parents**:

    C1.5.b2
    C1.6.b0, C1.6.b1, C1.6.b2
    C1.7.b0, C1.7.b1, C1.7.b2
    C1.8.b0, C1.8.b1
    C1.9.b0

and the **seven two-block parents**:

    C2.35.b1, C2.35.b2, C2.36.b1
    C2.45.b0, C2.45.b1, C2.46.b0, C2.55.b0.

Do not assume the direct triangle occurs in all 17 parents: independently identify the original caller for each. Next prioritize **C1.6.b0's 20 unresolved nested six-body exterior rows** as a *joint* nine-square/SAT completion problem and the seven mixed-side two-block parents under a single articulation/stress framework. Prefer a uniform cut>=4 theorem if it genuinely consumes many source parents at once; do not prune a four-edge full cut by deleting its fourth original force.

Each full parent changes from OPEN to C only after its entire named original domain has a complete certificate (hand, table-assisted or exactly computational), independent audit, all nine actual units/zero masks/loads/means preserved, and the canonical row(s) genuinely updated. Finally do a single-selected-certificate compatibility audit across all prerequisites and separately classify equality at Q.

## 3. Finite gates and anti-rabbit-hole rules

| Gate | Deliverable | Success criterion | Current |
| --- | --- | --- | --- |
| CA0 | Independent replay and mathematical audit of existing 4-root force screen | All chart roots, bounds and full-cut transfer checked; second verifier desirable | **X, review open** |
| CA1 | Exact full physical weak-edge triangle model | Original 3 hub stars, positive exits, normal/applications, all 9 squares, SAT/corners, all strict/tie branches encoded | **OPEN** |
| CA2 | Solver discovery on CA1 | Numerical candidate or bounded contradictions identify the dominating contact features; no claims of proof | **OPEN** |
| CA3 | Exact termination on all surviving T1–T4 families | Every box/disjunction has a verified contradiction or a precise equality/witness branch | **OPEN** |
| CA4 | Compressed mathematical table and original-caller join | Verifiable row coverage; audited shared means, terminals and zero-weight boundary cases | **OPEN** |
| CA5 | Other open parents with original nine-square completion | All 17 canonical parents closed, no phantom exclusions or lost genuine bodies | **OPEN** |
| CA6 | Global sharp theorem, all equality configurations, common-certificate audit | Complete necessity plus equality proof and independent end-to-end audit | **OPEN** |

An expensive subdivision that still has unresolved boundary boxes is partial research only. Before further subdividing a huge tree, inspect undecided boxes for a *single stronger derived inequality* that could eliminate an entire contact family. Track raw solver boxes separately from proved leaf coverage. Never infer all R²<Q from a run at Q−epsilon; work at closed Q or prove the exact limiting case. Commit coherent source, run information and new handoff together at every verified advance. Do not run Lean/Lake/CI.

## 4. Required session-end reporting

Report (i) exact parent SHA and new SHA; (ii) which complete original parent/fine IDs, if any, actually closed; (iii) exact computer statement with its quantifiers, root coverage, output and independent review status; (iv) surviving features with nonempty parameter domains, not an inflated arbitrary gate count; (v) one prioritized next experiment/inequality and the exact command to reproduce it. When a computation only reduces a proper feature, leave the canonical denominators unchanged.
