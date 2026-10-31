# PR #11 — pushed handoff and exact restart point (2026-10-28 UTC)

**PR:** https://github.com/vltanh/lean4-squares-in-circles/pull/11 (draft)  
**Branch:** `research/nine-tablefree-hand`  
**Substantive proof head before this metadata handoff:** `0b90e9a6addc3db8d27ce3263c6ffcdcf4e3d388`  
**Goal:** rigorous sharp nine-square packing proof and equality classification, ultimately integrated into Lean.  
**This file:** handoff-only; no new proof, checklist change, prerequisite audit or Lean verification is asserted.

## 1. Accepted inventory, exact unchanged original IDs

- **34 of 58 original coarse cells closed; 24 open.**
- **2,339 of 2,513 original fine obligations checked; 174 open.**
- These counts are inventory counts, **not estimates of remaining proof work**.
- The unrestricted sharp inequality `R² >= 1105/256`, complete original equality-packing classification, remaining end-to-end prerequisite audit and Lean integration are **OPEN**.
- The accepted hand proofs have had root and separately independent reviews at recorded source pins, but **Lean has not been compiled and CI has not run**.

The latest accepted checkpoint is
[`TWO_THETA_D_FAMILIES_AND_NEAR_BODY_BLOCK_CHECKPOINT_2026_10_28.json`](TWO_THETA_D_FAMILIES_AND_NEAR_BODY_BLOCK_CHECKPOINT_2026_10_28.json).
For exact source hashes, reviews, original-ID edits and the complete open-ID inventory, start there. The detailed chronological
[`HANDOFF_PR11_2026_10_28_CURRENT.md`](HANDOFF_PR11_2026_10_28_CURRENT.md),
[`CYCLIC_CELL_LEDGER.md`](CYCLIC_CELL_LEDGER.md) and
[`DEEP_GATED_ROADMAP.md`](DEEP_GATED_ROADMAP.md) are authoritative.
**Read the newest sections first**; earlier historical checkpoints have superseded counts.

## 2. Work already committed; do not redo

Four accepted continuation checkpoints after `cc143bb` closed:
- **Entire `C1.4.b3` cell:** all 24 original four-block/three-bridge placements, including the last H4/K4/B3/C2 three-leaf diamond's full parallel-tip branch. The fresh complete assembly
  [`THREE_GENUINE_LEAVES_DIAMOND_FRESH_COMPLETE_EXCLUSION.md`](THREE_GENUINE_LEAVES_DIAMOND_FRESH_COMPLETE_EXCLUSION.md)
  is present at blob `f6d32efd2386b352b2f67b8f781ab729538376a4`, and the full original cover and full join reviews are retained.
- **Entire `C2.44.b2` cell:** all 21 original rooted-type pairs and all strict/critical and physical-interface cases, including actual higher-degree hub forces and variable side applications.
- **20 original fine obligations:** fourteen original house/hub/lower/pentagon items, the independent nine-square `W.3` lower window, three D-leaf house/fan cases, then `M6.B5L.FAN.INNER.L134.D` and `M6.B5L.HOUSE.HUB.LTCB.D`. No invented fine IDs.
- **Uniform zero-count implications:** fixed D-root radius-3/125 near-body limit, near-origin access transfer to outside cyclic blocks, arbitrary-degree S-root moment/port order, D-root exclusion of separate leaf-bearing blocks, high-radius `C2.35.b2` private-D and clear-near-body reductions, unloaded opposed-moment-star theorem, and the earlier complete geometric kernels.

For `W.3`, the independent same-nine analytic radial measure proves `R>2>79/40` from arbitrary containing radius. For the two latest D-family closures, the real theta boundary-order obstruction forces root margins above 1/4; eight *actual* other square interiors then intersect the radius-5/4 circle in disjoint arcs longer than pi/4. These claims are hand proofs, not kernel-verified Lean theorems.

Accepted continuation commits: `53d3265`, `1adc352`, `66a9b30`, `0b90e9a`. The latest commit's 47 changed files were verified against their Git blob hashes, with 3,333 earlier files unchanged. The original 58 and 2,513-label inventories remain unaltered in cardinality and order.

## 3. Full remaining coarse-cell inventory

| Positive bodies inside the SAME nine-square packing | Open original cells |
| --- | --- |
| 6 (2) | `C1.5.b1`; `C1.6.b0` |
| 7 (4) | `C1.5.b2`; `C1.6.b1`; `C1.7.b0`; `C2.35.b0` |
| 8 (7) | `C1.5.b3`; `C1.6.b2`; `C1.7.b1`; `C1.8.b0`; `C2.35.b1`; `C2.36.b0`; `C2.45.b0` |
| 9 (11) | `C1.5.b4`; `C1.6.b3`; `C1.7.b2`; `C1.8.b1`; `C1.9.b0`; `C2.35.b2`; `C2.36.b1`; `C2.37.b0`; `C2.45.b1`; `C2.46.b0`; `C2.55.b0` |

Six-body `C1.5.b1` retains **ten whole original house/fan S/D families in nine load orbits**:
house roof `AC.S`, `ABC.S`; house hub `TC.S`, `TCB.S`; house lower `TD.S`, `TAC.S`, `TDC.S`, `TDC.D`; fan `endpoint234.S`, `inner134.S`. All five original house/fan rooted parent types still have open alternatives.

Six-body `C1.6.b0` retains positive-chord outer-hexagon domains and **five** inner-pentagon masks:
`H3.L024`, `H3.L1234`, `H3.L0124`, `H4_D0.L124`, `H4_D0.L0124`.
The complete H2_D0 graph is closed.

## 4. Most local unresolved domain — house lower `TDC.D`

The only remaining house/fan D-leaf family is `M6.B5L.HOUSE.LOWER.LTDC.D` (consult the original ledger for its exact spelled ID). The accepted unloaded-star result eliminates all original cases except strict high radius and actual B-to-A support
`0 < h <= epsilon < 1/60`.
After a single whole reflection the unresolved physical domain satisfies

```
0 < a <= epsilon < 1/60
b = 1 - a > 59/60
n_y > 19/20, |n_x| < 1/20
0 < h_B(n) <= epsilon
actual loaded C normal points strictly downward.
```

**The weak endpoints `h=epsilon` and `a=epsilon` remain open.** Actual D-root degree B3, unloaded A3, and loaded T/D/C degrees 2/3/2 must remain. Nothing proves an A–C contact, that A is physically clear, or that it meets the near-origin disk. The theta proof cannot simply be transplanted without a literal second boundary page. Completing this full original S/D/root/three-extra domain earns one original fine check only, not the whole C1.5.b1 cell.

## 5. Prioritized next proof work (no partial-cell promotion)

1. **Try to close all of `TDC.D`**, including the thin support endpoints, using full original force/torque at unloaded A3 and loaded B3/T2/D3/C2, the fixed-D-root near-body theorem and protected physical boundary paths. If this attempt fails, record a precise blocker rather than asserting closure.
2. **Attack all nine remaining S house/fan alternatives with a common lemma**, preserving the actual rooted house/fan graph, all side-mean ranges and arbitrary three completion squares. Seek a whole-domain statement that handles several load orbits together, not a succession of isolated sample parameters.
3. **Finish five inner-pentagon masks and outer-hexagon positive chords**, including every original block-load orbit and mask, to close `C1.6.b0`. Reuse the accepted pentagon localization only under its actual physical premises.
4. **Apply the accepted D-root separate-block/near-unit results to bigger cells**, particularly the still-open original `C2.35.b2` and `C2.36.b1`. The C2.35 proof currently excludes only necessary subdomains; the remaining oblique/nonparallel and non-clear forms require complete separate treatment.
5. After whole-domain lower-bound coverage, **audit original scalar prerequisites and classify every equality packing**; only then draft/integrate Lean while preserving the hand-proof contract.

## 6. Strict invariants and review protocol

Every argument is about **all nine original physical unit squares**; the 'six-, seven-, eight-body' tags mean positive-force component sizes, not theorems for fewer squares. Keep all arbitrary completion squares, true positive degrees, **all** original normal forces and torque balances (including every shared hub edge), compatible pre-extraction normal selections, real shared side means across their full intervals, disk masks, strict/weak and coincident endpoints, and individual zero contact weights. Never infer that a zero-force neighbor is physically absent, or that a unit avoiding O avoids the `epsilon` disk.

Promote an original checkbox **only** after its whole original graph/load/radius/physical/completion domain has a complete source, root review, independent review and exact ledger join. Do not subdivide or renumber 2,513 IDs. A uniform theorem that closes a proper necessary subclass receives zero additional coarse/fine checkbox credit.

**Execution history and scope:** GitHub connector commits/pushes only; no local checkout or extra unpublished working files were present at this handoff. The already-created `f6d32...` three-leaf diamond blob is verified *reachable in the substantive branch tree*. This file only records the current pushed state. No Lean build, CI dispatch, workflow run or merge was performed. PR stays draft.

## 7. Fast restart

1. Read this handoff; the latest exact [checkpoint](TWO_THETA_D_FAMILIES_AND_NEAR_BODY_BLOCK_CHECKPOINT_2026_10_28.json) and latest [chronological handoff](HANDOFF_PR11_2026_10_28_CURRENT.md).
2. Re-read live PR head before edits and verify pinned dependency file versions.
3. Work first on `TDC.D` and the nine S house/fan alternatives; prefer a full reusable physical theorem.
4. Save each completed source and independently reviewed original-domain join, then update only the existing original checklist lines with exact checkpoint hashes.
