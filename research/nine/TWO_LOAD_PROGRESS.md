# n=9 — two-load reciprocal continuation: progress and exact evidence

**Date:** 2026-10-23 UTC. **Read base:** `a89802cd834aef3a96d9622bd4829a2c49df17fd` on PR #11. This continues QUADRANT_BLOCK_PROGRESS.md, ORIGIN_POCKET_PROGRESS.md and PROGRESS_LEDGER.md without rewriting their historical claims.

**Global status:** unrestricted T9, P.ALL, Y.ALL and global equality necessity remain OPEN. A NEW universal two-loaded-component hand theorem closes the **entire** coarse cyclic cell C1.4.b0 and restricts two-loaded configurations across every other cell. Of 58 coarse cells, two are now closed and 56 remain open. These are bookkeeping counts, not proof-completion percentages. The new general arguments require independent audit; no Lean or CI was run.

## 1. Completed work and source provenance

| UTC, 2026-10-23 | Commit | Deliverable | Exact scope |
|---|---|---|---|
| 19:24:10 | [248202d](https://github.com/vltanh/lean4-squares-in-circles/commit/248202dba5d73d408f2a2f1d39ed06229fcbecb2) | TWO_LOAD_RECIPROCAL_RIGIDITY.md | Every physical positive component with exactly two circle-loaded bodies has parallel pair forces; no tree or simple-cycle assumption |
| 19:25:49 | [05e15a0](https://github.com/vltanh/lean4-squares-in-circles/commit/05e15a02a345b7311db90fc3643f876ee14666ae) | FOUR_BODY_CYCLIC_CELL_CLOSED.md | Every four-body biconnected positive component is excluded in the explicit radius window; completes the diamond load pattern |
| Subsequent clarification | [9fad28e](https://github.com/vltanh/lean4-squares-in-circles/commit/9fad28e5dd90011a454c4b1c743fc07fa3036cb7) | Correct section heading / residual domain | General two-load layers have |y|<1, NOT automatically the P slider domain |y|<=1/2 |
| Source committed before the pinned run | [0d4c958](https://github.com/vltanh/lean4-squares-in-circles/commit/0d4c9588b974a2ce986a077a10036013e7f1f164) | check_two_load_reciprocals.py | Exact standard-library finite regressions; source matched to the Git blob before execution |
| 19:32:40.835172–19:32:40.842767, actual execution | source 0d4c958 | Pinned local run | PASS, Python 3.13.5, exit 0 |
| Report record/correction | [4843058](https://github.com/vltanh/lean4-squares-in-circles/commit/48430583e24c30192ab2b4683574de8125833e20) | TWO_LOAD_RECIPROCAL_EXACT_CHECK.json | Correct report data; repairs an initial manual transcription of the three-loaded control's areas to +4/3 and -4/3 |

The already committed ACUTE_LOADED_CONTACT_GRAPH.md (`690f245`) and PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md (`a89802c`) are inputs. Their four-cycle exclusion is not counted again as a new result.

## 2. New theorem: force-polygon area, not another angle window

At the physical contact-point incidence graph, each body and each contact junction has a force polygon whose edge directions follow the planar cyclic order. For square corners this uses the equality between the inward tangent quadrant and the negative outward normal quadrant. Adjacent loaded circle atoms can be replaced by their resultant through an empty exterior cap, preserving the cyclic order.

With exactly two loaded bodies, add one exterior vertex with two opposite resultant-load edges. A face-potential integration gives globally glued reciprocal force polygons. Their signed areas cancel pairwise over the primal edges. Every finite polygon has nonnegative area; the two-edge exterior polygon has area zero. Therefore every polygon is degenerate and all aggregated forces are parallel.

A separate extreme-ray argument at three/four-body junctions recovers parallelism of **each original pair force**, not just its aggregate. This is proved without assuming the body-pair graph planar or equating the 19-term translational stress with the 27-atom physical force/torque certificate.

**Research-window consequence:** for 79/40<=R<=sqrt(Q), every two-loaded component has q=17/4, two radial side-normal loaded endpoints at (+/-3/2,0), and axis-aligned unloaded bodies in the two layers x=+/-1/2. Every directed endpoint-to-endpoint path has exactly two internal squares. The strict point-contact normal convention limits each layer to at most two bodies, hence total component size is 4, 5 or 6. All two-loaded 7–9-body components and all triangle-containing two-loaded components are excluded.

**Important nonclaim:** five- and six-body two-loaded cores can genuinely branch or have cycles. Their inner heights need not lie in [-1/2,1/2]; their remaining-square capacities are open. The four-body case is P, but a larger component is not silently reduced to P.ALL by choosing an arbitrary path.

## 3. Entire coarse cell C1.4.b0 now closed

The exhaustive four-body biconnected simple graphs are C4, the diamond K4-e, and K4. The channel theorem already excluded all C4 load patterns; the loaded-noncontact rule excludes K4. For the diamond it leaves only the two nonadjacent tips loaded. The new parallel-force theorem excludes that residual: three positive contacts cannot form a triangle of pairwise touching, pairwise interior-disjoint positive-length projection intervals.

This is a complete cell exclusion for **all** square orientations, contact points and load allocations, regardless of the five other physical squares. It is not a sample adjacency or a small perturbation theorem.

## 4. Pinned finite execution

Committed script: `research/nine/check_two_load_reciprocals.py`, commit `0d4c9588b974a2ce986a077a10036013e7f1f164`.

- Source Git blob SHA-1: `1c379f90967ff5f36d5b1a54cbc1a1eb4ecbc1f3`.
- Source SHA-256: `3398c22593628d4c0253e76bfd9a7639b7e507a08d80da7ff20d758402d81a1c`.
- Actual run: 2026-10-23 19:32:40.835172–19:32:40.842767 UTC, Python 3.13.5, exit 0.
- Report: [TWO_LOAD_RECIPROCAL_EXACT_CHECK.json](TWO_LOAD_RECIPROCAL_EXACT_CHECK.json); compact formatting preserves the executed values.

```sh
python check_two_load_reciprocals.py \
  --source-commit 0d4c9588b974a2ce986a077a10036013e7f1f164 \
  --output TWO_LOAD_RECIPROCAL_EXACT_CHECK.json
```

The checker uses exact Fraction arithmetic and a rational polar-order comparator; no floating angles, optimizer or external packages.

**Passed finite checks:**
- 12 exact radius/window comparisons;
- all 64 labelled simple graphs on four vertices, recovering exactly three labelled C4 graphs, six diamonds and one K4 as the biconnected cases;
- every loaded subset of each such graph, with the precise surviving noncontact patterns (two opposite C4 vertices or two nonadjacent diamond tips);
- five complete physical square/stress examples, each with all corners, all true pairwise SAT tests, every genuine force point, exact center/torque equilibrium and normalized circle load;
- planar incidence rotation systems, Euler characteristic, exact dual face-potential integration, signed-area cancellation and weak convexity of every finite force polygon.

## 5. Negative controls and scope safeguards

1. **Three loaded bodies:** a nonaligned physical Y core has finite reciprocal area +4/3 at its unloaded branching body and exterior area -4/3. Its pair forces are not parallel. Thus the two-loaded premise cannot be dropped.
2. **Wrong cyclic order:** an abstract planar balanced vector graph with two exterior edges has two opposite finite polygon areas, -1 and +1. It violates the physical cyclic-direction hypothesis. Equilibrium and area cancellation alone do not imply parallelism; the square-specific ordering proof is essential.
3. **Nonzero channel heights:** a physical two-loaded six-cycle with inner centers at (+/-1/2,+/-3/5) satisfies every exact physical and force/torque test. No inner center lies in the original P slider range. Therefore choosing a channel does not automatically produce a P skeleton.
4. **Not just simple cycles:** a six-body two-loaded theta graph with seven positive contacts is physically realizable and has zero force-polygon areas. The new theorem does not misclassify it as a simple cycle or exclude the core instead of its completion.
5. **Five-body cyclic component with bridge:** an exact example is retained; larger coarse cells are not marked closed merely because two-loaded four-body components are excluded.

## 6. Audit priorities and next actual theorem

Independent review must check the physical junction direction order, replacement of adjacent circle atoms by an exterior port, face-potential existence for repeated faces/degenerate polygons, and recovery of pair normals from junction aggregates. These are the analytic proof's critical steps; finite regressions do not certify them generally.

**Still OPEN:** P.ALL, Y.ALL, full five-/six-body parallel-core completions, all other open cyclic cells with their physical completion constraints, the explicit lower-window prerequisite in final assembly, unrestricted equality, independent full audit and Lean/integration.

**Next completion criterion:** use the new invariant to finish whole remaining load/adjacency families or a full physical completion theorem. Do not infer that a cell with >=3-loaded possibilities is closed from the two-load result, and do not turn the 58-cell ledger into 56 independent angle-grid searches.