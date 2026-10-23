# n=9 — two-load reciprocal continuation: progress and exact evidence

**Date:** 2026-10-23 UTC. **Read base:** `a89802cd834aef3a96d9622bd4829a2c49df17fd` on PR #11. This continues QUADRANT_BLOCK_PROGRESS.md, ORIGIN_POCKET_PROGRESS.md and PROGRESS_LEDGER.md without rewriting their historical claims.

**Current global status:** unrestricted T9, P.ALL, Y.ALL and global equality necessity remain OPEN. The completion continuation below closes the entire six-body two-load capacity and reduces every five-body completion to P. Thus **P.ALL is now the only two-load completion obligation**. Global circle geometry leaves 3–7 noncollinear resultants in every remaining selected component. Of 58 coarse cyclic cells, two are closed and 56 remain open; these are bookkeeping counts, not proof-completion percentages. The full dependency chain still requires independent audit; no Lean compilation or CI was run.

## 1. Completed work and source provenance

| UTC, 2026-10-23 | Commit | Deliverable | Exact scope |
|---|---|---|---|
| 19:24:10 | [248202d](https://github.com/vltanh/lean4-squares-in-circles/commit/248202dba5d73d408f2a2f1d39ed06229fcbecb2) | TWO_LOAD_RECIPROCAL_RIGIDITY.md | Every physical positive component with exactly two circle-loaded bodies has parallel pair forces; no tree or simple-cycle assumption |
| 19:25:49 | [05e15a0](https://github.com/vltanh/lean4-squares-in-circles/commit/05e15a02a345b7311db90fc3643f876ee14666ae) | FOUR_BODY_CYCLIC_CELL_CLOSED.md | Every four-body biconnected positive component is excluded in the explicit radius window; completes the diamond load pattern |
| Subsequent clarification | [9fad28e](https://github.com/vltanh/lean4-squares-in-circles/commit/9fad28e5dd90011a454c4b1c743fc07fa3036cb7) | Correct section heading / residual domain | General two-load layers have abs(y)<1, NOT automatically the P slider domain abs(y)<=1/2 |
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

**Open at the earlier reciprocal checkpoint (superseded for five/six bodies by the continuation below):** P.ALL, Y.ALL, full five-/six-body parallel-core completions, all other open cyclic cells with their physical completion constraints, the explicit lower-window prerequisite in final assembly, unrestricted equality, independent full audit and Lean/integration.

**Next completion criterion:** use the new invariant to finish whole remaining load/adjacency families or a full physical completion theorem. Do not infer that a cell with >=3-loaded possibilities is closed from the two-load result, and do not turn the 58-cell ledger into 56 independent angle-grid searches.

## 7. Final rerun and ticked-roadmap synchronization

The identical source was rerun at **2026-10-23 19:44:32.616295–19:44:32.623763 UTC**, Python 3.13.5, exit 0. Its Git blob and SHA-256 were recomputed and matched again. All five physical examples passed, including the three-loaded control's nonzero reciprocal areas +4/3 and -4/3. The pinned committed JSON retains the original 19:32 run; this rerun is an additional regression, not an independent audit.

The following documentation commits synchronize all current entry points without changing the mathematical theorem scopes:

| Commit | Current artifact / checked state |
|---|---|
| 2d841b84c20b906e043a7ed71be0d551bb023089 | CYCLIC_CELL_LEDGER.md: C1.4.b0 checked, all 56 open rows retained |
| 6e674d0a03a19b60e71fe1d697eddc99f5892738 | DEEP_GATED_ROADMAP.md: nested TL.R / TL.P / TL.G contracts, residual capacities and audit gates |
| 40f9bb49e09810b41dfa3892b7a36fbbd9ff5d29 | G2_SUBGATES.md: new global two-load reduction and whole-cell status |
| 658cbfc476e110e228e8e315f943f47354c6ecd1 | ROADMAP.md: concise actual frontier and verification scope |
| 14b926dc5c0462e9a6a938be70988130dfaedd1a | README.md: current handoff; GitHub timestamp **2026-10-23 19:47:47 UTC** |

PR #11's title and body were updated after those commits, retaining **draft** status. No merge, CI, Lean build or independent mathematical audit was requested or performed. The unrestricted theorem and P/Y remain open; the finished result is one whole coarse-cell exclusion plus a general invariant spanning every two-loaded physical component. The unchanged upper-bound construction remains at Q.


## Completion continuation: every two-load completion now reduces to P

This section supersedes the earlier open five-/six-body status while preserving the historical record above.

| Commit | Complete hand result |
|---|---|
| [e4254b1](https://github.com/vltanh/lean4-squares-in-circles/commit/e4254b118da9b8383159182892a7309dd79531d7) | At most seven physical circle-touching squares in the declared window, using open arcs longer than pi/4 on the radius-5/4 circle |
| [52fec6f](https://github.com/vltanh/lean4-squares-in-circles/commit/52fec6f9e6258261bfe878a4d938e9473eb6cdc3) | Whole six-body two-load completion excluded: at most two arbitrary extras; includes new diagonal-center and cap-sign piercing lemmas |
| [1d28008](https://github.com/vltanh/lean4-squares-in-circles/commit/1d2800894e2261c0c3aa805b8b2980b849575e0f) | No common point of three circle-touching unit squares for R>sqrt(2) |
| [b46db3a](https://github.com/vltanh/lean4-squares-in-circles/commit/b46db3a27d0e8d261df4e43d9140dc07f8d91b54) | Whole five-body reduction and half-disk pair rigidity; every two-loaded nine-square completion contains actual family P |

### Six-body capacity

Every extra center lies between x=-1 and x=1. The doubled columns force it above or below the whole corresponding column; core barriers route it into y>=1/2 or y<=-1/2. The cap theorem gives at most two per side with opposite center signs. Two on one side force both opposite column heights beyond 1/2, excluding every extra on the other side. Hence at most two extras fit.

### Five-body reduction

Torque at the terminal adjacent to the singleton column forces that singleton height into [-1/2,1/2]. If a doubled-column height also lies there, an actual P skeleton is present. Otherwise the doubled heights lie strictly below -1/2 and above 1/2, forcing all added centers into the opposite open horizontal half-strip. After reflection, at most one upper extra fits by cap-sign piercing. A lower square crossing the axis would put its rightmost vertex strictly inside the lower doubled-column core, so all lower squares stay in the lower half-disk. Three there would have a close horizontal pair, forcing an excluded center on x=0. Thus this complementary branch has at most three extras.

### Exact remaining frontier and review

The six-cycle and theta examples are still physically valid cores; their completion to nine is excluded. Five-body cores are still valid; their completions are reduced to P. P.ALL remains open, and the proof does not turn the six-body exclusion into the closure of a coarse cell with other load counts.

The global resultant-direction continuation in CYCLIC_GLOBAL_CONTINUATION.md further shows that the remaining selected components have 3–7 loaded bodies with noncollinear resultants. Their exterior force polygon can have positive area, so the two-load zero-area proof does not force parallel channels there. P.ALL, Y.ALL, the remaining multi-load metric geometry, lower-window assembly, unrestricted equality and the full audit/integration chain remain open.

Separate reasoning passes checked the new cap inequalities, pair support minimum and equality, six-body coupling, singleton torque and five-body vertex routing. No numerical probe is used as a proof premise. No Lean compilation or CI was run in this continuation. These are hand proofs with local review, not a completed independent audit of the entire manuscript.


## Boundary graph continuation and exact method obstructions

Read base: 85cfcb6b31b7761c3c0c22112a9a28198694cfe2. The seven intervening imports since 2271166 were read before work resumed; they contain alternative proofs of already closed two-load results and do not add gate closures.

| Commit | Result and scope |
|---|---|
| [6f1d22e](https://github.com/vltanh/lean4-squares-in-circles/commit/6f1d22e9db8d546acfe1f094f70d6620c4838088) | Global circle-contact angular order and shadow proof; positive components consisting entirely of circle-touching bodies reduce to C7. Also records the exact regular C7 witness/capacity and the additive-measure impossibility theorem. |
| [411924d](https://github.com/vltanh/lean4-squares-in-circles/commit/411924df56b00d9f0e6a73bca86c9712b012b0ea) | Corrects one expanded local coordinate in the ring witness: (C_(j+1)−C_j)·u_j=−2sd, so the side contact coordinate is xi=1/2−cos(2delta), in(−1/2,0). The global contact definition, force/torque identities, radius and capacity remain unchanged. |

### Finished universal implication

CIRCLE_CONTACT_ANGULAR_ORDER.md proves the narrow center annulus, >36-degree separation of distinct circle-touching centers, <72-degree span of contacts, and the <60-degree angular shadow of every circle-touching square. Hence the full physical circle-touching graph is paths or one C7. Any positive component with all bodies circle-touching and at least one positive circle multiplier has no leaves: an unloaded leaf fails force balance; a loaded leaf would require a radial contact, excluded geometrically for R>3/2. Thus it is C7 and every other physical square is circle-clear. This reduction allows zero circle multipliers on some boundary bodies.

### Exact examples and method limits

SEVEN_LOADED_RING_COUNTEREXAMPLE.md gives radius R=cos(pi/7)+1/(2sin(pi/7)), with 79/40<R<103/50 and R²<17/4. Every neighboring contact is a genuine side/vertex contact; all other pairs are strictly separated; normalized positive circle and contact multipliers satisfy force and torque. Any origin-centered unit square fits as an eighth. For arbitrary added-square positions and orientations, the seven center disks exclude all additional centers of radius at least 1/2, proving at most one added square.

ADDITIVE_MEASURE_OBSTRUCTION.md proves a fractional packing of total mass 181/20 using rotational orbits of three explicit squares in D_(17/4). Pointwise angular occupancy is at most one. Tonelli's theorem therefore forces any nonnegative Borel measure assigning at least one to every square interior to have total mass at least181/20>9. This rules out the entire independent-square additive measure route, not merely one numerical weighting choice.

### Review and execution scope

The angular-order/shadow derivation and ring covering inequalities received separate hand review. A further global-coordinate check caught the ring expansion sign error after the first commit; the immediate correction above preserves that audit trail. The additive-measure proof received a separate full reasoning pass, including all angular branch and atomic-measure endpoints.

An exact Fraction evaluation reproduced the three angular-rectangle values 5/8,1341/1600,3721/4000 and the ring covering values 7/20,1597/1600,17/25,3893/8000. It also checked the positive rational gaps in the sine and tangent estimates for the additive-measure proof. These finite arithmetic checks supplement the displayed hand arguments; they are not a proof of the unrestricted packing theorem.

Exploratory sampled linear programs and square-pose searches guided or rejected candidate arguments. They are not premises of any committed theorem. In particular, a sampled half-pocket measure of total three is not a universal certificate. No Lean compilation or CI was run.

### Remaining work, with unchanged whole-cell count

P.ALL and Y.ALL remain open. The general C7 completion with two arbitrary circle-clear squares remains open, as do components containing a circle-clear body. The regular-ring capacity is not extrapolated to arbitrary rings. The count remains two whole coarse cells closed and 56 open, with the unrestricted radius, equality, lower-window assembly, independent full audit and Lean/integration obligations unchanged.


## 2026-10-23 23:53 UTC — complete 135-degree pocket and quantitative path tools

Base commit: `c510ed141bfcabd8f707012245acf9a302fcb2be`.

- **CLOSED WEDGE.2:** `WEDGE_135_CAPACITY_ONE.md` exhausts both owners and all pair-normal angles, using the two terminal frames. Every screened pocket of aperture at most 135 degrees has capacity one.
- **CLOSED analytic inputs:** `OWNED_AXIS_TERMINAL_CAP_EXCLUSION.md`, `POSITIVE_NORMAL_CAP_FLOOR_EXCLUSION.md`, and `RIGHT_OWNED_DOWNWARD_SEPARATOR.md`. These use direct support inequalities, concavity, completed squares and explicit polynomial identities; no interval-cover or generated coefficient table is a proof premise.
- **CLOSED sharp high-center bound:** `HIGH_CENTER_COMMON_POINT.md` proves that every square with center height greater than 3/sqrt(5) contains (0,sqrt(5)/2) strictly. The reflected radial pair proves sharpness.
- **CLOSED quantitative terminal cap:** `TERMINAL_CAP_SECTION_EXCLUSION.md` proves the all-orientation cap bound at 19/120; the complementary center threshold 161/120 exceeds 3/sqrt(5) by the exact comparison 25921>25920.

The cap proofs and high-center theorem received separate reasoning audits; the quantitative adapter's displayed polynomial identities and endpoint values were also checked with exact rational arithmetic. A zero-coordinate separator boundary was corrected before committing: the up-right normal (0,1) gives a weak floor at y=1/2, already covered by the cap theorem.

**Unchanged open parents:** P.ALL, Y.ALL, arbitrary positive C7 completion, mixed 3–7-load components, unrestricted radius and equality classification. The general annular same-sign pair statement is not inferred from the 135-degree reflection argument. Two coarse cells remain closed and 56 open. No Lean compilation or CI was run.
