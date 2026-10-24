# n=9 — two-load reciprocal continuation: progress and exact evidence

**Date:** 2026-10-23 UTC. **Read base:** `a89802cd834aef3a96d9622bd4829a2c49df17fd` on PR #11. This continues QUADRANT_BLOCK_PROGRESS.md, ORIGIN_POCKET_PROGRESS.md and PROGRESS_LEDGER.md without rewriting their historical claims.

**Current global status, October 23, 2026, America/Chicago:** P.ALL, Y.ALL, TREE.ALL, TL.COMPLETE and the entire C1.3.b1 triangle-plus-leaf cell are CLOSED hand. The selected physical certificate has one planar positive cyclic component of 5–9 bodies, with all other physical bodies retained. The unrestricted lower bound and complete equality necessity remain OPEN: general C7 completion and the remaining mixed cyclic cells are unresolved. Three whole coarse cells are closed and 55 remain open. The entire length-two-arm layout of C1.3.b2 is also excluded; the C4-plus-leaf inner hole is empty; all five-body biconnected graphs reduce to C5, house and fan with complete necessary load masks. C7 now has a complete simultaneous selection excluding every free vertex edge; its full all-owned capacity problem remains. Same-articulation S/S and D/S leaves and the adjacent-load C4 branch are also excluded. These do not close their larger parent cells. Historical entries below preserve their checkpoint claims; later entries supersede them. Full-chain audit and Lean integration remain unfinished; no Lean compilation or CI was run.

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


## 2026-10-24 00:07 UTC — P.ALL and Y.ALL complete; all trees and two-load components excluded

Base commit: `482ef277981c7898797a8df6b0e78e1100192924`.

### Complete physical capacity theorems

- **P.ALL CLOSED:** `P_ALL_COMPLETION.md` covers every slider pair in the closed square [-1/2,1/2]^2, every extra-square orientation, and every physical separator. The proof routes extras into two half-pockets of capacity three. A putative noncanonical upper triple contains a small inner square whose lower vertical-axis section is below 19/120. Both slider tops are at most that section height, so every lower extra has center below -161/120<-3/sqrt(5) and contains the same interior point. A canonical upper triple also leaves at most one lower extra. Thus five extras are impossible.
- **Complete local dependencies:** `P_HALF_POCKET_SECTION_PROOF.md` proves the y=1 section theorem and capacity three; `LOW_OUTER_SQUARE_MEETS_N_DISK.md` and `HIGH_OUTER_SQUARE_MEETS_N_DISK.md` prove strict intersection with the open north disk; `ANNULAR_SAME_SIDE_PAIR_EXCLUSION.md` exhausts all pair directions without an orientation or separator-owner restriction.
- **HALF.3 CLOSED:** `HALF_POCKET_TRIPLE_RIGIDITY.md` proves that every upper E/W triple is exactly the canonical aligned triple. The decisive inequality x<(q/p)(1/sqrt(2)-y), forced by the right neighbor of a small inner square, makes every direction toward the left neighbor impossible. Widening and the equality classification give capacity two for every screened pocket of aperture strictly below 180 degrees. This theorem also supplies a shorter independent P completion assembly; the quantitative proof is retained in full.
- **Y.ALL CLOSED:** `Y_ALL_COMPLETION.md` uses the actual core and terminals to screen three full rays, including origin and endpoints. Each whole extra square belongs to one pocket; the occupied K quadrant has no extra slot. The two remaining apertures sum to 270 degrees and are each strictly below 180 degrees. Their capacities are one and two, excluding four extras for every alpha/theta in the complete open parameter rectangle. Angular endpoints reduce to the closed P family.

### Exact structural consequences

`TREE_AND_TWO_LOAD_COMPLETION.md` assembles two complete implications in the explicit window 79/40<=R<=sqrt(1105)/16:

1. No selected positive component can be a tree, even if another component has cycles. The exhaustive six-profile cover reduces its former survivors to P or Y, both now excluded from nine-square completion. All six original tree rows are closed.
2. No selected positive component can have exactly two circle-loaded bodies, including cyclic components. Reciprocal rigidity leaves four, five, or six aligned bodies at q=17/4. Four bodies give P; five bodies reduce to P or total capacity eight; six bodies already have total capacity eight.

The lower-window prerequisite is retained as a prior-theorem dependency and is not claimed to follow from these capacities.

### Review and exact scope

The parent P argument and annular-pair theorem received independent complete hand audits, including zero horizontal coordinate, both slider constraints, all separator directions and the exact threshold comparison 25921>25920. The section and disk-intersection manuscripts received separate all-case review. The HALF.3 manuscript received two separate hand audits of its frame formulas, two factorizations, strict endpoint inequalities, north-disk routing and wedge-widening consequence. The Y and structural assemblies were checked against the actual physical screen and earlier component reductions.

These are analytic proofs; exploratory numerical searches are not premises. No Lean compilation, CI, or new finite sampling certificate is claimed. The complete prerequisite chain still needs a full independent audit and subsequent formalization.

### Remaining global obligations

Every surviving selected component is cyclic with 3–7 noncollinear loaded resultants. A boundary-only component is the general physical C7, whose two-circle-clear-square completion remains open. Mixed components containing a circle-clear body also remain open. The unrestricted lower bound, all equality necessity, explicit lower-window assembly, full-chain audit and standard-kernel integration remain unfinished. The coarse cyclic ledger is still two whole cells closed and 56 open; tree and two-load closure is not used to tick a cell with unresolved multi-load realizations.


## 2026-10-24 00:13 UTC — explicit lower-window dependency assembled

Base commit: `1760270deb45190883a23fb54a064a812a6bed6b`.

`LOWER_WINDOW_FROM_EIGHT.md` supplies the exact declared R>=79/40 prerequisite for every physical nine-square packing. Deleting one square preserves the original Packing semantics. The actual existing `SquaresInCircles.optimal_radius 8` theorem then gives R>=EightStatement.radius; `StatementLink.selected_stationary.q_lower` and the stated square-root definition give EightStatement.radius>=79/40. The source declarations were read at the pinned base commit, including the direct `Eight.lower_bound` alternative and the statement/proof radius link.

This closes G0.W.2 as an explicit imported-theorem assembly. It does not replace the n=8 arithmetic-table dependencies: the actual Analysis import includes Generated.LocalStationaryBounds, and the normalization/capture chain has further generated bounds. G0.W.3 remains separate if a fully standalone table-free hand lower bound is required. The direct P/Y capacities use only their own q=17/4 geometry.

No Lean compilation or CI was run. General C7 completion, mixed cyclic completion, unrestricted sharpness/equality and full-chain verification remain open; no cyclic cell count changes.

### Additional complete geometric input — centered forty-degree arcs

`CENTERED_INNER_ARC.md` proves that every circle-touching square in the full declared radius window contains the entire closed arc of |p|=5/4 within 20 degrees of its center direction in its OPEN interior. The exact trigonometric comparisons are cos(pi/9)>15/16 and sin(pi/9)<11/32. Both own-coordinate deviations reduce to a cubic whose expansion about s=3/8 has the positive lower bound 117/40960. Consequently every pair of physically disjoint circle-touching squares has minor center-angle separation strictly greater than 40 degrees.

The entire derivation received two independent hand audits, including all constants and the shifted-cubic certificate. It strengthens the earlier 36-degree necessary bound but does not by itself exclude either global cyclic completion class.


## 2026-10-24 — all nine-body simple positive cycles excluded

SIMPLE_POSITIVE_CYCLE_BODY_BOUND.md supplies a complete hand theorem in the declared radius window. A selected simple positive component has at most eight bodies. Its strict point-only vertex/vertex normal convention is the one already available from the physical stress construction.

- [x] Exact top-cap contact bound at 7/10.
- [x] Full four-square-junction crossing exclusion, including the remaining axis-position block case.
- [x] Local noncrossing replacement, Jordan cycle and exterior attachment paths.
- [x] Circular center order through disjoint paths in the radius-5/4 annulus.
- [x] Channel bounds for zero, one and two clear transmitters, giving more than 40 degrees per cycle body.
- [x] Two separate hand audits covered the inequalities, degeneracies and topology.
- [ ] Smaller-cycle completion and branching cyclic components remain open.

This is a whole simple-cycle cardinality theorem, not a closure of the entire nine-body biconnected cell. All 56 currently open coarse rows remain unchecked. No Lean compilation, CI or numerical premise is used.


## 2026-10-24 — full boundary-cycle force geometry and exterior-pocket exclusion

C7_FORCE_POLYGON.md proves that every all-boundary positive seven-cycle has an embedded convex polygon whose vertices lie in its actual squares and whose edges follow the physical contact forces through their true application points. A loaded vertex is radial to its circle resultant; a zero-load body contributes a straight transmission vertex. The complete one-/two-circle-corner normal-cone analysis and the winding/convexity argument received an independent hand audit.

C7_COMPLETION_LOCALIZATION.md proves that every extra square lies inside this polygon. The center/contact Jordan curve and one circle spoke per body bound seven exterior cells. Within any occupied exterior cell, dilating all extra centers about the two boundary bodies' common point strictly preserves obstacle separations and preserves every mutual separation. Until first circle contact the cell confines the motion. The resulting eighth circle-touching body contradicts the universal budget. A homotopy within the ring bodies then transfers winding to the convex concurrence polygon. Two separate full hand audits passed.

- [x] CY.C7.POLYGON: whole positive boundary-cycle structural theorem.
- [x] CY.C7.LOCALIZE: all exterior pockets empty; every completion square is contained in the concurrence polygon.
- [ ] CY.C7.COMPLETE: the two-square capacity inside that polygon remains open.
- [ ] CY.MIXED.COMPLETE: cyclic components with circle-clear bodies remain open.

No coarse cell is marked closed by these necessary conditions. The unrestricted sharp theorem and equality necessity remain open. No Lean compilation, CI, numerical search or certificate table is a premise of either new theorem.


## 2026-10-24 01:02 UTC — planar physical certificate and unique positive component

PHYSICAL_BODY_GRAPH_UNCROSSING.md proves existence of a physical certificate whose positive body-pair graph is planar and all physical circle-touching positive vertices lie on the exterior face. Compatible strict normals at a four-square junction permit an exact uncrossing identity at the same actual contact point, preserving each body's force and torque. The added forces are original shared-side endpoint rows. Thinning only the surviving atoms restores the 27-atom bound without adding a removed crossing; aggregation retains the graph. Optional finite normal avoidances remain available.

UNIQUE_POSITIVE_COMPONENT.md attaches every positive circle corner as a boundary port of that embedding. Jordan crosscuts rule out alternating port sets of different components. Each balanced component has all consecutive port gaps at most pi; another component's ports would lie strictly in one gap and could not balance. This includes two antipodal ports. A virial sum excludes a positive contact component without circle weight. Thus there is exactly one positive component, and every other square has zero stress.

- [x] CY.PLANAR: complete construction, root and separate independent hand audit.
- [x] CY.UNIQUE: complete global uniqueness deduction, root and separate independent hand audit.
- [x] CY.ZERO: all other physical squares retained as zero-stress completion bodies.
- [ ] CY.SHARP: C7 capacity and mixed cyclic completion remain open, including the four-body triangle-plus-leaf cell.

No universal claim about arbitrary physical body graphs is made. The selected unique component has 4–9 bodies and 3–7 noncollinear loaded resultants in the declared window. The coarse cell count remains two closed and 56 open. No Lean compilation or CI was run.


## 2026-10-24 — uniform contact-ring hole capacities and empty boundary-pair pockets

CONTACT_RING_HOLE_AREA.md proves the complete bound `area(H) <= (k/4) cot(pi/k)` for every physical Jordan contact ring with 3<=k<=6, without a containing-radius assumption. Contracting each center/contact path inside its actual square gives a limiting contact polygon with winding only zero or one. A chord of length l>1 leaves an occupied inward square piece of area at least `sqrt(l*l-1)/2`; these pieces must be subtracted before counting completion area. A finite exact Fourier identity bounds signed polygon area by `cot(pi/k)/4` times the sum of squared edge lengths. The one-variable contribution is maximized at l=1 for k<=6. Thus three-, four-, five- and six-body rings have interior unit-square capacities 0, 1, 1 and 2 respectively.

CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md proves that an exterior pocket of any touching pair of circle-boundary squares is empty in the declared window. Every circle corner is within 20 degrees of its body's center direction, preserving circular order. Dilation of all pocket squares away from the pair's shared point preserves actual separations until one first touches the circle; its intervening center direction contradicts the angular-neighbor rule. A separate direct contact-triangle argument is also included.

- [x] CY.HOLE.3-6: full continuous-domain interior capacities, with separate root and independent hand audits.
- [x] CY.OUTERPAIR: full exterior boundary-pair pocket exclusion, with separate root and independent hand audits.
- [ ] CY.TRIANGLELEAF: at most four extras jointly in the two larger articulation/leaf regions remains unproved. No two-per-region claim is made.
- [ ] CY.C7.COMPLETE / CY.MIXED.COMPLETE: general C7 and mixed cyclic completion remain open.

The exact comparison for k=5 and the nonnegative winding argument are included in the manuscript. No optimizer, finite parameter cover, Lean compilation or CI run is used. The coarse cyclic count remains two whole cells closed and 56 open; the unrestricted lower bound and equality necessity remain open.


## October 23, 2026, 20:28 CDT / October 24, 01:28 UTC — deep ordered roadmap reconciliation

Reconciled the live PR head `f353540845b94fcc7e41e29f8eccf4fffd951af3` against the roadmap. Consolidated DEEP_GATED_ROADMAP.md around the current proved dependency chain, then added the full G3 execution tree: selected planar certificate and uniqueness; exhaustive boundary-only versus mixed split; the exact C7 capacity target and explicitly alternative proof routes; the first complete mixed cell C1.3.b1; full D and S articulation domains; finite semantic refinement contracts for every remaining coarse cell; and sharp parent assembly. G4 universal quantifiers, G5 equality necessity/converse and G6 full-chain audit received deeper exit subgates.

The first active mathematical target is triangle-plus-leaf completion. The aligned S articulation has a full shared-side slider interval, which is not covered by the zero-tilt limits of its two tilted-vertex formulas. This boundary case is retained explicitly. The D branch retains the whole strict slider interval and its selected-normal endpoint explanation. Both require a joint capacity at most four in the two residual regions, not an assumed two-per-region bound.

This commit changes proof planning and status only. It does not close C1.3.b1, C7 completion, any additional coarse cell, T9 or equality. Counts remain two closed and 56 open. Separate agents are working on the entire D branch, entire S branch and entire positive C7 capacity. No Lean compilation or CI was run.


## October 23, 2026 — first ordered closures after deep-roadmap commit d1be168

TRIANGLE_LEAF_CORE_REDUCTION.md completes G3.M4.0: exactly three loaded bodies, closed physical noncontacts from the leaf to the two triangle tips, the full force/common-moment system, the acute westward load cone, exhaustive D/S articulation formulas, and routing of every extra into two residual regions. The common triple-junction case is treated as an actual three-port tree, not an artificial triangular hole. A separate independent hand audit passed.

S_LEAF_TRIANGLE_EXCLUSION.md closes the entire S-leaf branch G3.M4.S, including all aligned heights and both tilted families. After a whole-packing reflection the articulation satisfies x+y>=d-3/2. Exact radius comparisons exclude the closed 90-degree circle arc with endpoint directions(-7,3)/sqrt(58) and(-3,-7)/sqrt(58) from every neighbor's circle corners. The positive circle corners of the touching B/C pair are pairwise acute and have a negative horizontal weighted sum. They must lie on both sides of the forbidden arc, contradicting acuteness. Both root and separate independent audits passed. No completion capacity assumption is needed because the entire stressed core is impossible.

BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md closes G3.B.R.DIAM.2 for all physical boundary C7 rings, without a stress premise. Exact shadow bounds and a common containing disk for all possible distant endpoint sectors show every three-contact path has endpoint distance<3; shorter paths are immediate. Root and separate independent audits passed. The enclosing-two=>diameter>=3 extraction remains open and is not inferred from far-vertex projections.

- [x] G3.M4.0 / C1.3.b1.REDUCE.
- [x] G3.M4.S, including S0 and S+/S-.
- [x] G3.B.R.DIAM.2.
- [ ] G3.M4.D and C1.3.b1.ALL remain open.
- [ ] G3.B.CAP, remaining mixed cells, T9 and full equality remain open.

The six files in roadmap commit d1be168 were read back from GitHub and matched exactly. No Lean compilation or CI was run. The coarse inventory still has two whole cells closed and 56 open.


## October 23, 2026, 21:00 CDT / October 24, 02:00 UTC — complete D contact reduction and strict center-cover piercing

D_LEAF_ARTICULATION_CONTACT_LOCALIZATION.md proves the full leftward-reaction theorem for every D-leaf triangle-plus-leaf core. Its support-span lemma includes arbitrary shared-side application means. Exact circle-corner acuteness excludes rightward reactions, and contact spans exclude vertical reactions. The remaining alternatives are parallel leftward reactions or opposite left-corner reactions with the exact height/slope relation. Root and another independent hand audit passed.

D_LEAF_GENERIC_CONTACT_SELECTION.md resolves the variable-application issue before choosing generic normals. An unloaded articulation determinant is a nonzero linear condition in any free strict vertex/vertex articulation normal. Finite avoidance is done before the physical stress argument and retains the matched four-junction normal pairs, uncrossing, conic thinning and unique planar component. Root independent audit passed. An exact positive physical D core at79/40<R<2 is retained as a control: the claim concerns a selected necessary certificate, not every possible stress. The entire D.PARALLEL and D.OBLIQUE branches remain open and now have detailed universal exit gates.

CENTER_COVER_PIERCING.md proves the full all-orientation radial-tail inequality and its strict common-point consequence: if the boundary-square centers fit in an open radius3/2 disk, the bounded complementary region has unit-square capacity at most1. Root independent audit passed for this theorem. The elementary minimum-enclosing-disk reduction further identifies the only possible C7 obstruction as an acute supporting triple with circumradius>=3/2. Pattern(1,1,5) is excluded; the other three positive graph-gap partitions remain open in this commit.

All nine files in commit697af9b were read back from GitHub and matched the submitted contents. No Lean compilation or CI was run. No whole coarse cell closes in this update: two remain closed and56 open; T9 and unrestricted equality remain open.


## October 23, 2026 — the entire selected oblique D branch is excluded

D_LEAF_NONPARALLEL_OWNER_EXCLUSION.md completes G3.M4.D.OBLIQUE. At least one loaded neighbor has a unique physical circle corner because one articulation contact is too close to the origin for a two-corner body. Simultaneous finite normal selection then removes a B/C vertex/vertex edge, handling both nonparallel and parallel fixed-force lines without a degenerate determinant claim. Every remaining B/C side owner, normal sign and actual application is covered.

The exact contact chart identifies actual positive-weight circle corners. If C has two physical circle corners, h<1/4 and the opposite B corner falls strictly short of the circle. If C has a unique corner, concurrence gives0<tau<1 and forces phi+psi<pi/4. A direct bound for h>=1/2 and a monotone pivot for h<=1/2 then put a genuine circle corner below the radius. The proof retains independent frames, unequal angles, all corner weights and the full height interval. Root full independent hand audit passed.

Only the entire parallel-left D branch remains before C1.3.b1 can close. The coarse inventory remains two closed and56 open. The generic-selection manuscript received a second independent audit; the strict-piercing theorem received a second audit and its minimum-disk section passed a separate audit. All nine files in commit1d5b4ed were read back from GitHub and matched. No Lean compilation or CI was run.


## October 23, 2026 — complete C1.3.b1 closure, no positive K4, and corrected C7 cover route

D_LEAF_PARALLEL_LEFT_EXCLUSION.md excludes the entire remaining parallel-left D branch. Its aligned-neighbor case retains every shared-side mean and uses a uniform corner-cap inequality; its vertex-supported case derives the full section/contact chart, eliminates every alternate circle mask, treats the coincident vertex/vertex breakpoint, and contradicts the allowed wall height using the two exact torque equations. Root and a separate independent audit passed.

TRIANGLE_LEAF_CELL_CLOSED.md assembles the full S exclusion, complete D localization, simultaneous pre-stress selections, and both exhaustive D exclusions. The assembly passed independent audit. This closes the entire C1.3.b1 cell with all five extra squares retained, and raises the selected positive cyclic component's minimum size to five. The live coarse inventory changes to three whole cells closed and55 open. The next m=5 cells are exactly C1.3.b2, C1.4.b1, C1.5.b0 and C2.33.b0; the deep roadmap now gives all their complete graph/layout branches and nested exit contracts.

NO_POSITIVE_K4_SUBGRAPH.md proves a uniform selected-graph obstruction with no radius premise. An arbitrarily small physical embedding cannot put another body center inside a triangle: a concentric inner square of side19/20 has uniform clearance from the three obstacles, preserves its nonzero winding through the contact-chord homotopy, and has area exceeding the maximum contact-triangle area. Hence every K4 subgraph is impossible. Root and separate independent audits passed. This closes the full K4 branch of C1.4.b1 but not its other graph branches.

BOUNDARY_TWO_CONTACT_SPAN.md proves the entire two-contact endpoint bound below3sqrt(3)/2 in the high-radius range, and excludes every acute minimum-center-disk supporting triple of gap type(1,2,4). Root full audit passed. Together with the earlier(1,1,5) exclusion, this leaves(1,3,3) and(2,2,3) for a positive-stress cover route.

C7_CENTER_COVER_GEOMETRIC_OBSTRUCTION.md gives an exact IVT family of actual physical C7 rings whose three radial centers require covering radius>3/2. All adjacent contacts and nonneighbor separations are proved; the obstruction persists at strictly subcritical radii by uniform continuity. A separate exact outgoing-contact torque identity proves these rings admit no positive C7 stress. Root full audit passed, including the robustness argument. The unstressed center-cover theorem is therefore rejected; the valid strict-piercing criterion remains conditional and the remaining cover gates explicitly retain positive stress. No two-square completion is claimed by the control.

All nine files in commit9a4573d were read back from GitHub and matched. Current handoff, concise roadmap and live ledgers were reconciled around the whole-cell closure; the deep roadmap retains the completed subproofs and supplies the entire five-body frontier. No Lean compilation or CI was run. T9, unrestricted equality and the full prerequisite-chain audit remain open.


## October 23, 2026 — five-body graph/load cover, full chain exclusion, empty C4 hole, and C7 block selection

NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md proves the complete selected-embedding obstruction: two vertices cannot have three common positive circle-touching neighbors. Deleting to K2,3 preserves the exterior-face incidence of all surviving boundary vertices, whereas its outer four-cycle can contain only two of the three common neighbors. Root proof and independent audit passed.

FIVE_BODY_BICONNECTED_REDUCTION.md classifies every biconnected simple graph on five vertices by complement paths/cycles and edge count. There are ten abstract types. Three contain K4; the wheel violates connectedness of the induced loaded complement; K2,3, the three-page book and the once-subdivided K4 violate the new common-neighbor obstruction. Only C5, house and the fan over a four-vertex path remain. The manuscript lists all necessary positive-load masks, with physical zero-weight circle contacts and all four extras retained. A one-off standard-library graph count was only a cross-check; the written classification is an exhaustive hand argument and does not depend on a finite computation. Independent audit passed. C1.5.b0 remains open until all three graph families receive full geometry/completion proofs.

TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md closes the entire length-two-arm layout of C1.3.b2. The true radial leaf/transmitter chain gives articulation right support x<1/60. A two-force concurrence lemma requires only one circle-touching neighbor and retains the possible outside-face two-corner concurrence. The embedded three-port order gives positive articulation concurrence and two leftward reactions. Every tilted articulation violates an exact center-cap distance bound. Parallel aligned reactions violate the unit center separation. In every remaining aligned chart, simultaneous finite selections retain both side owners and all corner masks; exact circle-coordinate sums force a+c<1/6 and then a corner norm above Q. Root and separate independent audits passed. The two layouts with two leaves remain open; the full C1.3.b2 parent is not ticked.

FOUR_CYCLE_LEAF_HOLE_EMPTY.md proves capacity zero in the inner hole of the entire C4-plus-leaf branch. An inner unit preserves nonzero winding through arbitrarily small physical routing and the contact-chord homotopy. Coincident contacts give a retraced loop or too-small triangle. Otherwise equality in the complete four-contact area bound forces a regular unit contact polygon and four outward aligned squares. A zero-load ring vertex would require a non-strict axis normal at a point-only vertex contact. If the other three ring vertices are loaded, their exact far-corner equations force R^2=5/2. Both alternatives contradict the declared certificate/window. Root and separate independent audits passed. All surviving C1.4.b1 completion is now exterior, since its diamond holes are triangular and K4 is excluded. The joint exterior capacity remains open.

C7_FIXED_APPLICATION_GENERIC_SELECTION.md proves a complete finite-avoidance theorem for one-circle-corner stars with fixed pair applications. C7_TWO_CIRCLE_CORNER_BLOCKS.md classifies radial vertex shells and all radial-pair contacts, chooses compatible open normal intervals excluding every three-radial run, and proves there are at most four radial bodies. Its exact inner-circle arc argument separately excludes parallel radial pairs in any physical C7. Root audits passed.

C7_SHARED_SIDE_BLOCK_GENERIC_SELECTION.md handles variable shared-side means collectively. Nonzero scalar multiples of J times chosen circle corners give pure translations annihilating every circle force and internal shared-side force, independently of the application positions. Combined with rotation, this gives a nontrivial determinant in each free endpoint normal. All one-active-corner and zero-load masks are listed before KKT, including the single-block closing-edge case, and the choices survive uncrossing/thinning. A surviving free vertex edge therefore meets a shared-side block with a body carrying both positive circle-corner weights. Such a radial body must be an endpoint; the no-parallel-radial theorem makes it the unique physical radial body of that block. Root full audit passed, including the strengthened weight/endpoint conclusion. This does not imply one owner per body or classify every remaining stationary ring.

The live README, concise roadmap, deep roadmap, G2 ledger and complete 58-row cyclic ledger now record these exact scopes. The deep tree adds the full C5/house/fan mask branches, the entire chain closure, every C4 hole-equality gate, and the C7 all-owned versus radial-endpoint-pinned domains. The latter retain all two-owner/zero-owner changes, shared means, zero weights and contact limits. The positive-stress center-cover patterns(1,3,3) and(2,2,3) remain open. Counts stay three whole cells closed and55 open; T9, unrestricted equality and full-chain audit remain open.

All 13 files in commit604c939 were read back from GitHub and matched exactly. No Lean compilation or CI was run. Every commit uses [skip ci], and PR #11 remains draft.


## October 23, 2026 — whole S/S and D/S exclusions, C4 adjacent-load closure, and complete C7 free-edge cover

TWO_S_LEAVES_ONE_TRIANGLE_ARTICULATION.md excludes every same-articulation S/S leaf-type configuration. The two radial applications are on a side support, adjacent vertices, or opposite vertices. The first full domain is excluded by an inaccessible150-degree circle arc; adjacent vertices force a needed support face too close to0 for any boundary neighbor; opposite vertices give an inaccessible120-degree arc. Every positive leaf-weight combination points the triangle-tip load into the forbidden arc, contradicting its pairwise acute circle corners. Root and separate independent audits passed.

TWO_MIXED_LEAVES_ONE_TRIANGLE_ARTICULATION.md excludes the entire D/S leaf-type domain at one articulation. The D support makes A aligned; the S support is exhaustively the top side, northeast vertex or northwest vertex. Exact height bounds make the appropriate90- or120-degree circle arc inaccessible for every actual neighbor orientation. Its interior contains every negative leaf-resultant direction. Root and separate independent audits passed. Only D/D remains in the same-articulation layout; the two-distinct-articulation layout also remains open. No full C1.3.b2 closure is claimed.

FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md proves a stronger orientation-free geometric detour theorem and closes the full adjacent-loaded-pair C4-with-leaf branch. A radial-leaf articulation is within max(sqrt(R^2-1/4)-2,0) of0. A normal channel through a zero-load transmitter forces the high-radius window and confines its far square to minimum projection>59/60. A complete all-orientation cap lemma then puts that square's entire shadow within atan(13/20). A circle-touching detour square meeting both endpoints would violate the independent strict atan(23/16) boundary shadow bound, with the exact cosine margin21/sqrt(446665)>1/36. The far endpoint need not touch the circle, and the detour body need not carry circle weight. Both leaf types, both channel widths, all actual means and orientations are retained. Root and separate audits passed. The C4 opposite-load and three-load branches and both diamond attachments remain open.

BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md extends the fixed-point determinant selection from C7 to every unique-physical-circle-corner degree-two star with at least one boundary neighbor. A free contact toward the possibly clear neighbor has a nonzero coefficient after the radial-inner-corner/outer-width case is excluded. A free boundary contact has a nonzero coefficient or is already impossible by the nonzero boundary-contact moment. Coincident applications, zero circle weights, matched junctions and all final uncrossing/thinning choices are covered. Variable shared-side applications are expressly outside the lemma. Independent audit passed; no unproved fixed-mean replacement is introduced.

C7_TWO_CIRCLE_CORNER_BLOCKS.md now includes a full fixed-contact cone obstruction at a radial-pair endpoint. Its strict failure persists in an open interval near the appropriate tangent axis. An adaptive choice on each maximal physical radial run excludes every two-run having either outside contact point-only, while longer runs retain the previous exclusion. Thus both endpoints of every surviving radial/radial edge belong to nonsingleton shared-side blocks. Root full audit passed for the strengthened two-sided statement.

C7_PINNED_VERTEX_CONTACT_TYPES.md derives every relevant length2–5 shared-side block profile from its unique radial endpoint. The new general contact bound |p|>=sqrt(R^2-1)-1 applies to every boundary/boundary common point, not only vertices. Exact vertex-radius ranges exclude all unequal endpoint-length pairs. For length3 pairs, the high vertex violates the40-degree center-separation theorem; both low-vertex side-axis endpoints violate exact application-mean or circle-cone conditions, so an open normal choice excludes that whole pair. The only surviving free-edge types are radial/radial and the mirror pair of two length2 blocks. Root and separate independent audits passed.

The same manuscript contracts maximal shared-side blocks and gives the full free-edge arrangement cover. Every incident block has at least two bodies; at most three fit among seven bodies. Two free incident edges have opposite radial/radial and unique/unique types, ruling out a free cycle. Disjoint free edges would require at least eight bodies. Hence there are at most two free edges. With two, the only block-length layouts are2+2+3, or2+2+2 plus a unique-physical-circle-corner singleton on the owned complementary path. Individual-block poses are now exhaustively known; actual owned complementary contacts, their weights and the capacity theorem remain open. The all-owned C7 domain also remains open, with every ownership transition retained.

The six live status files now expose each complete branch and each remaining parent obligation. The C7 minimum-center-disk patterns(1,3,3) and(2,2,3), the mixed parent cells, T9, unrestricted equality and full-chain audit are still open. The coarse inventory remains three whole cells closed and55 open. All13 files in commitfbc12b1 were read back from GitHub and matched exactly. No Lean compilation or CI was run; every new commit uses[skip ci], and PR#11 remains draft.


## October 23, 2026 — the complete C7 free-normal branch is closed

C7_TWO_FREE_EDGES_EXCLUSION.md independently excludes both complete two-free-edge layouts. For2+2+3, the closing center gap is strictly greater than60 degrees and both radii exceed sqrt(2), so the required touching centers would be more than sqrt(2) apart. For2+2+2 plus a singleton, both possible owners of its second contact give a full point segment. Exact trigonometric bounds for the first point and an orientation-uniform two-point unit-square center theorem force every singleton corner below411/200<sqrt(17)/2. This contradicts physical circle contact even at zero multiplier. Root full independent audit passed.

C7_RADIAL_VERTEX_EDGE_EXCLUSION.md then supplies a stronger simultaneous-selection theorem excluding every radial/radial edge. The complete free-edge graph cover supplies an incident pinned block with an owned far external point. Normalize the common positive origin moment to one. Force balance through each unique-corner body uniquely propagates the internal force magnitude and actual shared-side mean because the circle direction is never parallel to the common side axis. No mean is frozen by assumption. The radial anchor's final mean x is therefore fixed independently of the free radial-pair normal. The exact two-corner cone inequality fails near the tangential endpoint for every x>d; at x=d it fails for every strict nonaxis normal. Adaptive physical-run choices preserve all previous selections, uncrossing and thinning. Separate full independent audit passed.

C7_MIRROR_VERTEX_EDGE_EXCLUSION.md excludes the remaining single unique/unique mirror edge. Its exact common-normal cone has endpoint means x=c and x*=c(c^2-2c+13/4)/(c^2+5/4) at the radial shared side. The anchor's other external normal is an actual fixed vertex/side normal. Its nonnegative circle cone imposes closed intervals on the fixed slope k; the endpoint intervals are disjoint because x*<=14375/13312<13/12<21/19<c(2a0-1)/(2c+1). At least one endpoint fails strictly, including the s=0 and mean-boundary cases; continuity supplies a nonempty open interval of strict common normals. The choices are physical and precede multipliers. Root full independent audit passed.

The complete selected-C7 contact domain is now side-axis-owned. This is a full free-normal exclusion, not a one-owner-per-body theorem. The remaining capacity proof must retain every zero-owner/two-owner transition, physical radial/unique-corner mask, zero weight, shared-side mean and both arbitrary completion squares. The deep roadmap now gives an explicit3^7 owner-word domain, the elementary count v2-v0=D of doubly owned edges, and separate full one-owner and transition-containing proof exits. No numerical pose cover or angle grid is introduced.

S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md proves a global S-leaf obstruction: all other loads cannot lie in one connected physical graph of boundary neighbors of its articulation. The existing inaccessible90-degree arc and the leaf's separated circle-corner interval split every such neighbor into one strict vertical-sign class. Physical boundary edges preserve the class by acuteness and circle-corner ordering; force balance then fails. This excludes the entire S-leaf diamond-hub case with a physically boundary second hub, including zero weight there. The clear-hub and D branches remain. Root full audit passed.

UNIT_BYPASS_NORMAL_CHANNEL.md proves, without a radius premise, that a normal-transmission channel whose endpoints have another common physical unit neighbor has exactly one side-normal transmitter. The unit bypass diameter first limits the reserve to sqrt(2). Diagonal equality would give two same-frame unit squares separated transversely to their diagonal: disjointness requires center distance at least sqrt(2), while their same endpoint support face bounds it by one. Thus the reserve is exactly one. Every actual side application mean remains. This sharpens the entire opposite-load C4 residual without declaring its full geometry or exterior capacity solved. Root full audit passed.

All12 files in commitc298675 were read back from GitHub and matched exactly. The live summaries and deep roadmap now record the complete C7 free-normal closure and its sole all-owned terminal capacity gate. Counts remain three whole coarse cells closed and55 open. T9, unrestricted equality and the full prerequisite-chain audit remain open. No Lean compilation or CI was run; commits use[skip ci] and PR#11 stays draft.
