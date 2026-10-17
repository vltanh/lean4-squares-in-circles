# Gated roadmap to the unrestricted eight-square theorem

Started: 2026-10-16 (America/Chicago); continued 2026-10-17 UTC.
Starting head: `77ac445d3c8b5299d02aa58d14aa444646234959`.
Scope: PR #9, `research/eight/**`, pen-and-paper research with exact
computer assistance. This is the active queue, superseding the
chronological queue in `GATED_ROADMAP_2026_10_13.md`.

**The unrestricted proof remains open. The entire M5 and M6 branches
are now excluded at the research ceiling.** The new universal
[exterior-frame theorem](GLOBAL_EXTERIOR_FRAME_WINDOW.md) bypasses the
former M5 small-J/diffuse split. A global radial-boundary reduction and
three complete continuous certificates leave three explicit radial
patterns. Sharp global capture of the survivors is the active gate.

## 1. Exact target and closure standards

Let \(q_*=R_*^2\) be the unique least admissible five-corner family
radius selected by [HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md),
with the radical and stationary equations in
[HUMAN_FIVE_CORNER.md](HUMAN_FIVE_CORNER.md). The decimal
\(R_*\approx1.97877086534\) is descriptive only. The
[exact construction](ANALYTIC_EXACT_CONSTRUCTION.md) proves attainment
by an actual eight-square packing.

The lower-bound target is:

> Every eight-tuple of unit squares with pairwise disjoint open interiors
> contained in a disk of squared radius q satisfies q >= q_*.

Work under the convenient ceiling \(Q=9789/2500>q_*\). A branch
excluded throughout \(q\le Q\) is finished. A branch admitting
configurations between \(q_*\) and \(Q\) must receive its sharp
\(q_*\) bound; decreasing a rounded search radius is not closure.

Three distinct exits remain visible:

1. **Optimality:** the unrestricted lower bound and actual construction.
2. **Equality:** all attaining poses, including genuine slider freedoms.
3. **Hand-proof closure:** analytic replacement of every retained
   computer-assisted premise.

An exact computer-assisted theorem may be used for subsequent research.
It is not automatically a short hand proof. No Lean writing or
compilation, CI invocation, production-source change, or merge is
included in this work.

## 2. Gate table with exact exits

| Gate | Required exit | Current status |
|---|---|---|
| G0: target, exact model, attainment | Define q_* exactly; cover every actual packing by the ordered seven-angle model, with all 32 vertices and 28 true SAT alternatives. | **Passed, hand proofs.** Original Gate 1 and target interfaces re-audited. |
| G1: fiber and owner alternatives | Preserve original common-center fibers, sparse alternatives, canonical owner ties, and the exhaustive M5–M8 orientation cover. | **Passed, hand proofs.** Original Gates 2, 3A, and 3B.1 re-audited. |
| G2: central core | Every packing below Q has one central square containing the closed radius-1/12 disk in its open interior. | **Passed, computer-assisted.** All four exact branches replayed; counts and margins reproduced. |
| G3: radial-boundary cover | Every exterior seven-cycle deforms, at fixed true frames and physical angle sum 2π, into two explicit one-parameter boundary curves while retaining adjacent SAT. | **Passed, hand proof.** Nonneighbor constraints are explicitly relaxed. |
| G4: global frame concentration | All seven exterior frames lie in one open 45-degree interval; exclude every M5 and M6 configuration. | **Passed, computer-assisted.** All 40 four-type branches complete, followed by hand odd-cycle and frame-lifting proofs. Also D<7/10. |
| G5a: no adjacent core states | Cover the whole boundary cycle by five binary necklaces with no adjacent C. | **Passed.** Hand core-pair bound plus the completed G4 pair theorem. |
| G5b: three-core exclusion | Exclude the whole COCOCOO continuous family at Q. | **Passed, computer-assisted.** All eight closed pair branches complete; a hand sum gives 3929/625>2π. |
| G5c: short two-core exclusion | Exclude the whole COCOOOO continuous family at Q. | **Passed, computer-assisted.** All 28 directed role/sign branches complete; their cost sum is 125709/20000>2π. |
| G6: global survivor capture | Cover every remaining physical boundary cycle by a finite explicit collection of families on which all sharp-proof hypotheses hold, or prove a direct universal sharp inequality. | **ACTIVE / OPEN.** Three radial words remain; M7 and M8 are not closed. |
| G7a: quantitative candidate terminal | Give explicit continuous pose/frame tolerances including both full slider ranges, with every actual SAT owner covered. | **Passed.** The quantitative curved tube admits center error 1/1000 and total five-edge mismatch 1/10000. All 44 wrong-gap and 640 owner-reserve comparisons pass; an explicit nonlinear estimate proves the sharp bound. |
| G7b: terminal completeness | Prove q>=q_* on every family retained by G6, or strictly exclude it. | Open. G7a applies once G6 proves its hypotheses; unclassified branches remain. |
| G8: unrestricted assembly | Prove that every normalized packing reaches a completed terminal theorem, then combine with the exact construction. | Waiting for G6–G7b. **Radius interface passed:** monotone outer-radius expansion and a 10^-16 center pullback transfer a sharp rational-ceiling capture to an actual smaller disk. |
| G9: global equality | Trace equality through a complete cover and recover exactly all attaining poses and slider ranges, with converse feasibility. | Open. Deformations used for lower bounds need a separate equality analysis. |
| H: hand conversion and final audit | Replace each retained computational premise by an analytic proof and audit the full dependency chain, ties, and boundaries. | Open. Currently G2, G4, G5b, and G5c contain computational premises. |

The old M5-DIFFUSE gate is closed by G4 as a whole. The recovered 3+5
and 4+4 reference certificates are no longer dependencies of the
active route. Their historical results remain valid and separately
audited; their hand conversion is unnecessary if the new route is
converted analytically instead.

## 3. The active G6 parent domain

The geometric reduction is precise. A parent state is an ordered
seven-cycle of actual unit squares with:

- centers in cyclic order and gaps \(3/5<\delta_i<\pi\), summing
  **exactly** to \(2\pi\);
- a square on the `O` or `C` radial curve at the sharp rational ceiling
  Q_sharp=q_c+10^-16 for each label, where
  q_c=3.91553413751747532652;
- all seven adjacent genuine SAT disjunctions, with actual frame
  widths and a consistent frame at every vertex;
- all seven exterior frames in one interval of length less than 7/10.

Nonneighbor overlaps and overlaps with the central square beyond its
radius-1/12 core have been relaxed. A universal sharp theorem on this
larger domain would suffice. If the relaxation admits a smaller
counterexample, restore the necessary original geometric constraints;
do not discard the counterexample by assumption.

The [monotone-radius lemma](OUTER_RADIUS_MONOTONICITY_AND_SHARP_PULLBACK.md)
expands each O radius while retaining all center rays, frames, relative
parameters, C states, and selected true SAT inequalities. Thus the
completed exclusions at the coarser Q=9789/2500 apply to this sharp parent
domain with the same radial word. Conversely, starting with any hypothetical
q<q_*, put q_bar=max(q,q_c-2*10^-16), perform the radial reduction there,
and expand to Q_sharp. The center change on returning to q_bar is at
most 10^-16. A terminal center-error target 0.00099 therefore transfers
into the proved 0.001 tube. Capture at the larger circle alone would not
have supplied this contradiction; the explicit pullback does.

The finite radial cover, up to rotation and reflection, is:

| Word | Exact residual obligation |
|---|---|
| `OOOOOOO` | Cover or exclude the full all-outer seven-cycle. |
| `COOOOOO` | Cover or exclude every one-core seven-cycle. |
| `COOCOOO` | Cover the long-separation two-core family and retain its candidate-compatible sharp configurations. |

Each word still contains seven continuous relative-frame parameters
and compatible physical gaps. The word list is a completed geometric
reduction; it is not a completed contact classification.

### G6.1 — completed finite cover

Give explicit families \(F_1,\ldots,F_N\) and prove that every parent
state arising below \(q_*\) lies in their union. Retain all owner
ties, shared parameter endpoints, cyclic relabelings, reflections,
and actual closing constraints. A sampled first-contact graph does
not prove this union.

### G6.2 — usable sharp hypotheses

For each retained family, prove the exact hypotheses of its terminal
inequality. The new
[uniform slider theorem](HUMAN_UNIFORM_SLIDER_LOCAL_SHARPNESS.md)
extends local sharpness to a neighborhood of the full candidate-compatible
T/G slider rectangle, including both radial endpoints. All 44 wrong-axis
corner bounds and all 640 owner-coefficient corner bounds passed exactly;
convexity and concavity fill the continuous rectangle. This repairs the
former fixed-slider interface. The
[quantitative terminal theorem](HUMAN_QUANTITATIVE_SLIDER_TUBE.md)
now supplies exact tolerances on the whole chart
|tan(t/2)-0.06189741100766035970|<=1/2000: center error at most 1/1000
and total aligned-edge angular mismatch at most 1/10000. Its explicit
dual estimate leaves a positive angular term 7S/2500. A global box must
prove every labeling, slider, common-tilt, center, and mismatch hypothesis;
numerical convergence to the candidate does not establish capture.

### G6.3 — union and usability audit

Check that every child has a full continuous proof or is precisely
retained. Only a complete cover with completed terminal proofs
discharges G6–G7. Optimizer minima, unfinished trees, and improved
nonsharp numerical bounds do not discharge a child.

## 4. Current proof dependencies and exact replay

The main assembled theorem is
[GLOBAL_EXTERIOR_FRAME_WINDOW.md](GLOBAL_EXTERIOR_FRAME_WINDOW.md).
Its dependencies are deliberately separated:

| Step | Proof artifact | Standard |
|---|---|---|
| Uniform core | CENTRAL_CORE_CERTIFICATE.md; verify_central_core.cpp | Exact computer certificate plus hand counting |
| Radial deformation | CYCLIC_RADIAL_BOUNDARY_REDUCTION.md | Hand geometry |
| Continuous four-type inequalities | FOUR_TYPE_BOUNDARY_PAIR_CERTIFICATE.md; verify_fourtype_pairs.cpp | Complete exact dyadic verification |
| Seven-walk type budget | FOUR_TYPE_ODD_CYCLE_LEMMA.md | Hand four-vertex graph proof |
| Frame window and D<7/10 | FRAME_SEMICIRCLE_FORCING.md; EXTERIOR_FRAME_CONCENTRATION.md | Hand concavity, lifting, and rational Taylor bounds |
| No adjacent C | NO_ADJACENT_CORE_BOUNDARY_STATES.md | Hand estimate using certified pair costs |
| No three C | THREE_CORE_BOUNDARY_EXCLUSION.md; verify_boundary_pair_costs.cpp | Complete exact dyadic verification plus hand telescoping |
| No short two C | SHORT_TWO_CORE_BOUNDARY_EXCLUSION.md; verify_boundary_pair_costs.cpp | Complete exact directed-role verification plus hand telescoping |
| Local sharpness across both full slider ranges | HUMAN_UNIFORM_SLIDER_LOCAL_SHARPNESS.md; verify_uniform_slider_local_dual.py | Analytic compact-family extension with finite exact coefficient checks |
| Explicit full-slider terminal | HUMAN_QUANTITATIVE_SLIDER_TUBE.md; verify_quantitative_slider_tube.py; QUANTITATIVE_SLIDER_TUBE_AUDIT.md | Exact coefficient bounds and a hand nonlinear remainder estimate |
| Coarse/sharp radius transfer | OUTER_RADIUS_MONOTONICITY_AND_SHARP_PULLBACK.md | Hand monotonicity of active true SAT projections and an explicit center-error bound |

All three continuous certificates retain exact rational constants, sources,
all complete branch logs, strict margins, and SHA-256 manifests. The
proof notes give direct build and run commands. Independent audits
cover the actual SAT formulas, complete closed domain coverage,
monotone cost restriction, interval acceptance, and source/data/log
binding. Budget exhaustion or a missing completion line is failure.

## 5. Executed work and remaining standard

This continuation re-audited the foundational representation/fiber/
owner/majority gates. It also recovered and replayed the complete old
96-root 3+5 order certificate and 66-root 4+4 certificate: 162 roots,
145,970 nodes, and 127,744 exact contradiction leaves. The recovered
low proof is an independent order certificate, not the formerly
missing grid certificate.

The new route then supplied the hand radial reduction, completed all
40 four-type branches (3,746,056 nodes and 1,874,308 terminal rectangles),
and closed all M5/M6. The no-adjacent-core lemma and all eight
three-core branches (754,058 nodes and 377,285 terminal rectangles),
followed by the complete short-two-core cover (9,535,240 nodes and
4,768,516 terminal rectangles), reduce the global radial cover to the
three displayed words. The uniform local theorem now includes the full
candidate-compatible slider rectangle. Its quantitative extension now
provides a precise terminal tube, and the hand monotone-radius lemma
resolves how a capture at Q_sharp contradicts a packing below q_*.

**Next required exit:** a complete sharp capture or direct inequality
for those remaining continuous families. Global optimality, global
equality, and hand-proof closure remain open until their stated gates
are proved.
