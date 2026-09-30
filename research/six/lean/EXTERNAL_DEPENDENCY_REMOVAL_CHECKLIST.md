# External-dependency removal checklist for the n=6 proof

This file tracks the stronger target requested for the six-square formalization:

> the unrestricted lower bound and uniqueness should be proved by Lean source
> that does not depend on external-script success, externally generated
> certificate tables, or certificate-style finite-cover machinery.

Compilation is deliberately out of scope for this checklist. The audit here is
static: imports, proof bodies, and checked-in data.

## What counts as an external/certificate dependency here

Three different things are distinguished.

1. **Actual external execution from Lean.** File/process calls, `run_tac`,
   `Lean.ofReduceBool` / `native_decide`, imported PASS flags, or custom
   axioms would be hard failures.
2. **Certificate-era Lean dependencies.** Checked-in finite stress rows,
   interval/cell-cover checkers, and reified pair-envelope checks can be
   kernel-checked with ordinary `decide`, but they are still the
   certificate-style proof route we want to remove from the final theorem.
3. **Historical research artifacts.** Python scripts, JSON, logs, replay
   manifests, and audit tools that are not imported by Lean. These do not
   currently prove the theorem, but should remain clearly separated from the
   final dependency path.

Static source inspection found no actual theorem-path process/file invocation,
no `Lean.ofReduceBool`, no `run_tac`, and no project `axiom` declaration
used to establish the six-square result. The apparent `native_decide`
occurrence in the Six proof diff is prose saying that ordinary `decide` is
used instead. The two `sorry` declarations in `Challenge.lean` are the
intentional Comparator challenge holes, not imports of the Solution proof.

The work below therefore removes **category 2** from the public n=6 theorem
path and leaves category 3 only as historical/research material.

---

## A. Normalization certificate path — already bypassed

The current analytic normalization endpoint is
`Normalization.normalize_of_candidate` via `Six/AnalyticNormalization.lean`.
It does not need the old normalization finite-cover modules.

- [x] Strong central box replaced analytically.
- [x] Five-pin covering and labelled windows replaced analytically.
- [x] Moving-pin and W/D order path connected analytically.
- [x] Appendix A / D-own replaced analytically.
- [x] Candidate-radius cardinal refinements connected without normalization
      certificate checks.
- [ ] Confirm the final unrestricted endpoint import graph does not reach:
  - `Normalization/Certificates/CentralGrid.lean`
  - `Normalization/Certificates/Checks.lean`
  - `Normalization/Certificates/ConeSemantics.lean`
  - `Normalization/Certificates/Model.lean`
  - `Normalization/Certificates/Semantics.lean`
- [ ] After the final dependency graph is clean, mark those modules explicitly
      historical or remove them from the active Six development surface.

Note: the namespace `Normalization.Certificates` in `PinData.lean` contains
ordinary real pin constants. The namespace name alone is not an external
dependency.

---

## B. Fixed-row D-edge classification — still on the endpoint path

### Certificate/data modules to eliminate from the final transitive path

- [ ] `Stress/FixedData/Default.lean`
- [ ] `Stress/FixedData/Hard.lean` — includes the historical 53-cell (6,6) region.
- [ ] `Stress/FixedData/Tails.lean`
- [ ] `Stress/FixedData/AppendixC.lean`
- [ ] `Stress/FixedData/Bridges.lean`
- [ ] `Stress/FixedData/Checks.lean`
- [ ] `Stress/FixedRow.lean`
- [ ] `Stress/FixedReification.lean`
- [ ] `Stress/FixedGraph.lean`
- [ ] `Stress/FixedGeometry.lean`
- [ ] `Stress/ExactCover.lean`
- [ ] `Stress/RowTactics.lean`

These modules are self-contained Lean once the rows are checked in, but the
row inventories, weights and subdivisions are the certificate-era finite-data
route. `Checks.lean` proves 59 default + 53 hard + 3 tails + 99 Appendix-C +
3 bridge rows with ordinary `decide`; `ExactCover` then recursively proves
that row domains cover the requested real boxes.

### Classification modules that consume them

- [ ] Replace `Classification/A22Edges.lean`.
- [ ] Replace `Classification/A23Edges.lean`.
- [ ] Replace `Classification/Pattern26Edges.lean`.
- [ ] Replace `Classification/CardinalEdges.lean`.
- [ ] Replace `Classification/CandidateGraph.lean`.
- [ ] Replace `Classification/CandidateTails.lean`.
- [ ] Replace the certificate-derived parts of
      `Classification/CommonDomain.lean`.

### Existing analytic replacement route

Use `Analytic/SecondaryReduction.lean`,
`Analytic/CardinalWingClosure.lean`, and `Analytic/ReductionInterface.lean`
instead of reproducing every old row.

Already available:

- [x] W/D primary and reverse-secondary exclusions.
- [x] Full D/S forward-secondary selection.
- [x] `d > 1/2`.
- [x] D-sourced quarter-gap restrictions.
- [x] Double-D-secondary exclusion.
- [x] Both-cardinal wing branch closed.
- [x] Lower OWN-S tail proved; in fact canonical OWN S has positive deviation.
- [x] OWN-W outer tail follows once both candidate D edges are established.
- [x] Low-D D-sourced west separator excluded; a missing west wing has `d > 3/5`.
- [x] Exact logical reduction to the remaining missing-wing cases.

Still needed for a completely certificate-free D-edge/domain reduction:

- [ ] Prove `¬ MissingWestWing P` without `FixedData/Hard` or `ExactCover`.
- [ ] Prove `¬ MissingSouthWing P` without fixed rows.
- [ ] Prove the remaining OWN-S upper tail
      `P.ownBits 4 = true -> P.helperAngle 4 <= 11/25`,
      or derive it from the candidate graph.
- [ ] Assemble an unconditional theorem
      `analytic_reduction (P) : FixedPair.ReductionHypotheses P`.
- [ ] Make that theorem the only source of candidate D edges and pair domains
      used downstream.

---

## C. Common pair-envelope certificate — still on the endpoint path

### Certificate machinery to eliminate from the final transitive path

- [ ] `Stress/PairCertificateModel.lean`
- [ ] `Stress/PairCertificateChecks.lean`
- [ ] `Stress/PairLocal.lean`
- [ ] `Stress/PairLowerBound.lean`

The two substantive certificate checks are:

- `outer_checked`: finite outer cover for all bit/source choices.
- `local_derivative_checked`: 96 guarded local derivative checks over six
  sectors and two axes.

Both are proved inside Lean with ordinary `decide`, but they are the
certificate-style pair-envelope route to remove.

### Generic reification/interval machinery that should become unreachable

These modules are not inherently unsound or external, but the final n=6
endpoint should no longer need them once the pair certificate path is gone:

- [ ] `ProofTools/Certificate.lean`
- [ ] `ProofTools/Expression.lean`
- [ ] `ProofTools/RationalInterval.lean`
- [ ] `ProofTools/TrigInterval.lean`
- [ ] `ProofTools/Smooth.lean`
- [ ] `ProofTools/SmoothCalculus.lean`
- [ ] `ProofTools/FormulaLemmas.lean`

Do **not** remove a generic proof-tool module merely by name if another
non-certificate analytic theorem still imports it; the acceptance condition is
that the public n=6 endpoints do not transitively require the certificate
checker path.

### Existing analytic replacement

- [x] `Analytic/FixedPair.lower_bound` proves the adjacent-pair envelope on
      the explicit bit-dependent `Domain`.
- [x] Equality-compatible source classification at the origin is analytic.
- [x] Actual N/W and E/S pair work is connected to the packing.
- [x] Corrected diagonal remainder and unique zero are analytic.
- [x] `Analytic/FixedCandidateClosure.lean` proves radius and candidate
      angle/source data from `ReductionHypotheses`.

Remaining wiring:

- [ ] Stop importing `Stress/PairLowerBound.lean` from the final closure.
- [ ] Use `FixedPair.lower_bound` only through proved
      `ReductionHypotheses`.
- [ ] Remove `PairCertificateChecks` and its reified finite cover from the
      transitive graph of both unrestricted endpoints.

---

## D. Diagonal certificate path — already replaced

- [x] The old diagonal finite checker was removed.
- [x] `Stress/DiagonalVertexCheck.lean` is only a compatibility wrapper around
      the analytic `DiagonalRemainder` proof.
- [ ] Remove the compatibility wrapper from the final path when
      `CommonDomain` is no longer used.

No new diagonal certificate replacement is required.

---

## E. Final radius closure — rewire away from certificate carriers

Current route:

`LowerBound -> Stress.BalancedClosure -> PairLowerBound + CommonDomain`.

`BalancedSystem` imports `Classification.CommonDomain`, and
`BalancedClosure` imports `Stress.PairLowerBound`, so the current
unrestricted radius theorem still transitively reaches both certificate
families above.

Checklist:

- [ ] Add an unconditional analytic closure theorem, e.g.
      `normalized_radius_eq_analytic`, from
      `FixedPair.radius_of_reduction` plus `analytic_reduction P`.
- [ ] Change `Six/LowerBound.lean` to import that analytic closure rather than
      `Stress/BalancedClosure`.
- [ ] Replace the call to `Stress.normalized_radius_eq`.
- [ ] Ensure `Six.lower_bound` transitively avoids
      `Classification.CandidateGraph`, `CommonDomain`,
      `PairLowerBound`, `ExactCover`, `FixedData/*`, and
      `PairCertificateChecks`.

---

## F. Equality / uniqueness — remove the hidden old-closure dependency

The equality layer is not yet certificate-free even if the radius theorem is
rewired:

- `Equality/LocalCenters.lean` imports `Stress/BalancedClosure`.
- `Equality/SupportRigidity.lean` uses the balanced stress equality lemmas.
- `Equality/Reconstruction.lean` currently obtains
  `normalized_candidate_data` from the old `BalancedClosure` route.

The analytic fixed-pair closure already supplies:

- exact radius;
- all five candidate helper/diagonal angles;
- candidate-compatible N/W and E/S source indices;
- zero total candidate work.

What is still missing is an **analytic equality bridge** from that data to the
support/separator equalities used by reconstruction.

Checklist:

- [ ] Strengthen the analytic actual-pair/candidate-work interface to retain the
      actual selected N/W and E/S source witnesses, not only their scalar values.
- [ ] Build or refactor a balanced equality stress whose hypotheses are
      `ReductionHypotheses` / analytic candidate data, not `CommonDomain`.
- [ ] Prove nonnegative weights from the analytic domains (or directly at the
      zero candidate angles) instead of importing certificate-derived ranges.
- [ ] Prove zero total defect at equality from the analytic lower bound and the
      actual separator inequalities.
- [ ] Recover individual support/separator tightness from positive weights.
- [ ] Refactor `Equality/LocalCenters.lean` so it no longer imports
      `Stress/BalancedClosure`.
- [ ] Refactor `Equality/SupportRigidity.lean` to use the analytic equality
      bridge.
- [ ] Change `Equality/Reconstruction.normalized_congruent_candidate` to use
      `FixedPair.candidate_data_of_reduction` (or its strengthened successor)
      instead of `Stress.normalized_candidate_data`.
- [ ] Verify reflection absorption remains unchanged and certificate-free.
- [ ] Ensure `Six.uniqueness` transitively avoids every module listed in
      sections B and C.

---

## G. Development root cleanup

`SquaresInCircles/Six.lean` currently imports
`Classification.CandidateGraph` directly.

- [ ] Replace that import with the final analytic reduction/closure entry point.
- [ ] Update its module documentation so it no longer describes the fixed-row
      classification as the active proof.
- [ ] Keep legacy certificate modules out of the public Six root even if they
      remain in the repository for history.

---

## H. Historical external scripts and generated artifacts

These are **not Lean theorem imports** today. They should not be confused with
the active proof, but their names document the external-development history.

### Normalization research

- `research/six/check_normalization_core.py`
- `research/six/check_normalization_side_nearest.py`
- `research/six/n6_normalization_exact.py`
- `research/six/n6_normalization_interval.py`
- `research/six/n6_normalization_n0.py`
- `research/six/normalization_cert/*.py`
- `research/six/normalization_cert/REPLAY_MANIFEST.json`
- `research/six/normalization_cert/UNIT_TEST_LOG.txt`

### A2 / fixed-row research

- `research/six/check_A2_*.py`
- `research/six/n6_a2_fixed.py`
- `research/six/n6_a2_scalar.py`

### Audit/replay material

- `research/six/lean/check_algebra.py`
- `research/six/lean/check_cap_algebra.py`
- `research/six/lean/test_source_audit.py`
- `research/six/lean/ALGEBRA_CHECKS.json`
- `research/six/lean/CAP_ALGEBRA_CHECKS.json`
- `research/six/lean/CAP_LOCAL_MANIFEST.json`
- `research/six/lean/SOURCE_AUDIT.json`
- `research/six/lean/UPLOAD_AUDIT_RESULTS.json`
- `research/six/lean/LOCAL_BUILD_LOG.txt`
- `research/six/lean/SOURCE_TEST_LOG.txt`
- `scripts/audit-six-sources.py`
- `scripts/verify-six-foundations.sh`

Checklist:

- [ ] Keep all of the above out of Lean imports and theorem premises.
- [ ] Once the final dependency audit is clean, move clearly historical
      certificate-generation/replay material under a single archival
      subdirectory or delete it if repository history is sufficient.
- [ ] Do not delete ordinary documentation/figure/build tooling merely because
      it is a script; `scripts/figures/*`, `scripts/link_lean.py`, and
      `scripts/verify-comparator.sh` are not mathematical proof dependencies.

---

## I. Final static dependency acceptance check

Compilation is intentionally excluded here.

The source-level removal is complete only when static import traversal from all
four endpoints

- `SquaresInCircles.Six.lower_bound`
- `SquaresInCircles.Six.uniqueness`
- `SquaresInCircles.optimal_radius`
- `SquaresInCircles.optimal_packings`

does **not** reach any of:

- `Normalization/Certificates/Checks` or its executable certificate model;
- `Stress/FixedData/*`;
- `Stress/ExactCover`;
- `Stress/RowTactics`;
- `Classification/CandidateGraph` / certificate-derived candidate tails;
- `Stress/PairCertificateModel`;
- `Stress/PairCertificateChecks`;
- `Stress/PairLocal`;
- `Stress/PairLowerBound`;
- `ProofTools.Certificate.certify` through the final theorem chain;
- any research script, JSON result, log, manifest or external PASS flag.

- [ ] Produce the final transitive import/declaration inventory.
- [ ] Record the exact replacement theorem for every removed dependency edge.
- [ ] Update `STATUS.md` after this checklist is fully discharged.

Only after this source-level checklist is complete should compilation/kernel
validation be treated as the next, separate phase.
