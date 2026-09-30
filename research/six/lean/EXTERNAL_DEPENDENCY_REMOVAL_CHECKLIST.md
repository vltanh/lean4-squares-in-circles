# n=6 proof dependency checklist

This ledger distinguishes two proof routes. See `APPROACHES.md` for the
conceptual comparison.

Compilation, Comparator and kernel/axiom execution remain unperformed on the
current analytical head.

## Route A: historical self-contained finite classification

This route was built to avoid external-script theorem premises while still
using internal finite computation.

Its historical reduction stage used modules such as:

```text
Classification.CandidateGraph
Classification.CandidateTails
Classification.CommonDomain
Stress.ExactCover
Stress.FixedData.*
Stress.FixedRow / FixedReification / RowTactics
```

The fixed data are exact and their checkers use ordinary Lean computation such
as `decide`. That is categorically different from importing the success of a
Python search.

This route remains in the repository as development history and as a useful
cross-check. It is **not the current public n=6 endpoint path**.

## Route B: current analytical hand proof

The current source path is:

```text
original Packing
  -> Normalization.normalize_of_candidate
  -> Analytic.FixedPair.complete_reduction
       -> Analytic.candidate_diagonal_separators
            -> analytic MissingWestWing exclusion
            -> analytic MissingSouthWing exclusion
       -> SouthOuterTail.normalized_own_south_upper_tail
       -> ReductionInterface.reduction_iff_edges_and_south_tail
  -> analytic fixed-pair / diagonal closure
  -> retained selected-source witnesses
  -> eight contacts and exact support tightness
  -> point-set reconstruction and reflection absorption
  -> Six.lower_bound / Six.uniqueness / Six.optimum
  -> SquaresInCircles.optimal_radius / optimal_packings
```

At source/import level:

- [x] `Six/LowerBound.lean` imports `Analytic.CompleteReduction` directly.
- [x] `Six/Uniqueness.lean` uses `complete_reduction` directly.
- [x] `Classification/Reduction.lean` is only a compatibility adapter to the
      analytical reduction.
- [x] the old pair-certificate / BalancedClosure equality chain is not used by
      the public endpoint.
- [x] the former three reduction obligations are supplied analytically.
- [x] the final OWN-S tail is analytical.
- [x] no external research script success is a theorem premise in the new
      source chain.

## Legacy pair/equality chain

The old route

```text
Equality.Reconstruction
  -> Equality.SupportRigidity
  -> Stress.BalancedClosure
  -> Stress.PairLowerBound
  -> Stress.PairLocal
  -> Stress.PairCertificateChecks
  -> Stress.PairCertificateModel
```

was already bypassed before the final analytical classification was completed.
Those files remain historical source.

The current equality path is

```text
Analytic.SelectedPairWork
  -> Equality.ContactCoordinates
  -> Equality.AnalyticContacts
  -> Equality.AnalyticReconstruction
```

and retains the actual selected separator witnesses.

## Remaining dependency work

The mathematical replacement is source-complete. What remains is verification
of the *elaborated* dependency graph rather than more source rewiring:

- [ ] full Lean build;
- [ ] `#print axioms` on `Six.lower_bound`, `Six.uniqueness`,
      `SquaresInCircles.optimal_radius` and `optimal_packings`;
- [ ] inspect the accepted declaration dependencies and confirm that
      `Stress.ExactCover`, fixed-row/fixed-data checkers and the legacy
      pair-certificate chain are unreachable from the advertised n=6 results;
- [ ] run Comparator and independent kernel replay.

A textual import review is strong evidence about the intended path but is not a
substitute for elaboration and kernel inspection.

## External scripts and artifacts

Historical scripts under `research/six/` and `research/six/lean/` are
development/replay material. They may remain in the repository.

For both routes, the theorem must not assume their reported success. For the
analytical route specifically, substantive inequalities are proved in Lean by
the displayed algebra/analysis rather than imported from those scripts.

## Current claim

The current repository contains two documented approaches:

- a historical self-contained finite-checker proof route;
- a current table-free analytical source route.

The public n=6 endpoints now select the analytical route. Kernel validation of
that route is still pending.
