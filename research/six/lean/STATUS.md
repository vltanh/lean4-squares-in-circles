# n=6 status

PR #7, branch `feat/six-lean-proof`.

## Summary

There are two distinct n=6 proof approaches in the repository. They are
documented side by side in `APPROACHES.md`.

1. The **self-contained finite-classification route** used ordinary Lean
   finite checking and exact fixed rows. It never required an external script
   result as a theorem premise.
2. The **analytical hand-proof route** replaces that classification by
   continuous geometric and analytic arguments.

The current public n=6 source uses the **analytical route**.

At source level, the three former reduction obligations are closed:

- `MissingWestWing` is excluded analytically;
- `MissingSouthWing` is excluded analytically;
- canonical OWN-S satisfies the required upper tail
  `helperAngle 4 < 11/25`.

`Analytic.FixedPair.complete_reduction` therefore constructs
`ReductionHypotheses` for every normalized packing.

## Current public endpoint path

```text
Packing
  -> Normalization.normalize_of_candidate
  -> Analytic.FixedPair.complete_reduction
       -> Analytic.candidate_diagonal_separators
       -> SouthOuterTail.normalized_own_south_upper_tail
       -> ReductionInterface
  -> Analytic.FixedPair.radius_of_reduction
  -> retained selected-source work
  -> eight-contact equality reconstruction
  -> Six.lower_bound / Six.uniqueness / Six.optimum
  -> SquaresInCircles.optimal_radius / optimal_packings
```

`Six/LowerBound.lean` imports `Analytic.CompleteReduction` directly.
`Six/Uniqueness.lean` uses `Analytic.FixedPair.complete_reduction` directly.
Neither public endpoint imports a `Classification` module.

`Classification/Reduction.lean` remains only as a compatibility namespace
adapter. Its implementation now delegates to the analytical results.

## Analytical source milestones

Completed source blocks include:

- [x] exact candidate construction and normalization;
- [x] analytic fixed-pair envelope on the explicit domains;
- [x] corrected diagonal remainder, nonnegativity and unique zero;
- [x] full secondary-source selection and double-D exclusion;
- [x] low-D west exclusion and strengthened D-sourced west gap;
- [x] complete cardinal-W missing-south exclusion;
- [x] complete OWN-W missing-south exclusions;
- [x] complete missing-west exclusions for cardinal-S and OWN-S branches;
- [x] reflected two-OWN cases with their reflected domains proved explicitly;
- [x] sharper shared-center OWN/OWN angle budgets;
- [x] final OWN-S upper tail in `Analytic/SouthOuterTail/`;
- [x] unconditional `Analytic.FixedPair.complete_reduction`;
- [x] lower bound routed directly through the analytical reduction;
- [x] uniqueness routed through the analytical reduction and eight contacts;
- [x] point-set reconstruction and absorption of the recorded reflection.

The hand proof is summarized in `docs/proof/six.md`. Detailed analytic notes
are listed below.

## Historical finite-classification route

The old finite classifier remains in the repository for provenance. It used
exact fixed data, proved checker soundness and ordinary Lean `decide`.
It is not an external Python oracle, and it is useful as an independent
development/reference route.

It is no longer the advertised endpoint path. Presence of
`Stress.ExactCover`, `Stress.FixedData` or old classification modules in the
repository should not be read as a dependency claim about
`Six.lower_bound` or `Six.uniqueness`.

See `APPROACHES.md` and `EXTERNAL_DEPENDENCY_REMOVAL_CHECKLIST.md` for the
dependency distinction.

## Validation status

The analytical route is **source-complete, not yet validated by execution on
this head**.

Still unexecuted:

- [ ] full `lake build`;
- [ ] `lake comparator`;
- [ ] `SixAxiomAudit.lean` and the public-root axiom audit;
- [ ] a transitive elaborated dependency check confirming that no old
      finite-cover/table declaration is reachable from the public n=6 results;
- [ ] independent kernel/Palomar replay.

No CI run or commit status is currently recorded for the final analytical head.
Recent proof-development commits used `[skip ci]`.

Accordingly, the correct current claim is:

> The analytical proof is complete at source level and wired into the public
> endpoints; kernel acceptance and final dependency/axiom validation are still
> pending.

## Documentation map

- `APPROACHES.md` — distinction between the finite and analytical routes.
- `HUMAN_ANALYTIC_STANDARD.md` — acceptance rules for the analytical route.
- `ANALYTIC_NORMALIZATION_PROOF.md` — normalization.
- `ANALYTIC_DIAGONAL_PROOF.md` — diagonal scalar closure.
- `ANALYTIC_CARDINAL_SOUTH_PROOF.md` — cardinal-W large-south exclusion.
- `ANALYTIC_SOUTH_TAIL_PROOF.md` — final OWN-S tail, including the repaired
  exceptional OWN/OWN corner.
- `EXTERNAL_DEPENDENCY_REMOVAL_CHECKLIST.md` — source-path dependency ledger.
- `docs/proof/six.md` — reader-oriented proof overview.
