# Two n=6 proof approaches

This file separates two mathematically different routes that have existed in
PR #7. They prove the same public statements over the same `Packing`,
`Congruent`, exact candidate and normalization definitions, but they use
different methods for the final classification step.

Neither route changes the problem statement. The distinction is about proof
method and dependency structure.

## Approach A: self-contained Lean finite classification

### Purpose

This was the first complete source route to the unrestricted n=6 lower bound
and uniqueness theorem. It was designed to satisfy the requirement that no
external Python program, numerical log or imported PASS flag be a theorem
premise.

The key point is that an ordinary Lean computation such as `decide` is part
of the Lean proof term. It is not an external numerical oracle.

### Historical architecture

At the source checkpoints where this route was active, the endpoint was

```text
Packing
  -> Normalization.normalize_of_candidate
  -> Classification.reduction
       -> CandidateGraph / CandidateTails / CommonDomain
       -> Stress.ExactCover / fixed rows / ordinary decide
  -> analytic fixed-pair and diagonal closure
  -> retained separating-source witnesses
  -> eight-contact equality reconstruction
  -> Six.lower_bound / Six.uniqueness
```

The finite stage used exact rational data, proved checker soundness and kernel
computation. It did not call Python at theorem elaboration time. For the weaker
"self-contained Lean, no external-script premise" criterion, this route was a
legitimate candidate pending compilation and kernel audit.

### What remains in the repository

The historical modules are intentionally still present for provenance,
comparison and regression work, including files under:

- `Six/Classification/`;
- `Six/Stress/FixedData/`;
- `Six/Stress/ExactCover.lean`;
- `Six/Stress/FixedRow.lean` and related reification/checking modules.

They are **not the current public n=6 proof path**. In particular,
`Classification/Reduction.lean` is now only a compatibility adapter to the
analytical reduction; it no longer imports the old finite classifier.

This distinction matters: "present in the repository" does not mean "a
dependency of the advertised theorem".

## Approach B: analytical hand proof

### Purpose

This is the current proof route and the stronger mathematical target. The
classification must be readable as a continuous geometric/analytic argument,
not as exhaustive angle boxes or a generated stress table.

Allowed ingredients include exact algebra, geometric separating axes, support
inequalities, whole-interval monotonicity and concavity, exact Taylor
inequalities, and finitely many endpoints forced by those analytic reductions.

### Current architecture

The source path at the current head is

```text
Packing
  -> Normalization.normalize_of_candidate
  -> Analytic.FixedPair.complete_reduction
       -> analytic exclusion of MissingWestWing
       -> analytic exclusion of MissingSouthWing
       -> analytic OWN-S upper tail
       -> ReductionInterface
  -> analytic fixed-pair and diagonal closure
  -> retained separating-source witnesses
  -> eight-contact equality reconstruction
  -> Six.lower_bound / Six.uniqueness / Six.optimum
  -> SquaresInCircles.optimal_radius / optimal_packings
```

`Six/LowerBound.lean` imports `Analytic.CompleteReduction` directly.
`Six/Uniqueness.lean` passes `complete_reduction` directly to the equality
reconstruction. Neither public endpoint imports a `Classification` module.

### Main analytical blocks

The proof is split into reviewable pieces:

- normalization and exact candidate geometry;
- whole-domain fixed-pair and diagonal bounds;
- secondary-source reduction and phase restrictions;
- missing-south exclusions, including the large OWN-S case;
- missing-west exclusions for cardinal and OWN branches;
- the final OWN-S upper-tail proof in `Analytic/SouthOuterTail/`;
- `Analytic/CompleteReduction.lean`, which assembles the unconditional
  `ReductionHypotheses`;
- retained-source eight-contact equality reconstruction.

The final south-tail argument deliberately uses a different support estimate at
one exceptional OWN/OWN endpoint. The earlier rectangular scalar profile is not
claimed positive there.

For a reader-oriented outline see `docs/proof/six.md`. The most detailed
analytic companions are:

- `ANALYTIC_NORMALIZATION_PROOF.md`;
- `ANALYTIC_DIAGONAL_PROOF.md`;
- `ANALYTIC_CARDINAL_SOUTH_PROOF.md`;
- `ANALYTIC_SOUTH_TAIL_PROOF.md`.

## Current status of the two routes

| Question | Finite-classification route | Analytical route |
| --- | --- | --- |
| Same public statements? | yes | yes |
| External script success used as a theorem premise? | no | no |
| Uses internal finite covers / generated fixed rows? | yes | no on the intended endpoint path |
| Current public endpoint? | no | yes |
| Source-level reduction complete? | historical yes | yes |
| Lean build run on current head? | not relevant to current endpoint | no |
| Comparator / axiom audit / independent replay run? | no current claim | no |

The analytical route is therefore **source-complete but not yet
machine-validated on the current head**. Compilation and dependency/axiom
inspection remain necessary before describing the n=6 result as kernel-checked.
