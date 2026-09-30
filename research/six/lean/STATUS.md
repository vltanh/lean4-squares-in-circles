# n=6 analytic hand-proof status

PR #7, branch `feat/six-lean-proof`.

## Active target

The current request is to work towards a **completely analytical hand proof**,
with frequent incremental commits. `HUMAN_ANALYTIC_STANDARD.md` is therefore
the active mathematical criterion, not an optional improvement to packaging.
The public `Packing`, `Congruent`, exact candidate and unrestricted theorem
statements are to remain unchanged.

The final proof must not use generated stress tables, substantive finite-box
certification, or an external program's success as a mathematical premise.
Ordinary Lean finite computation is not an external Python oracle, but the
remaining finite classification is still insufficient for this hand-proof
criterion and must be replaced.

Compilation, Comparator, the axiom audit and independent replay remain separate
validation gates. A written proof body is not a record of kernel acceptance.

## Current public endpoint path

The unrestricted source currently has the following path:

```text
Packing
  -> Normalization.normalize_of_candidate
  -> Classification.reduction
       [remaining internal fixed-row / ExactCover classification]
  -> analytic fixed-pair and diagonal closure
  -> retained actual separator witnesses
  -> eight-contact equality and point-set reconstruction
  -> Six.lower_bound / Six.uniqueness / Six.optimum
  -> SquaresInCircles.optimal_radius / optimal_packings
```

The public root and the independent Challenge statements cover every
`1 <= n <= 7`. The old pair-envelope checker and BalancedClosure are not used
by the new radius/equality endpoints. However, `Classification.Reduction` still
imports the internal classification through `CommonDomain`. The complete hand
proof is therefore **not finished**, and the finite classification has not
been removed from the public endpoint path.

## New analytic progress in this continuation

The starting source checkpoint was `158ec1fb3d8cde807ef5f5ff91782378a11e6cf5`.

### Entire cardinal-W missing-south branch

`CardinalSouthTail/Geometry.lean` now supplies
`CardinalSouthTail.not_missing_south`: a normalized packing with cardinal W
cannot have `MissingSouthWing`, regardless of the S central bit.

The previous argument covered only `s<=12/25`. The remaining large-S case has
S OWN. The new proof combines the actual CW, CS, WD and D-sourced DS
inequalities with weights `4,10,3,3`. It retains the negative central x-force,
uses exact disk supports, and proves the resulting scalar positive on its
whole domain by diagonal monotonicity and separate concavity. There are six
distinct geometric endpoint inequalities, proved from explicit Taylor bounds;
there is no angle-grid or fixed-row premise.

The proof is split into reviewable modules:

- `Analytic/CardinalSouthTail/Scalar.lean`: the whole-domain scalar argument.
- `Analytic/CardinalSouthTail/Support.lean`: exact support estimates and rational weakening.
- `Analytic/CardinalSouthTail/Geometry.lean`: actual packing separators and the full branch exclusion.

### Sharper shared-center OWN budget

`CoupledWingBudgetSharp.lean` proves

    P.helperAngle 4 - P.helperAngle 2 < 24/25

for two OWN wings. This improves the previous bound of 1. Its proof uses one
concave affine-gap function on `[22/75,2/3]`, with two Taylor endpoint
inequalities, and the actual shared-center radial sum.

### Smaller remaining domains

`OwnWingFrontier.lean` records the following consequences:

- A missing south wing must have W OWN. The former cardinal-W / large-S
  exception is closed.
- A missing west wing still has `d>3/5` and `d-w>1`.
- If W is cardinal in a missing-west case, S must be OWN.
- If both wings are OWN in a missing-west case, `s-w<24/25` and `d-s>1/25`.

These facts are consequences of a hypothetical missing wing, not assumptions
added to `Packing` and not claims that the remaining region is empty.

`AnalyticReduction.lean` exports the new modules. `SixAxiomAudit.lean` lists
their key declarations for later checking. The hand derivation is written in
`ANALYTIC_CARDINAL_SOUTH_PROOF.md`.

## Exact remaining analytic obligations

`ReductionInterface.reduction_iff_three_obligations` still isolates exactly:

- [ ] Exclude `MissingWestWing` with at least one OWN wing, on the smaller
      domains described above.
- [ ] Exclude `MissingSouthWing` with W OWN.
- [ ] Prove the canonical OWN-S upper tail `helperAngle 4 <= 11/25`.

The lower OWN-S tail is already proved, with the stronger sign `s>0`.
The OWN-W outer tail follows from the two candidate D edges and is not an
additional independent open problem.

Once these three statements exist, replace the imports and body of
`Classification.Reduction` via `reduction_iff_three_obligations`. The analytic
radius and equality modules do not need to be redesigned. Then audit the
complete transitive path to make the fixed-row/ExactCover and associated
reified interval machinery unreachable from the public endpoints.

## Source and validation status

The repository-wide module migration was already present at the starting
checkpoint: its 353 regular Lean files had leading `module` declarations.
The five new Lean modules in this continuation also use `module`, public
imports and public exposure. Visibility/elaboration has not been validated by
a build.

The new hand argument's weighted-sum identity and rational endpoint margins
were cross-checked during development. Such arithmetic cross-checks are not
premises of the Lean declarations and are not substitutes for compiling them.
The source commits use `[skip ci]`; no proof runner has been started here.

The pinned project configuration remains Lean `v4.35.0-rc3` with matching
mathlib, the committed `lake-manifest.json`, and the existing Comparator
configuration. The intended allowed axiom set is only `propext`,
`Classical.choice`, and `Quot.sound`. Metadata is not an executed axiom report.

The final gates remain unexecuted:

- [ ] Full Lean compilation/elaboration, including the new analytic modules.
- [ ] `lake comparator` on the exact final commit.
- [ ] Execute `SixAxiomAudit.lean` and the public-root axiom audit.
- [ ] Confirm no `sorryAx`, `Lean.ofReduceBool`, custom axiom, missing definition,
      or substantive certificate/table dependency on the final theorem path.
- [ ] Independent replay and the registry's mechanical/editorial checks on the
      final pinned commit.

The public endpoints still use finite internal checks today. Their removal is
part of the active mathematics work, not something certified by the unchecked
validation list above.

## Documentation map

- `STATUS.md`: live mathematical progress and validation ledger.
- `HUMAN_ANALYTIC_STANDARD.md`: active hand-proof acceptance criterion.
- `ANALYTIC_CARDINAL_SOUTH_PROOF.md`: new four-edge hand proof and sharper OWN budget.
- `ANALYTIC_NORMALIZATION_PROOF.md`: normalization companion.
- `ANALYTIC_DIAGONAL_PROOF.md`: diagonal scalar companion.
- `NORMALIZATION_DEPENDENCIES.md`: normalization dependency review.
- `EXTERNAL_DEPENDENCY_REMOVAL_CHECKLIST.md`: remaining internal-classification
  boundary and the already removed legacy pair/equality chain.
- `UPLOAD_AUDIT.md` and historical audit data: development evidence only.
