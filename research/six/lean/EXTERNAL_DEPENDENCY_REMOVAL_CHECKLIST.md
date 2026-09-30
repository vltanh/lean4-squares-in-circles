# n=6 proof dependency checklist

Source review only. Compilation, Comparator and kernel/axiom execution remain
explicitly deferred. The initial checkpoint for this continuation was
`132b54cb08b1f039b4038eb08c68cafdc2f52dcb`.

## Two distinct requirements

The user explicitly requires a self-contained Lean proof with **no external
script success used as a theorem premise**. Ordinary Lean `decide` is not an
external process or an imported PASS flag. The earlier version of this ledger
incorrectly described removal of every internal finite cover as part of that
external-dependency requirement.

The stronger, entirely table-free analytic conversion is tracked separately
below. Its outstanding cases must not be called solved merely because an
internal Lean classification theorem already proves the required conclusion.
Conversely, an internal Lean checker must not be described as calling Python
when it does not do so.

There is no new external script, file read, imported Boolean success artifact,
custom axiom, `sorry`, `native_decide`, or `Lean.ofReduceBool` in the proof
changes of this continuation. The historical research scripts are not invoked
by the new theorem chain. This static observation is not a kernel audit.

## Current endpoint path

```text
original Packing
  -> Normalization.normalize_of_candidate
  -> Classification.reduction
       [remaining internal fixed-row classification is isolated here]
  -> analytic FixedPair.lower_bound / diagonal remainder
  -> SelectedPairWork, retaining the actual source witnesses
  -> eight real contacts and unique disk support
  -> exact point-set reconstruction and reflection absorption
  -> Six.lower_bound / Six.uniqueness / Six.optimum
  -> SquaresInCircles.optimal_radius / optimal_packings
```

The public theorem signatures and `Packing`, `Congruent`, Geometry and
Challenge were not changed during this continuation. The new endpoint path
has no additional unproved premise: `Classification.reduction P` supplies its
explicit reduction input using the existing internal Lean proofs. The complete
source has not been compiled, so elaboration and kernel acceptance are unclaimed.

## Completed: remove the old pair-certificate route from both endpoints

- [x] Preserve actual N/W and E/S source inequalities in `SelectedPairs`.
- [x] Prove work bounds for each supplied source, not just an existential scalar value.
- [x] Retain those same sources through analytic angle/source/radius rigidity.
- [x] Stop importing `Stress.PairLowerBound` from the radius endpoint.
- [x] Route `Six.lower_bound` through `FixedPair.radius_of_reduction`.
- [x] Remove `BalancedClosure` from generic `Equality.LocalCenters`.
- [x] Make the old adapter's dependency explicit in `Equality.SupportRigidity`.
- [x] Derive all eight candidate-frame contacts from the actual packing and retained sources.
- [x] Prove support tightness by the exact positive weighted sum of those contacts.
- [x] Fix all five exterior centers by the unique disk-support lemmas.
- [x] Fix the central center by the two pairs of opposite central inequalities.
- [x] Reconstruct open and closed square point sets without the old equality adapter.
- [x] Absorb the one recorded diagonal reflection using the candidate's actual symmetry.
- [x] Route `Six.uniqueness` through `Equality.AnalyticReconstruction`.
- [x] Make `Six.lean` export the actual new endpoint path.
- [x] Configure the deferred axiom audit to import the public root and list the new lemmas.

Replacement modules:

| Module | Role |
|---|---|
| `Analytic/SelectedPairWork.lean` | Actual selected sources, work inequalities, rigidity with witnesses |
| `Equality/ContactCoordinates.lean` | Eight-contact scalar support saturation and center uniqueness |
| `Equality/AnalyticContacts.lean` | Actual packing geometry supplies those contacts |
| `Equality/AnalyticReconstruction.lean` | Candidate point sets and recorded reflection |
| `Classification/Reduction.lean` | Explicit boundary to the remaining internal classification |

### Static import evidence

The complete PR patch at source checkpoint
`4dc8948d5bb23ea7e6d571766782e8a366166952` was searched for incoming imports.
The module migration makes the relevant import headers visible in that patch.
The old chain is now:

```text
Equality.Reconstruction                     [no incoming repository import found]
  -> Equality.SupportRigidity               [only imported by that legacy Reconstruction]
  -> Stress.BalancedClosure                 [only imported by legacy SupportRigidity]
  -> Stress.PairLowerBound                  [only imported by BalancedClosure]
  -> Stress.PairLocal                       [only imported by PairLowerBound]
  -> Stress.PairCertificateChecks           [only imported by PairLocal]
  -> Stress.PairCertificateModel            [only imported by PairCertificateChecks]
  -> ProofTools.SmoothCalculus              [only imported by PairCertificateModel]
```

`Six.lower_bound` and `Six.uniqueness` no longer import this chain. The files
remain available as historical source; deleting them is not needed to stop
using their proof route. This is a scoped source-import review, not a complete
elaborated declaration-dependency or axiom inventory.

## Remaining internal classification: explicit, not removed

`Classification.Reduction` still imports `Classification.CommonDomain` and
therefore uses the existing internal Lean fixed-row/domain-cover proofs:

- [ ] Replace the remaining `Classification.CandidateGraph` case reductions analytically.
- [ ] Replace the remaining `CandidateTails` / `CommonDomain` south upper-tail argument.
- [ ] Make `Stress.FixedData.Default`, `Hard`, `Tails`, `AppendixC`, `Bridges`
      and `Checks` unreachable from the public endpoints.
- [ ] Make `Stress.ExactCover`, `RowTactics`, `FixedRow`, `FixedReification`,
      `FixedGraph` and `FixedGeometry` unreachable from the public endpoints.
- [ ] Remove remaining reified interval machinery once the fixed-row boundary is gone.

These are **internal Lean proof dependencies**, not external-script calls.
They use explicit data, proved checker soundness and ordinary `decide` proof
bodies. Their concrete Lean execution remains untested here. They are permitted
by the no-external-script criterion, but remain unfinished under the stronger
human-analytic/table-free criterion.

### Exact outstanding analytic mathematics

The shared `Analytic.ReductionInterface` already proves that the stronger
conversion needs only:

- [ ] `not_missing_west`: exclude `MissingWestWing`, the mixed (6,6) source case.
- [ ] `not_missing_south`: exclude `MissingSouthWing`, the mixed (2,2) source case.
- [ ] `south_outer`: prove or derive the canonical OWN-S bound `s <= 11/25`.

The lower OWN-S tail is proved independently. The OWN-W lower tail follows
from the candidate D-edge graph, so neither is an independent open item.
The both-cardinal branch is already closed. A missing west wing forces
`d > 3/5`. These facts shrink the task but do not prove the three lines above.

When those lemmas exist, replace the body/imports of `Classification.Reduction`
using `reduction_iff_three_obligations`. The new radius, contact, reconstruction
and uniqueness modules will not need another proof redesign.

## Normalization and generic tools

- [x] The actual normalization interface uses the analytic core/pin/window,
      moving-pin, W/D-order and Appendix A path.
- [x] `Normalization.PinData` contains ordinary real pin constants; its
      historical `Certificates` namespace name is not an external dependency.
- [x] The former diagonal checker is only a wrapper around an analytic theorem.
- [ ] Complete the full final import/declaration inventory before claiming
      every historical normalization/checker module is unreachable.

`ProofTools.Certificate`, `Expression`, `RationalInterval`, `TrigInterval` and
related support syntax remain reachable through the internal classification.
The pair-specific `SmoothCalculus` path has been bypassed as described above.
Neither fact should be hidden by a rename or a blanket file-name scan.

## Historical scripts and artifacts

The following are development/replay material, not premises of the new Lean
proof bodies:

- `research/six/check_normalization_*.py` and `n6_normalization_*.py`;
- `research/six/normalization_cert/*.py`, its manifest and unit-test log;
- `research/six/check_A2_*.py`, `n6_a2_fixed.py`, `n6_a2_scalar.py`;
- `research/six/lean/check_algebra.py`, `check_cap_algebra.py`,
  `test_source_audit.py`, algebra/source/audit JSON files and historical logs;
- `scripts/audit-six-sources.py` and `scripts/verify-six-foundations.sh`.

- [x] No new theorem invokes these scripts or assumes their reported success.
- [ ] Complete a repository-wide static execution/import inventory before
      making an exhaustive no-external-execution claim about every file.
- [ ] Archive legacy research artifacts only after their references are reviewed;
      do not remove them merely because they are scripts.

Figure scripts, documentation-link tools and Comparator build wrappers are not
mathematical oracle dependencies. No GitHub proof runner was started here.

## Validation not performed

- [ ] Lean compilation and elaboration.
- [ ] Concrete execution of the retained internal finite checks.
- [ ] Endpoint `#print axioms` output.
- [ ] Comparator / independent kernel replay.

The user requested that compilation be skipped. None of these unchecked gates
is being represented as a successful run or as registry acceptance.
