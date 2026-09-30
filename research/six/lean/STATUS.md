# n=6 proof status and Palomar readiness

PR #7, branch `feat/six-lean-proof`.

This is the live status ledger for the six-square extension. The final
acceptance target is now **Palomar Registry compatibility**: the advertised
Solution declarations must be self-contained Lean proofs accepted by Comparator
with only `propext`, `Classical.choice`, and `Quot.sound`, and must not
depend on `sorryAx`, `Lean.ofReduceBool` / `native_decide`, a custom axiom,
an unnamed missing definition, or the success of an external script.

Ordinary Lean computation such as `decide` is permitted. External research,
Python replay, audit logs and numerical experiments may remain in the
repository, but their success is not a theorem premise.

The stronger human-analytic conversion in `HUMAN_ANALYTIC_STANDARD.md`
remains useful research work, but it is no longer the gate for Palomar
submission.

## Palomar-facing theorem path

The current unrestricted source already has the complete endpoint chain:

- `Six/LowerBound.lean` proves the unrestricted radius lower bound.
- `Six/Uniqueness.lean` proves equality classification and supplies
  `Optimum 6`.
- `SquaresInCircles.lean` includes case 6 in the two declarations compared by
  `comparator.json`.
- `Challenge.lean` independently states the same two public declarations for
  every `1 <= n <= 7`.

The legacy fixed-row/common-pair route uses finite data and ordinary kernel
`decide` through proved soundness lemmas. It does not call an external script
at theorem elaboration time. Under the current Palomar criterion this route is
eligible in principle; actual acceptance still requires the build, Comparator,
axiom audit and NanoDa replay on the final pinned commit.

## Static Palomar checks already satisfied

- [x] Public repository and immutable commits available.
- [x] `Challenge.lean` is 297 lines and about 10 KiB, below Palomar's
      1,000-line / 100 KiB hard limits and its 300-line warning threshold.
- [x] Challenge imports Mathlib only.
- [x] Challenge and Solution module names are distinct:
      `Challenge` and `SquaresInCircles`.
- [x] `comparator.json` compares nonempty theorem declarations and permits
      exactly `propext`, `Quot.sound`, `Classical.choice`.
- [x] PR diff contains no use of `Lean.ofReduceBool`, `run_tac`, external
      process invocation or custom `axiom`; the only `sorry` additions are
      the two deliberate Challenge theorem holes.
- [x] The apparent `native_decide` hit in the Six proof is documentation saying
      that the source uses ordinary `decide`, not an invocation.
- [x] Lean toolchain is `leanprover/lean4:v4.35.0-rc3`.
- [x] Mathlib is pinned to the matching `v4.35.0-rc3`.
- [x] Root uses `lakefile.toml` and has a committed `lake-manifest.json`.
- [x] Root has one Apache-2.0 `LICENSE`, matching `project.license`.
- [x] `formalization.yaml` is v0.4 and has been updated to include n=6,
      Palomar's source-type vocabulary, honest six-square provenance, and no
      unexecuted kernel/NanoDa success claim.

## Current hard Palomar blocker: Lean module system

Palomar now requires **every regular .lean file in the submitted repository**
to use Lean's module system, including unused files and generated certificates.
The present repository predates that migration: for example
`Challenge.lean` and `SquaresInCircles.lean` do not yet start with
`module`.

The compatibility migration must therefore be completed repository-wide:

- [ ] Prefix every regular `.lean` source with `module`.
- [ ] Convert imports needed by clients to `public import`.
- [ ] Initially expose the existing public API using the compatibility recipe
      (`@[expose] public section` / targeted exposure), then repair visibility
      errors rather than weakening statements.
- [ ] Keep every source file below 10,000 physical lines.
- [ ] Rebuild after the migration; a textual header edit alone is not enough.

## Final mechanical gates before submission

These results must be obtained from the exact final commit; they are not
inferred from source inspection:

- [ ] Full `lake build` on the Palomar-supported toolchain.
- [ ] `lake comparator` with the checked-in `comparator.json`.
- [ ] `#print axioms` for `SquaresInCircles.optimal_radius`,
      `SquaresInCircles.optimal_packings`, `Six.lower_bound` and
      `Six.uniqueness`; only the standard three axioms may remain.
- [ ] Confirm no Solution dependency introduces `sorryAx`,
      `Lean.ofReduceBool`, a custom axiom or an unnamed missing definition.
- [ ] Submit the exact 40-character commit to Palomar and let Palomar perform
      its mandatory independent NanoDa replay and metadata/editorial checks.

No GitHub Actions or other remote proof runner is being used as a substitute
for those final checks in this development session.

## Optional stronger analytic track

The human-analytic conversion has already replaced normalization, the fixed
pair envelope on its explicit domain, the corrected diagonal remainder, large
parts of the D-edge classification, and several tail arguments. Its remaining
mixed-wing reductions are valuable if a certificate-free mathematical proof is
desired in the stronger sense of eliminating finite Lean tables. They are not
required merely to satisfy Palomar's current mechanical proof standard.

## Documentation map

- `STATUS.md` — this Palomar/readiness ledger.
- `HUMAN_ANALYTIC_STANDARD.md` — optional stronger analytic standard.
- `ANALYTIC_NORMALIZATION_PROOF.md` — normalization companion.
- `ANALYTIC_DIAGONAL_PROOF.md` — diagonal scalar companion.
- `NORMALIZATION_DEPENDENCIES.md` — normalization dependency review.
- `UPLOAD_AUDIT.md` and audit data — historical development evidence only.


## External-dependency removal plan

The detailed static audit and removal plan is
`EXTERNAL_DEPENDENCY_REMOVAL_CHECKLIST.md`. It is the authoritative checklist
for eliminating certificate-era fixed-row, finite-cover, pair-envelope, and
historical external-result dependencies from the transitive path of the n=6
lower-bound and uniqueness theorems. Compilation is a separate later phase.
