# n=6 human-analytic proof status

PR #7, branch `feat/six-lean-proof`.

This is the single live progress ledger for the n=6 proof. Checked items mean
that the analytic argument, Lean proof body, and relevant source call sites have
been written. They do **not** mean Lean compilation or kernel/axiom acceptance;
those remain deferred.

The acceptance criterion is `HUMAN_ANALYTIC_STANDARD.md`. The original
`Packing` and `Congruent` predicates are unchanged.

## Current frontier

Analytic normalization is complete through
`Normalization.normalize_of_candidate`. The fixed-pair envelope and corrected
diagonal remainder are also written analytically on their explicit domains.
The remaining mathematical work is concentrated in two mixed D-edge source
cases and three OWN-wing tail inequalities.

For `Stress.pairNormal` on ordered pairs W/D and D/S:

| W/D | D/S | Sources | Status |
|---:|---:|---|---|
| 2 | 6 | W-secondary / S-secondary | candidate graph |
| 6 | 2 | D-secondary / D-secondary | analytically excluded |
| 6 | 6 | D-secondary / S-secondary | **open: MissingWestWing** |
| 2 | 2 | W-secondary / D-secondary | **open: MissingSouthWing** |

The historical 53-cell hard table corresponds to the mixed `(6,6)` case, not
the already excluded double-D-secondary case.

## Completed: normalization

- [x] Strong central box from genuine marker/SAT arguments, before pins/sectors.
- [x] Five-pin covering from direct geometry and the sixty-degree pin lemma.
- [x] Unique pin labels and all broad angular windows.
- [x] Allowed central axes from pin coordinates and strong-core exclusions.
- [x] OWN moving pins and cardinal cap-piercing cases.
- [x] W/D order and cyclic primary order.
- [x] One explicitly recorded global diagonal reflection.
- [x] Opposite-cardinal budgets with both hypotheses retained.
- [x] N25+ and exact candidate-radius cardinal refinements.
- [x] Analytic Appendix A, including D canonically OWN.
- [x] `normalize_of_ceiling` and `normalize_of_candidate` use the analytic path.

Human-readable companion: `ANALYTIC_NORMALIZATION_PROOF.md`.
Static review scope: `NORMALIZATION_DEPENDENCIES.md`.

## Completed: pair and diagonal scalar closure

- [x] Fixed central-edge pair stress with explicit central-force correction.
- [x] Actual N/W and E/S pair work connected to packing separators.
- [x] Exact smooth sector formulas and positive radicands.
- [x] Coordinate/diagonal concavity and geometrically forced endpoint reduction.
- [x] `FixedPair.lower_bound` on the explicit bit-dependent `Domain`, with
      the `|n|/1000` reserve.
- [x] Correct negative-side line slope `18/25`.
- [x] Corrected diagonal cap/vertex remainder on its explicit domain.
- [x] Diagonal remainder nonnegative with unique zero.
- [x] Actual candidate D-edge work matches the pair transverse residual.
- [x] Strict D support gives strict total work below the candidate radius.
- [x] `FixedCandidateClosure` proves angle/source/radius rigidity from
      `ReductionHypotheses`.

Human-readable diagonal companion: `ANALYTIC_DIAGONAL_PROOF.md`.

## Completed: analytic source reduction

- [x] All W/D primary and reverse-secondary sources excluded.
- [x] Full-range existence of a forward-secondary D/S separator.
- [x] Canonical OWN W has negative deviation.
- [x] Low-diagonal OWN-W and cardinal-W regions excluded analytically.
- [x] `normalized_diagonal_gt_half`: `d > 1/2` for both W bits.
- [x] High-D radial/transverse bounds.
- [x] Both D-sourced phase gaps exceed `pi/4`.
- [x] Candidate W edge is automatic on `w >= d-pi/4`.
- [x] Candidate S edge is automatic on `s <= d-pi/4`.
- [x] Double-D-secondary case excluded for all four W/S central-bit choices.
- [x] At least one actual candidate wing separator always exists.
- [x] `candidate_or_missing_wing` gives the exact remaining source split.
- [x] `reduction_iff_remaining_obligations` reduces the full scalar closure to
      missing-wing exclusions plus OWN-wing tails.

## Open mathematical obligations

These are the substantive source-level tasks that still block the unrestricted
human-analytic theorem.

- [ ] Exclude `MissingWestWing`: mixed `(6,6)`, including the historical
      53-cell hard region.
- [ ] Exclude `MissingSouthWing`: mixed `(2,2)`.
- [ ] OWN-W lower tail: if W is OWN, prove `-11/25 <= w`.
- [ ] OWN-S lower tail: if S is OWN, prove `-2/25 <= s`.
- [ ] OWN-S upper tail: if S is OWN, prove `s <= 11/25`.

Once these five facts are proved:

- [ ] Assemble unconditional `ReductionHypotheses`.
- [ ] Switch the final closure away from the old pair/fixed-row dependency path.
- [ ] Reconnect exact radius, support equality, reconstruction, and reflection absorption.
- [ ] Verify `Six.lower_bound`, `Six.uniqueness`, and public `Optimum 6`
      depend only on the analytic chain.
- [ ] Complete the final transitive dependency review.

## Validation boundary

No numerical search, interval subdivision, generated stress-table success flag,
or external program result is a permitted premise of the final theorem.
Historical computational files and audit logs may remain for comparison, but
must not occur on the final mathematical dependency path.

Compilation and execution of the axiom audit are still deferred. The canonical
audit entry point is now `SixAxiomAudit.lean`; its `#print axioms` commands are
configuration for the later audit, not recorded output.

## Documentation map

- `STATUS.md` — this live ledger; all older checklist/progress files were merged here.
- `HUMAN_ANALYTIC_STANDARD.md` — acceptance rules.
- `ANALYTIC_NORMALIZATION_PROOF.md` — normalization companion.
- `ANALYTIC_DIAGONAL_PROOF.md` — diagonal scalar companion.
- `NORMALIZATION_DEPENDENCIES.md` — scoped normalization dependency review.
- `UPLOAD_AUDIT.md` and audit data — historical computer-assisted-route evidence only.
