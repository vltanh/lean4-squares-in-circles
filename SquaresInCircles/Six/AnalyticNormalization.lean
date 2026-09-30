module
public import SquaresInCircles.Six.Normalization.StrongCardinal
public import SquaresInCircles.Six.Stress.CandidateCardinal

@[expose] public section

/-!
# Analytic normalization of an arbitrary six-square packing

The entry points exported here are `Normalization.normalize_of_ceiling` and
`Normalization.normalize_of_candidate`. Their input is the original `Packing`
predicate and the indicated radius ceiling. Strong-core exclusion comes before
pins and sectors; the five-pin covering, labelled windows, W/D order, moving
pins and Appendix A are analytic arguments. The one possible diagonal
reflection is recorded in the output relation, not silently spent twice.

This entry point also exports N25+ for cardinal E/N and the candidate-radius
opposite-cardinal budgets. Both opposite-cardinal hypotheses remain explicit.
The legacy `Normalization.Certificates` namespace used for the fixed pin
constants does not import or execute a checker.

No fixed D-edge classification, interval-cover engine, pair-envelope checker,
unrestricted lower-bound theorem or uniqueness theorem is imported here.
Those downstream analytic conversions are separate unfinished work.
Compilation and kernel/axiom acceptance remain deferred. This file records the
completed analytic normalization source chain, not an executed Lean build.

See `research/six/lean/ANALYTIC_NORMALIZATION_PROOF.md` and
`research/six/lean/NORMALIZATION_DEPENDENCIES.md` for the mathematical argument
and the precise scope of the static dependency review.
-/
