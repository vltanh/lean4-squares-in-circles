module
public import SquaresInCircles.Six.AnalyticNormalization
public import SquaresInCircles.Six.Analytic.ElementaryTrig
public import SquaresInCircles.Six.Analytic.CardinalFrame
public import SquaresInCircles.Six.Analytic.CandidateBounds
public import SquaresInCircles.Six.Stress.DiagonalRemainder

@[expose] public section

/-!
# Human-analytic checkpoint for the six-square proof

This entry point collects the completed analytic normalization together with
the earlier candidate-constant and diagonal-remainder results. The later
candidate-edge/domain reduction has its own isolated checkpoint in
`SquaresInCircles/Six/AnalyticReduction.lean`.

The unrestricted lower-bound and uniqueness endpoints are deliberately not
treated as completed here. The remaining source obligations are the two mixed
missing-wing exclusions and the three OWN-wing tail inequalities recorded in
`research/six/lean/STATUS.md`. Once those supply `ReductionHypotheses`, the
already written fixed-pair candidate closure can replace the old computational
downstream path.

No interval-cover engine, generated stress-table check, pair-envelope
certificate or Python success result is a mathematical premise of this
checkpoint. Historical names containing `Certificates` may still denote
ordinary real pin constants.

Compilation and kernel/axiom acceptance remain deferred and are not inferred
from source completion or static dependency review.

See `research/six/lean/STATUS.md`,
`ANALYTIC_NORMALIZATION_PROOF.md` and `ANALYTIC_DIAGONAL_PROOF.md`.
-/
