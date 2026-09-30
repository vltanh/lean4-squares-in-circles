import SquaresInCircles.Six.AnalyticNormalization
import SquaresInCircles.Six.Analytic.ElementaryTrig
import SquaresInCircles.Six.Analytic.CardinalFrame
import SquaresInCircles.Six.Analytic.CandidateBounds
import SquaresInCircles.Six.Stress.DiagonalRemainder

/-!
# Human-analytic checkpoint for the six-square proof

The complete analytic normalization is now included: original Packing ->
strong core -> five-pin covering and unique labels -> broad windows and
central axes -> one recorded diagonal reflection -> W/D order, moving pins,
cardinal budgets and the analytic Appendix A exclusion -> normalized model.
N25+ and the exact candidate-radius cardinal budgets are also available.

The diagonal cap/vertex remainder is analytic on its stated DiagonalDomain,
including its unique zero. The current proof that every packing reaches that
later, tighter domain still uses fixed D-edge rows and tails. The common pair
envelope also still has computational dependencies. Those two downstream
conversions, and reconnection of the unrestricted endpoints through them,
remain unfinished and are deliberately excluded from this entry point.

No interval-cover engine, generated stress-table check, pair-envelope
certificate or Python result is imported by this checkpoint. A few historical
names retain the word Certificates only for ordinary real pin constants.
Compilation and kernel/axiom acceptance are deferred, not inferred from source
completion or the static import review.

See `research/six/lean/ANALYTIC_PROGRESS.md`,
`ANALYTIC_NORMALIZATION_PROOF.md` and `ANALYTIC_DIAGONAL_PROOF.md`.
-/
