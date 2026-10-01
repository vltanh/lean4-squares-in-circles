import SquaresInCircles.Six.Stress.DiagonalVertexBound

/-!
# Human-analytic diagonal remainder and equality

Both support branches are proved by ordinary inequalities. The cap branch
has the explicit reserve (|w|+|s|)/40; the vertex branch is strictly positive
by the diamond reduction, concavity, and two quartic chords.

This module needs no pair-envelope lower bound, fixed-row classification,
normalization certificate, interval evaluator, or external certificate file.
Its DiagonalDomain hypothesis is explicit: deriving that domain from arbitrary
packings remains part of the separate analytic-conversion task.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress

def diagonalRemainder (w s d : ℝ) : ℝ :=
  pairLine w + pairLine (-s) + diagonalValue w s d + 2 * pairBase

/-- The scalar diagonal remainder is nonnegative on the whole stated domain. -/
theorem diagonal_remainder_nonnegative {w s d : ℝ} (hd : DiagonalDomain w s d) :
    0 ≤ diagonalRemainder w s d := by
  rw [diagonalRemainder, diagonal_value_formula hd]
  by_cases hc : 2 * Six.radius * |Real.sin (diagonalDelta w s d)| ≤ 1
  · rw [if_pos hc]
    have hh := diagonal_cap_remainder_lower hd
    nlinarith [abs_nonneg w, abs_nonneg s]
  · rw [if_neg hc]
    exact (diagonal_vertex_remainder_positive hd (le_of_not_ge hc)).le

/-- Its only zero has exactly the candidate angles. -/
theorem diagonal_remainder_zero {w s d : ℝ} (hd : DiagonalDomain w s d)
    (heq : diagonalRemainder w s d = 0) : w = 0 ∧ s = 0 ∧ d = Real.pi / 4 := by
  rw [diagonalRemainder, diagonal_value_formula hd] at heq
  by_cases hc : 2 * Six.radius * |Real.sin (diagonalDelta w s d)| ≤ 1
  · rw [if_pos hc] at heq
    exact diagonal_cap_zero_iff hd heq
  · rw [if_neg hc] at heq
    have hh := diagonal_vertex_remainder_positive hd (le_of_not_ge hc)
    linarith

end SquaresInCircles.Six.Stress
