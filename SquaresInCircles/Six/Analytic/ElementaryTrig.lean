import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Elementary analytic bounds for the human proof

This module imports only mathlib. Its inequalities are consequences of sine
and cosine on their ordinary sign intervals; there is no expression evaluator,
interval subdivision, generated table, or certificate-success premise.

The stress sign is explained by
  cos x + sin x = sqrt(2) * sin (x + pi/4).
Thus positivity is a single geometric interval statement, not two finite
numerical covers. Compiler validation is deferred, as elsewhere in this branch.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

/-- The first stress denominator and numerator are positive throughout the
single conceptual angle interval (-pi/4, pi/2). -/
theorem stress_angle_sign {x : ℝ}
    (hlo : -Real.pi / 4 < x) (hhi : x < Real.pi / 2) :
    0 < Real.cos x ∧ 0 < Real.cos x + Real.sin x := by
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hhi⟩
  have hs : 0 < Real.sin (x + Real.pi / 4) :=
    Real.sin_pos_of_pos_of_lt_pi
      (by linarith) (by linarith [Real.pi_pos])
  rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four] at hs
  have hh : 0 ≤ Real.sqrt 2 / 2 := by positivity
  refine ⟨hc, ?_⟩
  by_contra! h
  have hp := mul_nonpos_of_nonneg_of_nonpos hh h
  nlinarith only [hs, hp]

/-- Whole-domain sign proof for the west adjacent-pair stress. -/
theorem west_stress_sign {w : ℝ} (hw : -2 / 3 ≤ w ∧ w ≤ 5 / 8) :
    0 < Real.cos w ∧ 0 < Real.cos w + Real.sin w := by
  apply stress_angle_sign
  · linarith [hw.1, Real.pi_gt_d2]
  · linarith [hw.2, Real.pi_gt_d2]

/-- Whole-domain sign proof for the east adjacent-pair stress. -/
theorem east_stress_sign {e : ℝ} (he : -5 / 12 ≤ e ∧ e ≤ 3 / 10) :
    0 < Real.cos e ∧ 0 < Real.cos e + Real.sin e := by
  apply stress_angle_sign
  · linarith [he.1, Real.pi_gt_d2]
  · linarith [he.2, Real.pi_gt_d2]

end SquaresInCircles.Six.Analytic
