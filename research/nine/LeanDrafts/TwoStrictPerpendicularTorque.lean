import Mathlib

/-!
# Two-strict perpendicular hub interface: exact torque algebra

UNCOMPILED ordinary-kernel Lean draft, October 30, 2026.
See TWO_STRICT_PERPENDICULAR_AD_REGULAR_ANGLE_TORQUE_REDUCTION_2026_10_30.md.

These lemmas prove only the **algebraic** sign consequences of the actual
unloaded D3 torque, once the geometric support caller has supplied the
displayed equation. The full caller, the circle equations, the singular
physical mask and all-nine-unit conclusion are still OPEN.

No sorry, custom axioms, native_decide or external script/certificate.
The source has not been elaborated or checked by a Lean executable.
-/

namespace SquaresInCircles.Nine.TwoStrictPerpendicularDraft

/-- The regular D3 torque is exactly a positive-factor comparison. -/
theorem regular_D_torque_identity
    (nu gamma H J rho : ℝ)
    (hD : -gamma * rho * H + gamma * J +
      (rho - 1) * (nu + gamma * H) = 0) :
    nu * (1 - rho) = gamma * (J - H) := by
  nlinarith [hD]

/-- For a genuine D roof endpoint, regular D3 torque forces J > H. -/
theorem regular_D_torque_strict
    (nu gamma H J rho : ℝ)
    (hnu : 0 < nu) (hgamma : 0 < gamma) (hrho : rho < 1)
    (hD : -gamma * rho * H + gamma * J +
      (rho - 1) * (nu + gamma * H) = 0) :
    H < J := by
  have heq := regular_D_torque_identity nu gamma H J rho hD
  have hp : 0 < nu * (1 - rho) :=
    mul_pos hnu (sub_pos.mpr hrho)
  have hdiff : 0 < J - H := by
    by_contra hn
    have hle : J - H ≤ 0 := le_of_not_gt hn
    have hprod : gamma * (J - H) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hgamma.le hle
    linarith
  linarith

/-- In the singular J=0 chart the original D exterior side mean is inside
the full interval: there is no automatic unique-corner contradiction. -/
theorem singular_D_mean_interior
    (nu gamma rho lambda : ℝ)
    (hnu : 0 < nu) (hgamma : 0 < gamma) (hrho : 0 < rho)
    (hD : (nu + gamma) * lambda = gamma * rho) :
    0 < lambda ∧ lambda < rho := by
  have hsum : 0 < nu + gamma := by linarith
  have hnum : 0 < gamma * rho := mul_pos hgamma hrho
  have hlambda : 0 < lambda := by
    by_contra hn
    have hle : lambda ≤ 0 := le_of_not_gt hn
    have hprod : (nu + gamma) * lambda ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hsum.le hle
    linarith
  have hlt : lambda < rho := by
    have hprod : 0 < nu * rho := mul_pos hnu hrho
    have hineq : (nu + gamma) * lambda <
        (nu + gamma) * rho := by
      nlinarith [hD, hprod]
    exact (mul_lt_mul_left hsum).mp hineq
  exact ⟨hlambda, hlt⟩

end SquaresInCircles.Nine.TwoStrictPerpendicularDraft
