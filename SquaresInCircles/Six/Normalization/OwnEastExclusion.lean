import SquaresInCircles.Six.Normalization.CapSupport

/-!
# No own separator in the east quadrant when `cx > c0`

Let the centre of C have `cx > c0` and `0 ≤ cy ≤ cx + 1/10`. Then a square at an
angle `t` with `|t| ≤ π/4` and radial coordinate `a ≤ ρ0` is not separated from
C along its own axis: the margin
`a - 1/2 - (cx cos t + cy sin t) - (|cos t| + |sin t|)/2` is negative. With
`c = cos |t|` and `s = sin |t|` this reduces to a lower bound for a linear form
on the arc of the unit circle where `0 ≤ s ≤ c`.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

lemma east_quadrant_trig {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.pi / 4) :
    7 / 10 ≤ Real.cos t ∧ 0 ≤ Real.sin t ∧ Real.sin t ≤ Real.cos t := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi ht0
    (show Real.pi / 4 ≤ Real.pi by linarith [Real.pi_pos]) ht
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ t by linarith [Real.pi_pos])
    (show Real.pi / 4 ≤ Real.pi / 2 by linarith [Real.pi_pos]) ht
  rw [Real.cos_pi_div_four] at hc
  rw [Real.sin_pi_div_four] at hs
  have hsqrt : (7 : ℝ) / 10 ≤ Real.sqrt 2 / 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  exact ⟨hsqrt.trans hc,
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos]),
    hs.trans hc⟩

/-- A lower bound for a linear form on the arc of the unit circle where
`0 ≤ s ≤ c`; the coefficient `9/10 - A` comes from `cy ≤ cx + 1/10`. -/
lemma east_linear_support_gt {A k c s : ℝ}
    (hk : k < 63 / 100) (hA : k < A)
    (hc : 7 / 10 ≤ c) (hs : 0 ≤ s) (hcs : s ≤ c)
    (hu : c ^ 2 + s ^ 2 = 1) : k < A * c + (9 / 10 - A) * s := by
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s]
  rcases hc1.eq_or_lt with hc1 | hc1
  · have hs0 : s = 0 := by nlinarith
    rw [hc1, hs0]
    nlinarith
  · have hP := mul_nonneg (show 0 ≤ 1 - c by linarith)
      (show 0 ≤ 58 * c - 40 by linarith)
    have hsbound : (7 / 3) * (1 - c) ≤ s := by
      by_contra! hf
      have hp := mul_pos (sub_pos.mpr hf)
        (show 0 < (7 / 3) * (1 - c) + s by linarith)
      nlinarith
    have hdrop := mul_nonneg (sub_nonneg.mpr hA.le) (sub_nonneg.mpr hcs)
    have hsin := mul_nonneg
      (show 0 ≤ 9 / 10 - k by linarith) (sub_nonneg.mpr hsbound)
    have hreserve := mul_pos
      (show 0 < (7 / 3) * (9 / 10 - k) - k by linarith)
      (show 0 < 1 - c by linarith)
    nlinarith

/-- When `cx > c0` and `0 ≤ cy ≤ cx + 1/10`, the margin of the own separator of
a square in the east quadrant is negative. -/
theorem own_east_margin_negative {a cx cy t : ℝ}
    (ha : a ≤ rho0) (hx : c0 < cx) (hy0 : 0 ≤ cy) (hy : cy ≤ cx + 1 / 10)
    (ht : |t| ≤ Real.pi / 4) :
    a - 1 / 2 - (cx * Real.cos t + cy * Real.sin t) -
      (|Real.cos t| + |Real.sin t|) / 2 < 0 := by
  have htr := east_quadrant_trig (abs_nonneg t) ht
  have hcx0 : 0 < cx := c0_pos.trans hx
  have hA : rho0 - 1 / 2 < 1 / 2 + cx := by
    dsimp [c0] at hx
    linarith
  have hf := east_linear_support_gt
    (A := 1 / 2 + cx) (k := rho0 - 1 / 2)
    (c := Real.cos |t|) (s := Real.sin |t|)
    (by linarith [rho0_upper]) hA htr.1 htr.2.1 htr.2.2
    (by nlinarith [Real.sin_sq_add_cos_sq |t|])
  have hc : 0 ≤ Real.cos t := by
    have hc' := htr.1
    rw [Real.cos_abs] at hc'
    linarith
  rw [Real.cos_abs] at hf
  by_cases ht0 : 0 ≤ t
  · have hs : 0 ≤ Real.sin t := by
      simpa only [abs_of_nonneg ht0] using htr.2.1
    rw [abs_of_nonneg ht0] at hf
    have hp := mul_nonneg
      (show 0 ≤ cx + cy + 1 / 10 by linarith) hs
    rw [abs_of_nonneg hc, abs_of_nonneg hs]
    nlinarith
  · have htneg : t < 0 := lt_of_not_ge ht0
    have hs : Real.sin t ≤ 0 := by
      have hs' := htr.2.1
      rw [abs_of_neg htneg, Real.sin_neg] at hs'
      linarith
    rw [abs_of_neg htneg, Real.sin_neg] at hf
    have hp := mul_nonneg
      (show 0 ≤ cx - cy + 1 / 10 by linarith) (show 0 ≤ -Real.sin t by linarith)
    rw [abs_of_nonneg hc, abs_of_nonpos hs]
    nlinarith

end SquaresInCircles.Six.Normalization
