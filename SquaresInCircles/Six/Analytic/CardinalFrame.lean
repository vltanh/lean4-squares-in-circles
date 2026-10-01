import SquaresInCircles.Six.Normalization.CapSupport

/-!
# A deep cap faces the primary axis

A square with frame coordinates `(a, b)`, `|b| < 1/2`, that lies in a cap of
depth at least `coreRadius` and has its phase within `3π/4` of the cap normal,
has its phase within `2/5` of it. Within `π/4` this is the cap angle bound.
Beyond, a quarter turn of the frame exchanges the two coordinates, so the cap
faces the short coordinate; the cap angle bound gives `|sin t| < 2/5`, and the
cap is at most `(rho0 - 1/2) · 2/5` deep, less than `coreRadius`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private theorem short_axis_cap_impossible {a b h t : ℝ}
    (ha : |a| < 1 / 2) (hb : |b| ≤ rho0)
    (hh : coreRadius ≤ h) (ht : |t| ≤ Real.pi / 4)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : h + (|Real.cos t| + |Real.sin t|) / 2 ≤
      a * Real.cos t - b * Real.sin t) : False := by
  have hprofile := cap_support_bound_signed ht hbox hcap
  have hsmall : |t| < 2 / 5 := cap_angle_lt_two_fifths hh hprofile ht
  have hc : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo
    (show t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      have h := abs_le.mp ht
      constructor <;> linarith [h.1, h.2, Real.pi_pos])).le
  have hs : |Real.sin t| ≤ 2 / 5 := by
    have h := Real.abs_sin_sub_sin_le t 0
    simp only [Real.sin_zero, sub_zero] at h
    exact h.trans hsmall.le
  have hfirst := mul_le_mul_of_nonneg_right (le_abs_self a) hc
  have hsecond : -(b * Real.sin t) ≤ |b| * |Real.sin t| := by
    simpa only [abs_mul] using neg_le_abs (b * Real.sin t)
  have hshort := mul_nonpos_of_nonpos_of_nonneg
    (show |a| - 1 / 2 ≤ 0 by linarith) hc
  have htrans := mul_le_mul_of_nonneg_right hb (abs_nonneg (Real.sin t))
  have hcaploss := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ rho0 - 1 / 2 by linarith [rho0_lower])
  rw [abs_of_nonneg hc] at hcap
  nlinarith [coreRadius_gt_77_200, rho0_upper]

/-- A square with `|b| < 1/2` in a deep cap, with phase `|t| ≤ 3π/4`, has
`|t| < 2/5`. -/
theorem primary_cap_angle {a b h t : ℝ}
    (ha : |a| ≤ rho0) (hb : |b| < 1 / 2)
    (hh : coreRadius ≤ h) (ht : |t| ≤ 3 * Real.pi / 4)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : h + (|Real.cos t| + |Real.sin t|) / 2 ≤
      a * Real.cos t - b * Real.sin t) : |t| < 2 / 5 := by
  have hwide := abs_le.mp ht
  by_cases hhi : t ≤ Real.pi / 4
  · by_cases hlo : -Real.pi / 4 ≤ t
    · have hsmall : |t| ≤ Real.pi / 4 := abs_le.mpr ⟨by linarith, hhi⟩
      exact cap_angle_lt_two_fifths hh (cap_support_bound_signed hsmall hbox hcap) hsmall
    · have hfold : |t + Real.pi / 2| ≤ Real.pi / 4 := by
        apply abs_le.mpr
        constructor <;> linarith [hwide.1]
      have hc : Real.cos (t + Real.pi / 2) = -Real.sin t := by
        simp [Real.cos_add]
      have hs : Real.sin (t + Real.pi / 2) = Real.cos t := by
        simp [Real.sin_add]
      have hbox' : (|b| + 1 / 2) ^ 2 + (|-a| + 1 / 2) ^ 2 ≤ Q0 := by
        simpa only [abs_neg, add_comm] using hbox
      have hcap' : h + (|Real.cos (t + Real.pi / 2)| + |Real.sin (t + Real.pi / 2)|) / 2 ≤
          b * Real.cos (t + Real.pi / 2) - (-a) * Real.sin (t + Real.pi / 2) := by
        rw [hc, hs, abs_neg]
        nlinarith only [hcap]
      exact False.elim (short_axis_cap_impossible hb
        (by simpa only [abs_neg] using ha) hh hfold hbox' hcap')
  · have hfold : |t - Real.pi / 2| ≤ Real.pi / 4 := by
      apply abs_le.mpr
      constructor <;> linarith [hwide.2]
    have hc : Real.cos (t - Real.pi / 2) = Real.sin t := by
      simp [Real.cos_sub]
    have hs : Real.sin (t - Real.pi / 2) = -Real.cos t := by
      simp [Real.sin_sub]
    have hbox' : (|-b| + 1 / 2) ^ 2 + (|a| + 1 / 2) ^ 2 ≤ Q0 := by
      simpa only [abs_neg, add_comm] using hbox
    have hcap' : h + (|Real.cos (t - Real.pi / 2)| + |Real.sin (t - Real.pi / 2)|) / 2 ≤
        (-b) * Real.cos (t - Real.pi / 2) - a * Real.sin (t - Real.pi / 2) := by
      rw [hc, hs, abs_neg]
      nlinarith only [hcap]
    exact False.elim (short_axis_cap_impossible
      (by simpa only [abs_neg] using hb) ha hh hfold hbox' hcap')

end SquaresInCircles.Six.Analytic
