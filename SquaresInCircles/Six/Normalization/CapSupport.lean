import SquaresInCircles.Six.Normalization.CapBounds

/-!
# The depth of a cap that holds a square

A square in the closed disk of radius `R0` whose frame makes the angle
`t ∈ [0, π/4]` with the axis of the cap `x ≥ h`, and which lies in that cap,
has `h ≤ capDepth t`. Up to the switch angle `capSwitch = arcsin (1/(2 R0))`
the far corner projects on the direction `(cos t, sin t)` at most as far as
`(rho0 + 1/2, 1/2)`, by the tangent of the circle there, which gives
`h ≤ (rho0 - 1/2) cos t - (1/2) sin t`; beyond it Cauchy–Schwarz on the disk
gives `h ≤ R0 - cos t - sin t`. A signed angle `|t| ≤ π/4` reduces to `|t|`.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

lemma disk_linear_support {A B c s : ℝ}
    (hu : c ^ 2 + s ^ 2 = 1) (hbox : A ^ 2 + B ^ 2 ≤ Q0) :
    A * c + B * s ≤ R0 := by
  have hid : (A * c + B * s) ^ 2 + (A * s - B * c) ^ 2 =
      (A ^ 2 + B ^ 2) * (c ^ 2 + s ^ 2) := by ring
  rw [hu, mul_one] at hid
  have hs : (A * c + B * s) ^ 2 ≤ Q0 := by
    nlinarith [sq_nonneg (A * s - B * c)]
  by_contra! h
  have hp := mul_pos (sub_pos.mpr h)
    (show 0 < A * c + B * s + R0 by linarith [R0_nonneg])
  nlinarith [R0_sq]

/-- On the disk `A² + B² ≤ Q0` with `B ≥ b`, the linear form `A c + B s`, with
`c ≥ 0`, is largest at the point `(a, b)` of the circle when `a s ≤ b c`. -/
lemma disk_corner_support {A B a b c s : ℝ}
    (ha : 0 < a) (hB : b ≤ B) (hc : 0 ≤ c)
    (hcircle : a ^ 2 + b ^ 2 = Q0) (hbox : A ^ 2 + B ^ 2 ≤ Q0)
    (hslope : a * s ≤ b * c) : A * c + B * s ≤ a * c + b * s := by
  have ht : a * (A - a) + b * (B - b) ≤ 0 := by
    nlinarith [sq_nonneg (A - a), sq_nonneg (B - b)]
  have hct := mul_nonpos_of_nonneg_of_nonpos hc ht
  have hp := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hB)
  have hprod : a * (A * c + B * s - (a * c + b * s)) ≤ 0 := by
    nlinarith
  by_contra! h
  exact (not_lt_of_ge hprod)
    (mul_pos ha (show 0 < A * c + B * s - (a * c + b * s) by linarith))

lemma cap_low_branch_slope {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ capSwitch) :
    (rho0 + 1 / 2) * Real.sin t ≤ (1 / 2) * Real.cos t := by
  have hpi : capSwitch ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ t by linarith [Real.pi_pos]) hpi ht
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi ht0
    (show capSwitch ≤ Real.pi by linarith [Real.pi_pos]) ht
  rw [sin_capSwitch] at hs
  rw [cos_capSwitch] at hc
  calc
    (rho0 + 1 / 2) * Real.sin t ≤
        (rho0 + 1 / 2) * (1 / (2 * R0)) :=
      mul_le_mul_of_nonneg_left hs (by linarith [rho0_gt_one])
    _ = (1 / 2) * ((rho0 + 1 / 2) / R0) := by
      field_simp [ne_of_gt R0_pos]
    _ ≤ (1 / 2) * Real.cos t := mul_le_mul_of_nonneg_left hc (by norm_num)

/-- A square with `h + (cos t + sin t)/2 ≤ a cos t - b sin t`, the support
inequality of a square in the cap `x ≥ h`, has `h ≤ capDepth t`, for
`0 ≤ t ≤ π/4`. -/
theorem cap_support_bound {a b height t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ Real.pi / 4)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : height + (Real.cos t + Real.sin t) / 2 ≤
      a * Real.cos t - b * Real.sin t) :
    height ≤ capDepth t := by
  have hc : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo
    (show t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos])).le
  have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0
    (by linarith [Real.pi_pos])
  have hA := mul_le_mul_of_nonneg_right (le_abs_self a) hc
  have hB := mul_le_mul_of_nonneg_right (neg_le_abs b) hs
  have hab : height ≤ (|a| + 1 / 2) * Real.cos t +
      (|b| + 1 / 2) * Real.sin t - Real.cos t - Real.sin t := by
    nlinarith
  unfold capDepth
  split_ifs with hbranch
  · have hcorner := disk_corner_support
      (A := |a| + 1 / 2) (B := |b| + 1 / 2)
      (a := rho0 + 1 / 2) (b := (1 : ℝ) / 2)
      (c := Real.cos t) (s := Real.sin t)
      (by linarith [rho0_gt_one]) (by linarith [abs_nonneg b]) hc
      (by nlinarith [rho0_identity]) hbox (cap_low_branch_slope ht0 hbranch)
    dsimp [capFirst]
    nlinarith
  · have hround := disk_linear_support
      (A := |a| + 1 / 2) (B := |b| + 1 / 2)
      (c := Real.cos t) (s := Real.sin t)
      (by nlinarith [Real.sin_sq_add_cos_sq t]) hbox
    dsimp [capSecond]
    linarith

lemma sin_abs_angle {t : ℝ} (ht : |t| ≤ Real.pi) :
    Real.sin |t| = |Real.sin t| := by
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0]
    exact (abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht0
      (by simpa only [abs_of_nonneg ht0] using ht))).symm
  · have htneg : t < 0 := lt_of_not_ge ht0
    have hsin : 0 ≤ Real.sin (-t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by simpa only [abs_of_neg htneg] using ht)
    rw [Real.sin_neg] at hsin
    rw [abs_of_neg htneg, Real.sin_neg, abs_of_nonpos (by linarith)]

/-- The cap depth bound for a signed angle `|t| ≤ π/4`. -/
theorem cap_support_bound_signed {a b height t : ℝ}
    (ht : |t| ≤ Real.pi / 4)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : height + (|Real.cos t| + |Real.sin t|) / 2 ≤
      a * Real.cos t - b * Real.sin t) :
    height ≤ capDepth |t| := by
  have hangle : |t| ≤ Real.pi := by linarith [Real.pi_pos]
  have hc : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo
    (show t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      have hb := abs_le.mp ht
      constructor <;> linarith [Real.pi_pos])).le
  have hA := mul_le_mul_of_nonneg_right (le_abs_self a) hc
  have hB : -(b * Real.sin t) ≤ |b| * |Real.sin t| := by
    simpa only [abs_mul] using neg_le_abs (b * Real.sin t)
  apply cap_support_bound (a := |a|) (b := -|b|) (abs_nonneg t) ht
  · simpa only [abs_abs, abs_neg] using hbox
  · rw [Real.cos_abs, sin_abs_angle hangle]
    rw [abs_of_nonneg hc] at hcap
    nlinarith

end SquaresInCircles.Six.Normalization
