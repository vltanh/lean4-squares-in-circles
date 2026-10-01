import SquaresInCircles.Six.Normalization.CapIdentities
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Bounds on the cap depth

Rational bounds `3/2 < R0 < 1689/1000` and `29/100 < capSwitch < 2/5`, and the
angle bounds they give: a cap of depth at least `coreRadius` that holds a
square forces `t < 2/5`, and one of depth at least `1/2` forces `t < 1/4`.
Both follow from the monotonicity of `cos t + sin t` on `[0, π/4]` and Taylor
bounds at `2/5` and `1/4`. The file also proves `cos t ≤ 1 - t²/5` for
`|t| ≤ π`.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

lemma R0_gt_three_halves : (3 : ℝ) / 2 < R0 := by
  have h : Real.sqrt ((3 / 2 : ℝ) ^ 2) < Real.sqrt Q0 :=
    Real.sqrt_lt_sqrt (by positivity) (by norm_num [Q0])
  rw [Real.sqrt_sq (by norm_num)] at h
  exact h

lemma R0_lt_1689_1000 : R0 < (1689 : ℝ) / 1000 := by
  have h : Real.sqrt Q0 < Real.sqrt ((1689 / 1000 : ℝ) ^ 2) :=
    Real.sqrt_lt_sqrt Q0_pos.le (by norm_num [Q0])
  rw [Real.sqrt_sq (by norm_num)] at h
  exact h

lemma capSwitch_gt_29_100 : (29 : ℝ) / 100 < capSwitch := by
  have hden : 0 < 2 * R0 := by linarith [R0_pos]
  have hi : (29 : ℝ) / 100 < 1 / (2 * R0) := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith [R0_lt_1689_1000]
  have hs := Real.sin_le capSwitch_nonneg
  rw [sin_capSwitch] at hs
  linarith

lemma capSwitch_lt_two_fifths : capSwitch < (2 : ℝ) / 5 := by
  have hden : 0 < 2 * R0 := by linarith [R0_pos]
  have hi : 1 / (2 * R0) < (1 : ℝ) / 3 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [R0_gt_three_halves]
  by_contra! ht
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ (2 : ℝ) / 5 by linarith [Real.pi_pos])
    (show capSwitch ≤ Real.pi / 2 from Real.arcsin_le_pi_div_two _) ht
  rw [sin_capSwitch] at hs
  have hl := Real.sin_ge_sub_cube (x := (2 : ℝ) / 5) (by norm_num)
  nlinarith

/-- A quadratic upper bound for `cos` on `[-π, π]`. -/
lemma cos_le_one_sub_fifth_sq {t : ℝ} (ht : |t| ≤ Real.pi) :
    Real.cos t ≤ 1 - t ^ 2 / 5 := by
  have hpi : Real.pi < (22 : ℝ) / 7 := by linarith [Real.pi_lt_d4]
  have hp := mul_pos (sub_pos.mpr hpi)
    (show 0 < (22 : ℝ) / 7 + Real.pi by linarith [Real.pi_pos])
  have hpi2 : Real.pi ^ 2 < 10 := by nlinarith
  have hcoeff : (1 : ℝ) / 5 ≤ 2 / Real.pi ^ 2 := by
    apply (le_div_iff₀ (pow_pos Real.pi_pos 2)).mpr
    linarith
  have hm := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg t)
  have hc := Real.cos_le_one_sub_mul_cos_sq ht
  nlinarith

/-- `cos x + sin x` increases on `[0, π/4]`. -/
lemma cos_add_sin_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ Real.pi / 4) :
    Real.cos x + Real.sin x ≤ Real.cos y + Real.sin y := by
  have h := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ x + Real.pi / 4 by linarith [Real.pi_pos])
    (show y + Real.pi / 4 ≤ Real.pi / 2 by linarith)
    (show x + Real.pi / 4 ≤ y + Real.pi / 4 by linarith)
  simp only [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four] at h
  apply (mul_le_mul_iff_right₀ (show 0 < Real.sqrt 2 / 2 by positivity)).mp
  nlinarith only [h]

lemma capSecond_two_fifths_lt_core : capSecond (2 / 5) < coreRadius := by
  have hs := Real.sin_ge_sub_cube (x := (2 : ℝ) / 5) (by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (2 : ℝ) / 5)
  dsimp [capSecond, coreRadius]
  nlinarith [rho0_upper, R0_lt_1689_1000]

lemma capDepth_lt_core_of_two_fifths_le {t : ℝ}
    (ht : 2 / 5 ≤ t) (htpi : t ≤ Real.pi / 4) : capDepth t < coreRadius := by
  have hbranch : ¬ t ≤ capSwitch := by linarith [capSwitch_lt_two_fifths]
  rw [capDepth, ite_eq_right hbranch]
  have hm := cos_add_sin_mono (x := (2 : ℝ) / 5) (by norm_num) ht htpi
  have he := capSecond_two_fifths_lt_core
  dsimp [capSecond] at *
  linarith

/-- A cap of depth at least `coreRadius` that holds a square forces
`t < 2/5`. -/
theorem cap_angle_lt_two_fifths {height t : ℝ}
    (hh : coreRadius ≤ height) (hcap : height ≤ capDepth t)
    (htpi : t ≤ Real.pi / 4) : t < 2 / 5 := by
  by_contra! ht
  linarith [capDepth_lt_core_of_two_fifths_le ht htpi]

lemma capFirst_lt_half_of_quarter_le {t : ℝ}
    (ht : 1 / 4 ≤ t) (htpi : t ≤ Real.pi / 4) : capFirst t < 1 / 2 := by
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ (1 : ℝ) / 4 by linarith [Real.pi_pos])
    (show t ≤ Real.pi / 2 by linarith [Real.pi_pos]) ht
  have hpoly := Real.sin_ge_sub_cube (x := (1 : ℝ) / 4) (by norm_num)
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one t)
    (show 0 ≤ rho0 - 1 / 2 by linarith [rho0_lower])
  dsimp [capFirst]
  nlinarith [rho0_upper]

lemma capSecond_lt_half_of_quarter_le {t : ℝ}
    (ht : 1 / 4 ≤ t) (htpi : t ≤ Real.pi / 4) : capSecond t < 1 / 2 := by
  have hm := cos_add_sin_mono (x := (1 : ℝ) / 4) (by norm_num) ht htpi
  have hs := Real.sin_ge_sub_cube (x := (1 : ℝ) / 4) (by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1 : ℝ) / 4)
  dsimp [capSecond]
  nlinarith [R0_lt_1689_1000]

/-- A cap of depth at least `1/2` that holds a square forces `t < 1/4`. -/
theorem cap_angle_lt_quarter {height t : ℝ}
    (hh : 1 / 2 ≤ height) (hcap : height ≤ capDepth t)
    (htpi : t ≤ Real.pi / 4) : t < 1 / 4 := by
  by_contra! ht
  unfold capDepth at hcap
  split_ifs at hcap
  · linarith [capFirst_lt_half_of_quarter_le ht htpi]
  · linarith [capSecond_lt_half_of_quarter_le ht htpi]

end SquaresInCircles.Six.Normalization
