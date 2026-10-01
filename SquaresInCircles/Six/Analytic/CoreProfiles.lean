import SquaresInCircles.Six.Analytic.MarkerSupport

/-!
# Marker budgets for the squares above and below C

A contained square with `0 ≤ t ≤ 4/5` has `t + (5/4) u < 3/8` when
`a ≥ 1 + t/3`, and `t + (5/4) u < 2/3` when `a ≥ 177/200 + (3/8) t`: otherwise
its far corner would leave the disk, by a completed square. For a square above
or below C, at the angle `t` from the vertical, these bound how far its
marker turns, since the label is at most `(5/4) u`; the two budgets add up to
`25/24 < π/3`. The lower bounds on `a` come from the separation of the square
from C, along its own axis or along a side of C, through one Taylor bound
affine in `t` or through `sin t ≥ (9/10) t`; a square turned the other way
bounds `(5/4) u - t` in the same way.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma trig_affine_lower {A B r t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ r) :
    A+(B-A*r/2-B*r^2/6)*t ≤ A*Real.cos t+B*Real.sin t := by
  have hq := mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have ht2 := pow_le_pow_left₀ ht0 ht1 2
  have ht3 := mul_le_mul_of_nonneg_right ht2 ht0
  have hc := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := t)) hA
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube ht0) hB
  have hAq := mul_nonneg hA hq
  have hBq := mul_le_mul_of_nonneg_left ht3 hB
  nlinarith only [hc,hs,hAq,hBq]

private lemma north_quadratic (t : ℝ) :
    Q0 < (3/2+t/3)^2+(4/5-(4/5)*t)^2 := by
  have hsq := sq_nonneg (t-63/338)
  norm_num [Q0]
  nlinarith only [hsq]

private lemma south_quadratic (t : ℝ) :
    Q0 < (277/200+(3/8)*t)^2+(31/30-(4/5)*t)^2 := by
  have hsq := sq_nonneg (t-1475/3747)
  norm_num [Q0]
  nlinarith only [hsq]

lemma north_marker_budget {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 4/5) (ha : 1+t/3 ≤ a) :
    t+(5/4)*u < 3/8 := by
  by_contra! hf
  have hv : 4/5-(4/5)*t ≤ u+1/2 := by linarith
  have hv0 : 0 ≤ 4/5-(4/5)*t := by linarith
  have hA0 : 0 ≤ 3/2+t/3 := by linarith
  have hAsq := mul_nonneg
    (show 0 ≤ a+1/2-(3/2+t/3) by linarith)
    (show 0 ≤ a+1/2+(3/2+t/3) by linarith [h.half_le])
  have hVsq := mul_nonneg (sub_nonneg.mpr hv)
    (show 0 ≤ u+1/2+(4/5-(4/5)*t) by linarith [h.u_nonneg])
  nlinarith [h.containment,north_quadratic t]

lemma south_marker_budget {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 4/5) (ha : 177/200+(3/8)*t ≤ a) :
    t+(5/4)*u < 2/3 := by
  by_contra! hf
  have hv : 31/30-(4/5)*t ≤ u+1/2 := by linarith
  have hv0 : 0 ≤ 31/30-(4/5)*t := by linarith
  have hA0 : 0 ≤ 277/200+(3/8)*t := by linarith
  have hAsq := mul_nonneg
    (show 0 ≤ a+1/2-(277/200+(3/8)*t) by linarith)
    (show 0 ≤ a+1/2+(277/200+(3/8)*t) by linarith [h.half_le])
  have hVsq := mul_nonneg (sub_nonneg.mpr hv)
    (show 0 ≤ u+1/2+(31/30-(4/5)*t) by linarith [h.u_nonneg])
  nlinarith [h.containment,south_quadratic t]

/-- The budget `3/8` from `a ≥ 1/2 + (1/2) cos t + (61/100) sin t`, the bound
of a separation along the own axis of a square above C turned towards E. -/
lemma north_own_towards {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/4)
    (ha : 1/2+(1/2)*Real.cos t+(61/100)*Real.sin t ≤ a) :
    t+(5/4)*u < 3/8 := by
  have ht : t ≤ 4/5 := by linarith [Real.pi_lt_d2]
  have hb := trig_affine_lower (A := (1:ℝ)/2) (B := (61:ℝ)/100)
    (by norm_num) (by norm_num) ht0 ht
  apply north_marker_budget h ht0 ht
  linarith

/-- The budget `3/8` for `(5/4) u - t` from `a ≥ 1/2 + (1/2) cos t`, for a
square above C turned away from E. -/
lemma north_own_away {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/4)
    (ha : 1/2+(1/2)*Real.cos t ≤ a) :
    (5/4)*u-t < 3/8 := by
  have ht : t ≤ 4/5 := by linarith [Real.pi_lt_d2]
  have h2 := pow_le_pow_left₀ ht0 ht 2
  have hq := mul_nonneg ht0 (show 0 ≤ 4/5-t by linarith)
  have hrad : 3/2-t^2/4 ≤ a+1/2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have hr0 : 0 ≤ 3/2-t^2/4 := by nlinarith
  by_contra! hf
  have hv : 4/5+(4/5)*t ≤ u+1/2 := by linarith
  have hsA := mul_nonneg (sub_nonneg.mpr hrad)
    (show 0 ≤ a+1/2+(3/2-t^2/4) by linarith [h.half_le])
  have hsV := mul_nonneg (sub_nonneg.mpr hv)
    (show 0 ≤ u+1/2+(4/5+(4/5)*t) by linarith [h.u_nonneg])
  have hpoly : Q0 < (3/2-t^2/4)^2+(4/5+(4/5)*t)^2 := by
    have h4 := pow_nonneg ht0 4
    norm_num [Q0]
    nlinarith only [hq,ht0,h4]
  nlinarith [h.containment]

/-- The budget `3/8` from `a ≥ 1 + (u + 1/2) sin t`, for `0 ≤ t ≤ 1/4`. -/
lemma north_cap_towards {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1/4)
    (ha : 1+(u+1/2)*Real.sin t ≤ a) :
    t+(5/4)*u < 3/8 := by
  have hs := sine_nine_tenths ht0 (by linarith)
  have hp := mul_le_mul
    (show (1:ℝ)/2 ≤ u+1/2 by linarith [h.u_nonneg]) hs
    (show 0 ≤ (9/10)*t by positivity)
    (show 0 ≤ u+1/2 by linarith [h.u_nonneg])
  apply north_marker_budget h ht0 (by linarith)
  nlinarith

/-- The budget `2/3` from `a ≥ 1/2 + (77/200) cos t + (61/100) sin t`, the
bound of a separation along the own axis of a square below C turned towards
E. -/
lemma south_own_towards {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/4)
    (ha : 1/2+(77/200)*Real.cos t+(61/100)*Real.sin t ≤ a) :
    t+(5/4)*u < 2/3 := by
  have ht : t ≤ 4/5 := by linarith [Real.pi_lt_d2]
  have hb := trig_affine_lower (A := (77:ℝ)/200) (B := (61:ℝ)/100)
    (by norm_num) (by norm_num) ht0 ht
  apply south_marker_budget h ht0 ht
  linarith

/-- The budget `2/3` from `a ≥ 2 - rho0 + (u + 1/2) sin t`, for
`0 ≤ t ≤ 2/5`. -/
lemma south_cap_towards {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 2/5)
    (ha : 2-rho0+(u+1/2)*Real.sin t ≤ a) :
    t+(5/4)*u < 2/3 := by
  have hs := sine_nine_tenths ht0 (by linarith)
  have hp := mul_le_mul
    (show (1:ℝ)/2 ≤ u+1/2 by linarith [h.u_nonneg]) hs
    (show 0 ≤ (9/10)*t by positivity)
    (show 0 ≤ u+1/2 by linarith [h.u_nonneg])
  apply south_marker_budget h ht0 (by linarith)
  nlinarith [rho0_upper]

/-- The budget `2/3` for `(5/4) u - t` from `a ≥ 1/2 + (77/200) cos t`, for a
square below C turned away from E. -/
lemma south_own_away {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/4)
    (ha : 1/2+(77/200)*Real.cos t ≤ a) :
    (5/4)*u-t < 2/3 := by
  have ht : t ≤ 4/5 := by linarith [Real.pi_lt_d2]
  have h2 := pow_le_pow_left₀ ht0 ht 2
  have hrad : 277/200-(77/400)*t^2 ≤ a+1/2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have hr0 : 0 ≤ 277/200-(77/400)*t^2 := by nlinarith
  by_contra! hf
  have hv : 31/30+(4/5)*t ≤ u+1/2 := by linarith
  have hsA := mul_nonneg (sub_nonneg.mpr hrad)
    (show 0 ≤ a+1/2+(277/200-(77/400)*t^2) by linarith [h.half_le])
  have hsV := mul_nonneg (sub_nonneg.mpr hv)
    (show 0 ≤ u+1/2+(31/30+(4/5)*t) by linarith [h.u_nonneg])
  have hpoly : Q0 < (277/200-(77/400)*t^2)^2+(31/30+(4/5)*t)^2 := by
    have h4 := pow_nonneg ht0 4
    have hsq := sq_nonneg t
    norm_num [Q0]
    nlinarith only [ht0,h4,hsq]
  nlinarith [h.containment]

end SquaresInCircles.Six.Analytic
