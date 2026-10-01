import SquaresInCircles.Six.Analytic.MarkerSupport
import SquaresInCircles.Six.Analytic.EndpointReduction

/-!
# Marker bounds for the south quadrant

Let `(a, u)` be a contained chart and `0 ≤ t ≤ π/4`. If `a ≥ 1/2 + sin t`, the
far corner gives `sin t + u < 89/100`, by Cauchy–Schwarz on
`(1 + sin t, u + 1/2)`, and the side term of the label then gives
`t + label a u < π/2 - 27/50`. The same holds in the cap
`(u + 1/2) sin t ≤ (a - 1/2) cos t`: for `t ≤ 6/25` by `label a u ≤ π/4`, and
above by the axial term, since a quartic, positive on `[6/25, 4/5]` by its
chord, gives `t + 5u/4 < 103/100`. In the cap
`(u + 1/2) cos t ≤ (a - 1/2) sin t` instead `t - label a u > 27/50`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma octant_cos_lower {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/4) :
    7/10 ≤ Real.cos t := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi ht0
    (show Real.pi/4 ≤ Real.pi by linarith [Real.pi_pos]) ht1
  rw [Real.cos_pi_div_four] at hc
  have hroot : (7:ℝ)/10 ≤ Real.sqrt 2/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  exact hroot.trans hc

/-- If `a ≥ 1/2 + sin t`, then `t + label a u < π/2 - 27/50`. -/
theorem own_south_marker {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/4) (ha : 1/2+Real.sin t ≤ a) :
    t+Seven.label a u < Real.pi/2-27/50 := by
  have hs0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0
    (by linarith [ht1,Real.pi_pos])
  have ht : t < 2/3 := by
    by_contra! hlarge
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2) ≤ (2:ℝ)/3 by linarith [Real.pi_pos])
      (show t ≤ Real.pi/2 by linarith [Real.pi_pos]) hlarge
    have hl := Real.sin_ge_sub_cube (x := (2:ℝ)/3) (by norm_num)
    nlinarith [h.a_le_rho0,rho0_upper]
  have ht2 := pow_le_pow_left₀ ht0 ht.le 2
  have ht3 := mul_le_mul_of_nonneg_right ht2 ht0
  have hsin : (25/27)*t ≤ Real.sin t := by
    nlinarith [Real.sin_ge_sub_cube ht0]
  have hcompare := mul_nonneg
    (show 0 ≤ a+1/2-(1+Real.sin t) by linarith)
    (show 0 ≤ a+1/2+(1+Real.sin t) by linarith [h.half_le])
  have hcorner : (1+Real.sin t)^2+(u+1/2)^2 ≤ Q0 := by
    nlinarith [h.containment]
  have hsum : Real.sin t+u < 89/100 := by
    by_contra! hf
    have hsq := sq_nonneg ((1+Real.sin t)-(u+1/2))
    have hp := mul_nonneg
      (show 0 ≤ Real.sin t+u+3/2-239/100 by linarith)
      (show 0 ≤ Real.sin t+u+3/2+239/100 by linarith [h.u_nonneg])
    norm_num [Q0] at hcorner
    nlinarith
  have hlabel := genuine_label_le_side a u
  linarith [Real.pi_gt_d2]

private def capQuartic (t : ℝ) : ℝ :=
  (1+(331/250-(4/5)*t)*t)^2+(331/250-(4/5)*t)^2-Q0

lemma south_cap_quartic {t : ℝ} (ht : 6/25 ≤ t ∧ t ≤ 4/5) : 0 < capQuartic t := by
  have he (x : ℝ) : capQuartic x =
      quartic (172061/62500-Q0) (331/625) (49561/62500) (-1324/625) (16/25) x := by
    dsimp [capQuartic,quartic]
    ring
  rw [he]
  apply quartic_positive_of_chord (l := (6:ℝ)/25) (u := (4:ℝ)/5) (by norm_num) ht
  · norm_num [quartic,Q0]
  · norm_num [quartic,Q0]
  · have ht2 := pow_le_pow_left₀ (by linarith : 0 ≤ t) ht.2 2
    nlinarith [ht.1]

/-- In the cap `(u + 1/2) sin t ≤ (a - 1/2) cos t`,
`t + label a u < π/2 - 27/50`. -/
theorem cap_south_marker {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/4)
    (hcap : (u+1/2)*Real.sin t ≤ (a-1/2)*Real.cos t) :
    t+Seven.label a u < Real.pi/2-27/50 := by
  by_cases hsmall : t ≤ 6/25
  · have hl := h.seven_admissible.label_le_quarter
    linarith [Real.pi_gt_d2]
  · have htlo : 6/25 ≤ t := (lt_of_not_ge hsmall).le
    have hthi : t ≤ 4/5 := by linarith [Real.pi_lt_d2]
    have hcos : 0 < Real.cos t := by linarith [octant_cos_lower ht0 ht1]
    have hpoly := cos_le_one_sub_fifth_sq (t := t) (by
      rw [abs_of_nonneg ht0]
      linarith [ht1,Real.pi_pos])
    have hmul := mul_le_mul_of_nonneg_left hpoly ht0
    have hsc : t*Real.cos t ≤ Real.sin t := by
      nlinarith [Real.sin_ge_sub_cube ht0,pow_nonneg ht0 3]
    have hVs := mul_le_mul_of_nonneg_left hsc
      (show 0 ≤ u+1/2 by linarith [h.u_nonneg])
    have ha : 1+(u+1/2)*t ≤ a+1/2 := by
      by_contra! hf
      have hp := mul_pos (show 0 < (u+1/2)*t-(a-1/2) by linarith) hcos
      nlinarith only [hVs,hcap,hp]
    have haxial : t+(5/4)*u < 103/100 := by
      by_contra! hf
      let V : ℝ := 331/250-(4/5)*t
      have hV0 : 0 ≤ V := by dsimp [V]; linarith
      have hVu : V ≤ u+1/2 := by dsimp [V]; linarith
      have hVt := mul_le_mul_of_nonneg_right hVu ht0
      have hAa : 1+V*t ≤ a+1/2 := by linarith
      have hAt0 : 0 ≤ 1+V*t := by positivity
      have hsqA := mul_nonneg (sub_nonneg.mpr hAa)
        (show 0 ≤ a+1/2+(1+V*t) by linarith)
      have hsqV := mul_nonneg (sub_nonneg.mpr hVu)
        (show 0 ≤ u+1/2+V by linarith [h.u_nonneg])
      have hpos := south_cap_quartic ⟨htlo,hthi⟩
      change 0 < (1+V*t)^2+V^2-Q0 at hpos
      nlinarith [h.containment]
    have hl := h.seven_admissible.label_le_axial
    dsimp [Seven.axial] at hl
    linarith [Real.pi_gt_d2]

/-- In the cap `(u + 1/2) cos t ≤ (a - 1/2) sin t`, `t - label a u > 27/50`:
`cos t ≥ 7/10` and `sin t ≤ t` bound `u` linearly. -/
theorem positive_offset_cap_marker {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/4)
    (hcap : (u+1/2)*Real.cos t ≤ (a-1/2)*Real.sin t) :
    27/50 < t-Seven.label a u := by
  have hc := octant_cos_lower ht0 ht1
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi ht0
    (show t ≤ Real.pi by linarith [ht1,Real.pi_pos])
  have hcu := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ u+1/2 by linarith [h.u_nonneg])
  have ha := mul_le_mul_of_nonneg_right
    (show a-1/2 ≤ 613/1000 by linarith [h.a_le_rho0,rho0_upper]) hs0
  have hs := Real.sin_le ht0
  have hl := h.seven_admissible.label_le_axial
  dsimp [Seven.axial] at hl
  have ht : t ≤ 4/5 := by linarith [ht1,Real.pi_lt_d2]
  nlinarith

end SquaresInCircles.Six.Analytic
