import SquaresInCircles.Six.Normalization.Markers

/-!
# Lower bounds for the label

Cauchy–Schwarz with the normal `(1, 3/4)` at the far corner
`(a + 1/2, u + 1/2)` gives `a + (3/4) u < 5/4` for a contained chart, and so a
lower bound for the side term of the label; with the axial term `(5/4) u` and
the cap `π/4` this bounds the label below. For `0 ≤ t ≤ π/4`, an offset
`u ≥ 1/2 + sin t` gives a label above `t + 27/50`, and
`(1/2 - u) cos t ≤ (a - 1/2) sin t` gives `t + label a u > 27/50`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma chart_weighted_support {a u : ℝ} (h : ContainedChart a u) :
    a+(3/4)*u < 5/4 := by
  have hc := h.containment
  have hid : (a+1/2+(3/4)*(u+1/2))^2+
      ((3/4)*(a+1/2)-(u+1/2))^2 =
      (25/16)*((a+1/2)^2+(u+1/2)^2) := by ring
  have hsq : (a+1/2+(3/4)*(u+1/2))^2 ≤ (25/16)*Q0 := by
    nlinarith [sq_nonneg ((3/4)*(a+1/2)-(u+1/2))]
  by_contra! hf
  have hp := mul_nonneg
    (show 0 ≤ a+1/2+(3/4)*(u+1/2)-17/8 by linarith)
    (show 0 ≤ a+1/2+(3/4)*(u+1/2)+17/8 by linarith)
  norm_num [Q0] at hsq
  nlinarith

lemma genuine_label_le_side (a u : ℝ) :
    Seven.label a u ≤ Real.pi/6+(u-1/2)/3+(3/4)*(1-a) := by
  have h : Seven.label a u ≤ Seven.side a u := (min_le_left _ _).trans (min_le_right _ _)
  unfold Seven.side at h
  linarith

lemma genuine_side_lower {a u : ℝ} (h : ContainedChart a u) :
    Real.pi/6-17/48+(43/48)*u < Real.pi/6+(u-1/2)/3+(3/4)*(1-a) := by
  linarith [chart_weighted_support h]

lemma genuine_label_lower {a u L : ℝ} (h : ContainedChart a u)
    (hax : L < (5/4)*u)
    (hside : L ≤ Real.pi/6-17/48+(43/48)*u)
    (hquarter : L < Real.pi/4) : L < Seven.label a u := by
  unfold Seven.label Seven.axial Seven.side
  apply lt_min
  · exact lt_min (by linarith) (by linarith [genuine_side_lower h])
  · exact hquarter

lemma sine_nine_tenths {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) :
    (9/10)*t ≤ Real.sin t := by
  have h2 := pow_le_pow_left₀ ht0 ht1 2
  have h3 := mul_le_mul_of_nonneg_right h2 ht0
  nlinarith [Real.sin_ge_sub_cube ht0]

/-- For `0 ≤ t ≤ π/4`, an offset `u ≥ 1/2 + sin t` gives a label above
`t + 27/50`. -/
theorem marker_offset_ahead {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/4) (hu : 1/2+Real.sin t ≤ u) :
    t+27/50 < Seven.label a u := by
  have humax := h.u_lt_seven_tenths
  have ht : t < 11/50 := by
    by_contra! hlarge
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2) ≤ (11:ℝ)/50 by linarith [Real.pi_pos])
      (show t ≤ Real.pi/2 by linarith [Real.pi_pos]) hlarge
    have hl := Real.sin_ge_sub_cube (x := (11:ℝ)/50) (by norm_num)
    nlinarith
  have hs := sine_nine_tenths ht0 (by linarith)
  apply genuine_label_lower h
  · linarith
  · linarith [Real.pi_gt_d2]
  · linarith [Real.pi_gt_d2]

/-- For `0 ≤ t ≤ π/4`, the condition `(1/2 - u) cos t ≤ (a - 1/2) sin t` gives
`t + label a u > 27/50`. -/
theorem marker_offset_behind {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/4)
    (hcap : (1/2-u)*Real.cos t ≤ (a-1/2)*Real.sin t) :
    27/50 < t+Seven.label a u := by
  by_cases ht : 27/50 < t
  · linarith [h.seven_admissible.label_nonneg]
  · have ht' : t ≤ 27/50 := le_of_not_gt ht
    have hc : 5/6 ≤ Real.cos t := by
      have ht2 := pow_le_pow_left₀ ht0 ht' 2
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]
    have hcos0 : 0 ≤ Real.cos t := by linarith
    have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0
      (by linarith [ht1,Real.pi_pos])
    have hterm : a-1/2 ≤ 613/1000 := by linarith [h.a_le_rho0,rho0_upper]
    have hR := mul_le_mul_of_nonneg_right hterm hs
    have hsin := Real.sin_le ht0
    have huLower : 1/2-(1839/2500)*t ≤ u := by
      by_cases huHalf : u ≤ 1/2
      · have hlow := mul_le_mul_of_nonneg_left hc (show 0 ≤ 1/2-u by linarith)
        nlinarith only [hlow,hcap,hR,hsin]
      · linarith
    have hlabel : 27/50-t < Seven.label a u := by
      apply genuine_label_lower h
      · linarith
      · linarith [Real.pi_gt_d2]
      · linarith [Real.pi_gt_d2]
    linarith

end SquaresInCircles.Six.Analytic
