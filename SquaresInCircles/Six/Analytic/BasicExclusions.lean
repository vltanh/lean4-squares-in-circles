import SquaresInCircles.Six.Analytic.QuadrantGeometry

/-!
# Elementary separator exclusions before the strong central box

The excluded secondary directions would require |b| >= 17/20, contradicting
containment's |b| < 7/10. The remaining outward secondary direction has a
large genuine marker displacement, handled on all three label branches.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma inward_secondary_negative {b t x y : ℝ}
    (hb : |b| < 7/10) (ht : |t| ≤ Real.pi/4)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    b-1/2-x*Real.cos t-y*Real.sin t-angularWidth t < 0 := by
  have hc := octant_trig ht
  have hxc := mul_nonneg hx0 (show 0 ≤ Real.cos t by linarith [hc.1.1])
  have hys := (signed_sine_product (t := t) hy0 hy1).2
  have hb' := (le_abs_self b).trans_lt hb
  dsimp [angularWidth]
  rw [abs_of_nonneg (show 0 ≤ Real.cos t by linarith [hc.1.1])]
  nlinarith only [hxc,hys,hb',hc.1.1]

lemma east_secPlus_negative {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) (hy0 : 0 ≤ y) :
    centralMargin .secPlus t a b x y < 0 := by
  have hc := octant_trig ht
  have hyc := mul_nonneg hy0 (show 0 ≤ Real.cos t by linarith [hc.1.1])
  have hxs := (signed_sine_product (t := t) hx0 hx1).1
  have hb := (le_abs_self b).trans_lt h.u_lt_seven_tenths
  dsimp [centralMargin,centralTransverse,angularWidth]
  rw [abs_of_nonneg (show 0 ≤ Real.cos t by linarith [hc.1.1])]
  nlinarith only [hyc,hxs,hb,hc.1.1]

lemma east_secMinus_small_negative {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2)
    (hy : y ≤ 23/200) : centralMargin .secMinus t a b x y < 0 := by
  have hc := octant_trig ht
  have hyc := mul_le_mul_of_nonneg_right hy
    (show 0 ≤ Real.cos t by linarith [hc.1.1])
  have hxs := (signed_sine_product (t := t) hx0 hx1).2
  have hb := (neg_le_abs b).trans_lt h.u_lt_seven_tenths
  dsimp [centralMargin,centralTransverse,angularWidth]
  rw [abs_of_nonneg (show 0 ≤ Real.cos t by linarith [hc.1.1])]
  nlinarith only [hyc,hxs,hb,hc.1.1]

lemma north_secMinus_negative {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    centralMargin .secMinus (Real.pi/2+t) a b x y < 0 := by
  rw [north_secMinus]
  have hm := inward_secondary_negative (b := -b)
    (by simpa only [abs_neg] using h.u_lt_seven_tenths) ht hx0 hy0 hy1
  linarith

lemma south_secPlus_negative {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    centralMargin .secPlus (-Real.pi/2+t) a b x y < 0 := by
  rw [south_secPlus]
  exact inward_secondary_negative h.u_lt_seven_tenths ht hx0 hy0 hy1

lemma north_south_negative {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hy : y ≤ 1/2) :
    centralMargin .south (Real.pi/2+t) a b x y < 0 := by
  have hp := primary_projection_nonneg h ht
  have hc := octant_trig ht
  rw [north_south]
  dsimp [angularWidth]
  rw [abs_of_nonneg (show 0 ≤ Real.cos t by linarith [hc.1.1])]
  nlinarith only [hp,hy,hc.2.2]

lemma south_north_negative {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hy : 0 ≤ y) :
    centralMargin .north (-Real.pi/2+t) a b x y < 0 := by
  have hp := primary_projection_nonneg h ht
  have hc := octant_trig ht
  rw [south_north]
  dsimp [angularWidth]
  rw [abs_of_nonneg (show 0 ≤ Real.cos t by linarith [hc.1.1])]
  nlinarith only [hp,hy,hc.2.2]

lemma outward_secondary_offset {b t x y : ℝ}
    (ht : |t| ≤ Real.pi/4) (hx1 : x ≤ 1/2) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2)
    (hm : 0 ≤ b-1/2+x*Real.cos t+y*Real.sin t-angularWidth t) :
    1/2 ≤ b ∧ (t ≤ 0 → 1/2+|Real.sin t|/2 ≤ b) := by
  have hc := octant_trig ht
  have hxc := mul_le_mul_of_nonneg_right hx1
    (show 0 ≤ Real.cos t by linarith [hc.1.1])
  have hys := (signed_sine_product (t := t) hy0 hy1).1
  dsimp [angularWidth] at hm
  rw [abs_of_nonneg (show 0 ≤ Real.cos t by linarith [hc.1.1])] at hm
  refine ⟨by linarith,?_⟩
  intro ht0
  have hs0 : Real.sin t ≤ 0 := by
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ -t by linarith)
      (by have hh := abs_le.mp ht; linarith [hh.1,Real.pi_pos])
    rw [Real.sin_neg] at hs
    linarith
  have hneg := mul_nonpos_of_nonneg_of_nonpos hy0 hs0
  linarith

lemma outward_secondary_marker {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx1 : x ≤ 1/2) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2)
    (hm : 0 ≤ b-1/2+x*Real.cos t+y*Real.sin t-angularWidth t) :
    0 < t+signedLabel a b := by
  have hb := outward_secondary_offset ht hx1 hy0 hy1 hm
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have hlarge := h.large_offset_label (by simpa only [abs_of_nonneg hb0] using hb.1)
  rw [signedLabel_of_nonneg hb0]
  by_cases ht0 : 0 ≤ t
  · linarith
  · have hsmall : -t < 1/2 := by
      have hoff := hb.2 (le_of_not_ge ht0)
      have hu := h.u_lt_seven_tenths
      rw [abs_of_nonneg hb0] at hu
      by_contra! htbad
      have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
        (show -(Real.pi/2) ≤ (1:ℝ)/2 by linarith [Real.pi_pos])
        (show -t ≤ Real.pi/2 by have ht' := abs_le.mp ht; linarith [ht'.1,Real.pi_pos]) htbad
      have hl := Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)
      rw [Real.sin_neg] at hmono
      have ha := neg_le_abs (Real.sin t)
      linarith
    linarith

end SquaresInCircles.Six.Analytic
