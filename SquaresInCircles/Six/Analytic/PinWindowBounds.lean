module
public import SquaresInCircles.Six.Analytic.PinSectorCover

@[expose] public section

/-!
# Pin-specific OWN window endpoints

The W upper endpoint follows by comparing a single radial lower bound and a
single transverse lower bound with the far-corner radius. The D OWN endpoint
uses its normal coordinate and the negative-tilt radial profile. Both proofs
are whole-interval analytic arguments; no rectangle cover is used.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization Normalization.Certificates

lemma west_positive_width {t : ℝ} (ht : 5/8 ≤ t ∧ t ≤ Real.pi/4) :
    349/250 ≤ Real.cos t+Real.sin t := by
  have hm := cos_add_sin_mono (x := (5:ℝ)/8) (by norm_num) ht.1 ht.2
  have hc := Seven.cos_lower_six (x := (5:ℝ)/8) (by norm_num)
  have hs := Seven.sin_lower_seven (x := (5:ℝ)/8) (by norm_num)
  norm_num at hc hs
  linarith

lemma west_pin_sine {t : ℝ} (ht : 5/8 ≤ t ∧ t ≤ Real.pi/4) :
    697/1000 ≤ (9/10)*Real.sin (Real.pi/12+t) := by
  have hlo : (133:ℝ)/150 ≤ Real.pi/12+t := by linarith [twelfth_bounds.1]
  have hhi : Real.pi/12+t ≤ Real.pi/2 := by linarith [ht.2,Real.pi_pos]
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (133:ℝ)/150 by linarith [Real.pi_pos]) hhi hlo
  have hs := Seven.sin_lower_seven (x := (133:ℝ)/150) (by norm_num)
  norm_num at hs
  linarith

lemma west_own_upper_window {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hbox : CoreBox x y)
    (hm : 0 ≤ centralMargin .own (Real.pi+t) a b x y)
    (hpin : openSquare (orientedSquare (Real.pi+t) a b) (fixedPin 2)) : t < 5/8 := by
  by_contra! hlarge
  have ht0 : 0 ≤ t := by linarith
  have ht1 := (abs_le.mp ht).2
  have hc0 : 0 ≤ Real.cos t := by linarith [(octant_trig ht).1.1]
  have hs0 := sin_nonneg_octant ht0 ht1
  have hxc := mul_le_mul_of_nonneg_right
    (show coreRadius ≤ 1/2-x by linarith [hbox.1.2,c0_add_coreRadius]) hc0
  have hys := mul_le_mul_of_nonneg_right
    (show coreRadius ≤ 1/2-y by linarith [hbox.2.2,c0_add_coreRadius]) hs0
  have hw := west_positive_width ⟨hlarge,ht1⟩
  have hprod := mul_le_mul coreRadius_gt_387_1000.le hw
    (by norm_num : (0:ℝ) ≤ 349/250) coreRadius_pos.le
  have hrad : 77/50 ≤ a+1/2 := by
    dsimp [centralMargin,centralNormal,angularWidth] at hm
    simp only [Real.cos_pi_add,Real.sin_pi_add,abs_neg] at hm
    rw [abs_of_nonneg hc0,abs_of_nonneg hs0] at hm
    nlinarith
  have hY := hpin.2
  rw [fixedPin_eq_polar,pinDirection,pin_localY] at hY
  have hangle : 11*Real.pi/12-(Real.pi+t)=-(Real.pi/12+t) := by ring
  rw [hangle,Real.sin_neg] at hY
  have hYlo := (abs_lt.mp hY).1
  have hsin := west_pin_sine ⟨hlarge,ht1⟩
  have hb : 697/1000 ≤ |b|+1/2 := by nlinarith [neg_le_abs b]
  have hA := mul_nonneg (sub_nonneg.mpr hrad)
    (show 0 ≤ a+1/2+77/50 by linarith [h.half_le])
  have hB := mul_nonneg (sub_nonneg.mpr hb)
    (show 0 ≤ |b|+1/2+697/1000 by positivity)
  have hcontain := h.containment
  norm_num [Q0] at hcontain
  nlinarith

/-- D on a west OWN axis cannot point 1/4 radian below west. -/
lemma diagonal_west_own_lower {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hbox : CoreBox x y)
    (hm : 0 ≤ centralMargin .own (Real.pi+t) a b x y)
    (hpin : openSquare (orientedSquare (Real.pi+t) a b) (fixedPin 3)) : -1/4 < t := by
  by_contra! htlo
  let z := -t
  have hz : 1/4 ≤ z ∧ z ≤ Real.pi/4 := by
    dsimp [z]
    exact ⟨by linarith,(by have hh := abs_le.mp ht; linarith [hh.1])⟩
  have hs0 := sin_nonneg_octant (by linarith [hz.1]) hz.2
  have hc0 : 0 ≤ Real.cos z := by linarith [octant_cos_lower (by linarith [hz.1]) hz.2]
  have hprofile := west_own_negative_profile h ht (by linarith) hbox.1.2 hbox.2.1 hm
  have hX := (abs_lt.mp hpin.1).1
  rw [fixedPin_eq_polar,pinDirection,pin_localX] at hX
  have hangle : 5*Real.pi/4-(Real.pi+t)=Real.pi/4+z := by dsimp [z]; ring
  rw [hangle,Real.cos_add,Real.cos_pi_div_four,Real.sin_pi_div_four] at hX
  have hrlo : (7:ℝ)/10 ≤ Real.sqrt 2/2 := diagonal_trig_lower
  have hrhi : Real.sqrt 2/2 ≤ (71:ℝ)/100 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hsmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (1:ℝ)/4 by linarith [Real.pi_pos])
    (show z ≤ Real.pi/2 by linarith [hz.2,Real.pi_pos]) hz.1
  have hslow := Real.sin_ge_sub_cube (x := (1:ℝ)/4) (by norm_num)
  have hA := mul_le_mul_of_nonneg_right hrhi hc0
  have hB := mul_le_mul_of_nonneg_right hrlo hs0
  have hK := mul_le_mul_of_nonneg_right coreRadius_gt_387_1000.le hc0
  change 1/2+coreRadius*Real.cos z+(1/2)*Real.sin z ≤ a at hprofile
  norm_num at hslow
  nlinarith [Real.cos_le_one z]

end SquaresInCircles.Six.Analytic
