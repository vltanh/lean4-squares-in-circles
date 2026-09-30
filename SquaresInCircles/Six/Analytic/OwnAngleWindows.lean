module
public import SquaresInCircles.Six.Analytic.ForbiddenArcs
public import SquaresInCircles.Six.Analytic.OwnMovingPin
public import SquaresInCircles.Seven.Analysis

@[expose] public section

/-!
# OWN angle windows from whole-octant concavity

Three endpoint arguments give E's interval (-5/12,3/10) and W's lower
endpoint -2/3. The upper cosine/sine coefficients are never sampled on a grid.
At the rational endpoints only the proved Taylor inequalities are evaluated;
at pi/4 the exact trigonometric values suffice.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma coreRadius_gt_387_1000 : 387/1000 < coreRadius := by
  dsimp [coreRadius]
  linarith [rho0_upper]

lemma diagonal_trig_lower : (7:ℝ)/10 ≤ Real.sqrt 2/2 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]

lemma east_positive_profile_gt {t : ℝ} (ht : 3/10 ≤ t ∧ t ≤ Real.pi/4) :
    rho0 < 1/2+(1/2)*Real.cos t+(1/2)*Real.sin t := by
  have hleft : (613:ℝ)/1000 <
      (1/2)*Real.cos (3/10)+(1/2)*Real.sin (3/10) := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := (3:ℝ)/10)
    have hs := Real.sin_ge_sub_cube (x := (3:ℝ)/10) (by norm_num)
    norm_num at hc hs
    linarith
  have hright : (613:ℝ)/1000 <
      (1/2)*Real.cos (Real.pi/4)+(1/2)*Real.sin (Real.pi/4) := by
    rw [Real.cos_pi_div_four,Real.sin_pi_div_four]
    linarith [diagonal_trig_lower]
  have hh := trig_lower_of_endpoints (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 3/10)
    (show Real.pi/4 ≤ Real.pi/2 by linarith [Real.pi_pos]) ht hleft hright
  linarith [rho0_upper]

lemma east_negative_profile_gt {t : ℝ} (ht : 5/12 ≤ t ∧ t ≤ Real.pi/4) :
    rho0 < 1/2+(1/2)*Real.cos t+(387/1000)*Real.sin t := by
  have hleft : (613:ℝ)/1000 <
      (1/2)*Real.cos (5/12)+(387/1000)*Real.sin (5/12) := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := (5:ℝ)/12)
    have hs := Real.sin_ge_sub_cube (x := (5:ℝ)/12) (by norm_num)
    norm_num at hc hs
    linarith
  have hright : (613:ℝ)/1000 <
      (1/2)*Real.cos (Real.pi/4)+(387/1000)*Real.sin (Real.pi/4) := by
    rw [Real.cos_pi_div_four,Real.sin_pi_div_four]
    linarith [diagonal_trig_lower]
  have hh := trig_lower_of_endpoints (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 387/1000) (by norm_num : (0:ℝ) ≤ 5/12)
    (show Real.pi/4 ≤ Real.pi/2 by linarith [Real.pi_pos]) ht hleft hright
  linarith [rho0_upper]

lemma west_negative_profile_gt {t : ℝ} (ht : 2/3 ≤ t ∧ t ≤ Real.pi/4) :
    rho0 < 1/2+(387/1000)*Real.cos t+(1/2)*Real.sin t := by
  have hleft : (613:ℝ)/1000 <
      (387/1000)*Real.cos (2/3)+(1/2)*Real.sin (2/3) := by
    have hc := Seven.cos_lower_six (x := (2:ℝ)/3) (by norm_num)
    have hs := Seven.sin_lower_seven (x := (2:ℝ)/3) (by norm_num)
    norm_num at hc hs
    linarith
  have hright : (613:ℝ)/1000 <
      (387/1000)*Real.cos (Real.pi/4)+(1/2)*Real.sin (Real.pi/4) := by
    rw [Real.cos_pi_div_four,Real.sin_pi_div_four]
    linarith [diagonal_trig_lower]
  have hh := trig_lower_of_endpoints (by norm_num : (0:ℝ) ≤ 387/1000)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 2/3)
    (show Real.pi/4 ≤ Real.pi/2 by linarith [Real.pi_pos]) ht hleft hright
  linarith [rho0_upper]

/-- E's OWN window precedes pin assignment. -/
theorem own_east_window {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ c0)
    (hm : 0 ≤ centralMargin .own t a b x y) : -5/12 < t ∧ t < 3/10 := by
  have htr := octant_trig ht
  have hc0 : 0 ≤ Real.cos t := by linarith [htr.1.1]
  have hxc := mul_nonneg hx0 hc0
  have ha := h.a_le_rho0
  constructor
  · by_contra! htlo
    have hv0 : 0 ≤ -t := by linarith
    have hv1 : -t ≤ Real.pi/4 := by have hh := abs_le.mp ht; linarith [hh.1]
    have hs0 := sin_nonpos_octant (by linarith) (abs_le.mp ht).1
    have hylo : 387/1000 ≤ 1/2-y := by
      have hid := c0_add_coreRadius
      linarith [coreRadius_gt_387_1000]
    have hymul := mul_le_mul_of_nonneg_right hylo (sin_nonneg_octant hv0 hv1)
    have hbad := east_negative_profile_gt ⟨by linarith,hv1⟩
    dsimp [centralMargin,centralNormal,angularWidth] at hm
    rw [abs_of_nonneg hc0,abs_of_nonpos hs0] at hm
    rw [Real.sin_neg] at hymul
    rw [Real.cos_neg,Real.sin_neg] at hbad
    nlinarith
  · by_contra! hthi
    have ht0 : 0 ≤ t := by linarith
    have hs0 := sin_nonneg_octant ht0 ((le_abs_self t).trans ht)
    have hymul := mul_nonneg hy0 hs0
    have hbad := east_positive_profile_gt ⟨hthi,(le_abs_self t).trans ht⟩
    dsimp [centralMargin,centralNormal,angularWidth] at hm
    rw [abs_of_nonneg hc0,abs_of_nonneg hs0] at hm
    nlinarith

/-- W's negative OWN tail is excluded before pin assignment. -/
theorem own_west_lower_window {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx : x ≤ c0) (hy0 : 0 ≤ y)
    (hm : 0 ≤ centralMargin .own (Real.pi+t) a b x y) : -2/3 < t := by
  by_contra! htlo
  have hv0 : 0 ≤ -t := by linarith
  have hv1 : -t ≤ Real.pi/4 := by have hh := abs_le.mp ht; linarith [hh.1]
  have hs0 := sin_nonpos_octant (by linarith) (abs_le.mp ht).1
  have hc0 : 0 ≤ Real.cos t := by linarith [(octant_trig ht).1.1]
  have hxlo : 387/1000 ≤ 1/2-x := by linarith [c0_add_coreRadius,coreRadius_gt_387_1000]
  have hxmul := mul_le_mul_of_nonneg_right hxlo hc0
  have hymul := mul_nonneg hy0 (sin_nonneg_octant hv0 hv1)
  have hbad := west_negative_profile_gt ⟨by linarith,hv1⟩
  dsimp [centralMargin,centralNormal,angularWidth] at hm
  simp only [Real.cos_pi_add,Real.sin_pi_add,abs_neg] at hm
  rw [abs_of_nonneg hc0,abs_of_nonpos hs0] at hm
  rw [Real.sin_neg] at hymul
  rw [Real.cos_neg,Real.sin_neg] at hbad
  nlinarith [h.a_le_rho0]

end SquaresInCircles.Six.Analytic
