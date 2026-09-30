import SquaresInCircles.Six.Analytic.TwoPinCover

/-!
# The short fringe before the western fixed pin

Between the two southwest pins, TwoPinCover already handles every chart.
Only the fringe theta < -pi/12 remains. OWN is handled by one completed-square
inequality after rotating the radial profile by pi/12. A cardinal cap is
handled by one explicit increasing quadratic. No searched partition appears.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma twelfth_bounds : (261:ℝ)/1000 ≤ Real.pi/12 ∧ Real.pi/12 ≤ 131/500 := by
  constructor <;> linarith [Real.pi_gt_d2,Real.pi_lt_d4]

lemma twelfth_trig : 193/200 ≤ Real.cos (Real.pi/12) ∧
    129/500 ≤ Real.sin (Real.pi/12) ∧ Real.sin (Real.pi/12) ≤ 27/100 := by
  have hb := twelfth_bounds
  have hsq := mul_nonneg (show 0 ≤ 131/500-Real.pi/12 by linarith)
    (show 0 ≤ 131/500+Real.pi/12 by linarith [Real.pi_pos])
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi/12)
  have hsmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (261:ℝ)/1000 by linarith [Real.pi_pos])
    (show Real.pi/12 ≤ Real.pi/2 by linarith [Real.pi_pos]) hb.1
  have hslow := Real.sin_ge_sub_cube (x := (261:ℝ)/1000) (by norm_num)
  have hsup := Real.sin_le (show 0 ≤ Real.pi/12 by positivity)
  norm_num at hslow
  exact ⟨by nlinarith,by linarith,by linarith⟩

lemma rotated_west_profile :
    1/2 ≤ coreRadius*Real.cos (Real.pi/12)+(1/2)*Real.sin (Real.pi/12) ∧
      3/8 ≤ (1/2)*Real.cos (Real.pi/12)-coreRadius*Real.sin (Real.pi/12) := by
  have ht := twelfth_trig
  have hk : 387/1000 ≤ coreRadius := coreRadius_gt_387_1000.le
  have hk1 : coreRadius ≤ 39/100 := by dsimp [coreRadius]; linarith [rho0_lower]
  have hc0 : 0 ≤ Real.cos (Real.pi/12) := by linarith [ht.1]
  have hs0 : 0 ≤ Real.sin (Real.pi/12) := by linarith [ht.2.1]
  have hlow := mul_le_mul hk ht.1 (by norm_num : (0:ℝ) ≤ 193/200) coreRadius_pos.le
  have hupp := mul_le_mul hk1 ht.2.2 hs0 (by norm_num : (0:ℝ) ≤ 39/100)
  exact ⟨by nlinarith [ht.2.1],by nlinarith [ht.1]⟩

lemma west_fringe_quadratic (s : ℝ) :
    Q0 < (23/16+(3/8)*s)^2+(1-(9/10)*s)^2 := by
  have hid : (23/16+(3/8)*s)^2+(1-(9/10)*s)^2-Q0 =
      (1521/1600)*(s-385/1014)^2+330327/4225000 := by
    norm_num [Q0]
    ring
  have hs := sq_nonneg (s-385/1014)
  nlinarith

/-- In the OWN fringe the west pin's transverse upper inequality cannot fail. -/
lemma own_west_fringe_transverse {a b v : ℝ} (h : ContainedChart a |b|)
    (hv : Real.pi/12 ≤ v ∧ v ≤ 2/3)
    (ha : 1/2+coreRadius*Real.cos v+(1/2)*Real.sin v ≤ a) :
    (9/10)*Real.sin (v-Real.pi/12)-b < 1/2 := by
  let δ := v-Real.pi/12
  have hd : 0 ≤ δ ∧ δ ≤ 1/2 := by
    dsimp [δ]
    constructor <;> linarith [hv.1,hv.2,twelfth_bounds.1]
  have hdsq := mul_nonneg (show 0 ≤ 1/2-δ by linarith [hd.2])
    (show 0 ≤ 1/2+δ by linarith [hd.1])
  have hc : 7/8 ≤ Real.cos δ := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := δ)]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hd.1
    (show δ ≤ Real.pi by linarith [hd.2,Real.pi_gt_d2])
  have hs1 : Real.sin δ ≤ 1/2 := (Real.sin_le hd.1).trans hd.2
  have hrot : coreRadius*Real.cos v+(1/2)*Real.sin v =
      (coreRadius*Real.cos (Real.pi/12)+(1/2)*Real.sin (Real.pi/12))*Real.cos δ+
      ((1/2)*Real.cos (Real.pi/12)-coreRadius*Real.sin (Real.pi/12))*Real.sin δ := by
    rw [show v=Real.pi/12+δ by dsimp [δ]; ring,Real.cos_add,Real.sin_add]
    ring
  have hA := mul_le_mul_of_nonneg_right rotated_west_profile.1
    (show 0 ≤ Real.cos δ by linarith)
  have hB := mul_le_mul_of_nonneg_right rotated_west_profile.2 hs0
  have harad : 23/16+(3/8)*Real.sin δ ≤ a+1/2 := by
    rw [hrot] at ha
    nlinarith
  by_contra! hfail
  have htrans : 1-(9/10)*Real.sin δ ≤ |b|+1/2 := by
    change 1/2 ≤ (9/10)*Real.sin δ-b at hfail
    linarith [neg_le_abs b]
  have hrad0 : 0 ≤ 23/16+(3/8)*Real.sin δ := by linarith
  have htrans0 : 0 ≤ 1-(9/10)*Real.sin δ := by linarith
  have hsqA := mul_nonneg (sub_nonneg.mpr harad)
    (show 0 ≤ a+1/2+(23/16+(3/8)*Real.sin δ) by linarith [h.half_le])
  have hsqB := mul_nonneg (sub_nonneg.mpr htrans)
    (show 0 ≤ |b|+1/2+(1-(9/10)*Real.sin δ) by linarith [abs_nonneg b])
  nlinarith [h.containment,west_fringe_quadratic (Real.sin δ)]

/-- The cardinal-cap fringe is even shorter: its bad transverse inequality
would force a >= 2-rho0+117/500 > rho0. -/
lemma cap_west_fringe_transverse {a b v H : ℝ} (h : ContainedChart a |b|)
    (hv : Real.pi/12 ≤ v ∧ v ≤ 2/5) (hH : coreRadius ≤ H)
    (hcap : H+angularWidth (-v) ≤ centerX (-v) a b) :
    (9/10)*Real.sin (v-Real.pi/12)-b < 1/2 := by
  let δ := v-Real.pi/12
  have hd0 : 0 ≤ δ := by dsimp [δ]; linarith [hv.1]
  have hv0 : 0 ≤ v := by linarith [hv.1,Real.pi_pos]
  have hvmin : 13/50 ≤ v := by linarith [hv.1,twelfth_bounds.1]
  have hc0 : 0 ≤ Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [hv.2,Real.pi_gt_d2]⟩
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hv0
    (by linarith [hv.2,Real.pi_gt_d2])
  have hs := sine_nine_tenths hv0 (by linarith [hv.2])
  have hδ := Real.sin_le hd0
  by_contra! hfail
  have hV : 617/500-(9/10)*v ≤ 1/2-b := by
    change 1/2 ≤ (9/10)*Real.sin δ-b at hfail
    dsimp [δ] at hδ
    linarith [twelfth_bounds.1]
  have hV0 : 0 ≤ 617/500-(9/10)*v := by linarith [hv.2]
  have hprod := mul_le_mul hV hs (by positivity : 0 ≤ (9/10)*v)
    (show 0 ≤ 1/2-b by linarith)
  have hq := mul_nonneg (show 0 ≤ v-13/50 by linarith)
    (show 0 ≤ (9/10)*(1-(9/10)*v) by linarith [hv.2])
  have hbound : 117/500 ≤ (1/2-b)*Real.sin v := by nlinarith
  have hnormal := mul_nonneg (show 0 ≤ a-1/2 by linarith [h.half_le])
    (show 0 ≤ 1-Real.cos v by linarith [Real.cos_le_one v])
  dsimp [angularWidth,centerX] at hcap
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hc0,abs_of_nonneg hs0] at hcap
  dsimp [coreRadius] at hH
  nlinarith [h.a_le_rho0,rho0_upper]

end SquaresInCircles.Six.Analytic
