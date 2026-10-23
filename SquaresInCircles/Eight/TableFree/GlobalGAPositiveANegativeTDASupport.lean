module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveANegativeTDLowSource

/-!
# Whole-interval A support bounds for the negative-TD2 stress

Uncompiled transcription of Section 6 and the A endpoint estimates in
Section 7 of the positive-A/negative-TD2 hand proof. The two actual support
branches retain their common value and derivative at the intrinsic angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveANegativeTD.ABounds
open Secondary PositiveAngularEnvelope TwoPositive.ASupport

theorem alpha_upper : alpha<(103/200:ℝ) := by
  have hx : (103/400:ℝ)∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_gt_three]
  have hc := Real.cos_pos_of_mem_Ioo hx
  have hs : 0≤Real.sin (103/400:ℝ) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by norm_num) (by linarith [Real.pi_gt_three])
  have hA : 0<axial+1/2 := by linarith [axial_bounds.1]
  have htan : (1/2)/(axial+1/2)<Real.tan (103/400:ℝ) := by
    rw [Real.tan_eq_sin_div_cos,div_lt_div_iff₀ hA hc]
    have hsl := Real.sin_ge_sub_cube (show (0:ℝ)≤103/400 by norm_num)
    have hcu := cos_upper_four (show (0:ℝ)≤103/400 by norm_num)
    have hm := mul_le_mul_of_nonneg_right
      (show (19/10:ℝ)≤axial+1/2 by linarith [axial_bounds.1]) hs
    norm_num at hsl hcu ⊢
    linarith
  by_contra! hnot
  have hxβ : (103/400:ℝ)≤beta := by dsimp [alpha] at hnot; linarith
  have hm := Real.strictMonoOn_tan.monotoneOn hx
    (show beta∈Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [beta_mem.1,Real.pi_pos],beta_mem.2⟩) hxβ
  rw [show Real.tan beta=(1/2)/(axial+1/2) by exact Real.tan_arctan _] at hm
  linarith

theorem axial_second_upper {a : ℝ} (ha : a∈Icc 0 alpha) : axialDD a<1/50 := by
  have haU : a≤(103/200:ℝ) := ha.2.trans alpha_upper.le
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi ha.1
    (by linarith [Real.pi_gt_three] : (103/200:ℝ)≤Real.pi) haU
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [ha.1,Real.pi_pos]) (by linarith [Real.pi_gt_three]) haU
  have hsin0 : 0≤Real.sin a := (transport_trig
    (show a∈Icc 0 frameCap from ⟨ha.1,ha.2.trans alpha_bounds.2.le⟩)).2.2.1
  have hC := cos_lower_six (show (0:ℝ)≤103/200 by norm_num)
  have hS := sin_upper_five (show (0:ℝ)≤103/200 by norm_num)
  have hm := mul_le_mul_of_nonneg_right
    (show axial-1/2≤183/200 by linarith [axial_bounds.2]) hsin0
  norm_num at hC hS
  dsimp [axialDD]
  linarith

theorem axial_derivative_bounds {a : ℝ} (ha : a∈Icc 0 frameCap) :
    -(61/50:ℝ)<axialD a ∧ axialD a< -(69/100:ℝ) := by
  obtain ⟨hc,hc1,hs0,hs1,_⟩ := transport_trig ha
  have hp : (1/2)*Real.sin a+(183/200)*Real.cos a<(21/20:ℝ) := by
    have hsquare : ((1/2)*Real.sin a+(183/200)*Real.cos a)^2≤
        (1/4:ℝ)+(183/200)^2 := by
      nlinarith [Real.sin_sq_add_cos_sq a,
        sq_nonneg ((183/200)*Real.sin a-(1/2)*Real.cos a)]
    nlinarith
  have hupper := mul_le_mul_of_nonneg_right
    (show axial-1/2≤183/200 by linarith [axial_bounds.2]) (by linarith : 0≤Real.cos a)
  have hlower := mul_le_mul
    (show (1829/2000:ℝ)≤axial-1/2 by linarith [axial_bounds.1]) hc.le
    (by norm_num : (0:ℝ)≤7648/10000) (by linarith [axial_bounds.1])
  dsimp [axialD]
  constructor <;> linarith

theorem circle_derivative_bounds {a : ℝ} (ha : a∈Icc 0 frameCap) :
    -(61/50:ℝ)<circleD a ∧ circleD a< -(69/100:ℝ) := by
  obtain ⟨hc,hc1,hs0,hs1,_⟩ := transport_trig ha
  have hRu := mul_le_mul_of_nonneg_left (Real.cos_le_one (a/2)) (Real.sqrt_nonneg qCap)
  have hC := Real.one_sub_sq_div_two_le_cos (x:=a/2)
  have ha2 : (a/2)^2≤(7/20:ℝ)^2 := by
    apply pow_le_pow_left₀ (by linarith [ha.1])
    dsimp [frameCap] at ha
    linarith [ha.2]
  have hhalf : (751/800:ℝ)≤Real.cos (a/2) := by nlinarith
  have hRl := mul_le_mul
    (show (197/100:ℝ)≤R by linarith [radius_bounds.1]) hhalf (by norm_num)
    (Real.sqrt_nonneg qCap)
  dsimp [circleD]
  constructor <;> linarith [radius_bounds.2]

theorem charge_left_lower : -(159/1000:ℝ)<charge (1/6:ℝ) := by
  rw [charge_low (by norm_num)]
  have hc := cos_lower_six (show (0:ℝ)≤1/6 by norm_num)
  have hs := sin_upper_five (show (0:ℝ)≤1/6 by norm_num)
  have hs0 : 0≤Real.sin (1/6:ℝ) := (transport_trig
    (show (1/6:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).2.2.1
  have hm := mul_le_mul_of_nonneg_right
    (show axial-1/2≤183/200 by linarith [axial_bounds.2]) hs0
  norm_num at hc hs
  dsimp [axialCharge]
  linarith

theorem charge_cap_lower : -(713/1000:ℝ)<charge frameCap := by
  have he : ¬frameCap≤alpha := by dsimp [frameCap]; linarith [alpha_upper]
  rw [charge,if_neg he]
  have hs := sin_lower_seven (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hhalf := sin_upper_five (show (0:ℝ)≤frameCap/2 by norm_num [frameCap])
  have hs0 : 0≤Real.sin (frameCap/2) := (half_trig
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).1
  have hm := mul_le_mul_of_nonneg_right radius_bounds.2.le hs0
  norm_num [frameCap] at hs hhalf
  dsimp [circleCharge]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveANegativeTD.ABounds
