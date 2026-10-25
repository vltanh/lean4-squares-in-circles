module

public import SquaresInCircles.Eight.TableFree.GlobalGAPairedEGains

/-!
# Subadditivity of the original sorted-circle primary charge

Uncompiled transcription of Section 2 of
`HAND_G3_NONNEGATIVE_A_E_TOTALS_TD0_OR_POSITIVE_TD2_EXCLUSION.md`.
The axis and circle formulas are kept separate. The axis ratio uses
the increasing second derivative and the exact endpoint at 8/15;
the circle ratio then decreases from the matching transition.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PrimaryCharge
open Candidate Secondary TwoPositive.ASupport

def axisF (t : ℝ) : ℝ := t*axialD t-axialCharge t
def circleF (t : ℝ) : ℝ := t*circleD t-circleCharge t

theorem transition_upper : GlobalGA.TwoPositive.ASupport.alpha<(8/15:ℝ) := by
  have hb : 0<axial+1/2 := by linarith [axial_bounds.1]
  have hh := Real.arctan_le_self
    (div_nonneg (show (0:ℝ)≤1/2 by norm_num) hb.le)
  have hratio : (1/2)/(axial+1/2)<4/15 := by
    apply (div_lt_iff₀ hb).mpr
    linarith [axial_bounds.1]
  dsimp only [TwoPositive.ASupport.alpha,TwoPositive.ASupport.beta]
  linarith

theorem axisF_hasDerivAt (t : ℝ) : HasDerivAt axisF (t*axialDD t) t := by
  have h : HasDerivAt axisF (1*axialD t+t*axialDD t-axialD t) t :=
    ((hasDerivAt_id' t).mul (axial_second t)).sub (axial_derivative t)
  convert h using 1
  ring

theorem circleF_hasDerivAt (t : ℝ) : HasDerivAt circleF (t*circleDD t) t := by
  have h : HasDerivAt circleF (1*circleD t+t*circleDD t-circleD t) t :=
    ((hasDerivAt_id' t).mul (circle_second t)).sub (circle_derivative t)
  convert h using 1
  ring

theorem axisDD_monotone : MonotoneOn axialDD (Icc 0 (8/15:ℝ)) := by
  have hd (t : ℝ) : HasDerivAt axialDD (-(-Real.sin t)/2+(axial-1/2)*Real.cos t) t :=
    (((Real.hasDerivAt_cos t).neg).div_const 2).add
      ((Real.hasDerivAt_sin t).const_mul (axial-1/2))
  apply monoOn_of_hasDeriv_nonneg (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => hd t)
  intro t ht
  have hh := transport_trig (show t∈Icc 0 (7/10) from ⟨ht.1.le,by linarith [ht.2]⟩)
  have hp := mul_nonneg (show 0≤axial-1/2 by linarith [axial_bounds.1])
    (show 0≤Real.cos t by linarith [hh.1])
  linarith [hh.2.2.1]

theorem axisF_at_cut : axisF (8/15:ℝ)< -(1/50:ℝ) := by
  have ht : (8/15:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hbracket := PositiveANegativeTD.sine_ge_angle_cos ht
  have hcoeff := mul_le_mul_of_nonneg_right
    (show axial-1/2≤183/200 by linarith [axial_bounds.2])
    (show 0≤Real.sin (8/15:ℝ)-(8/15)*Real.cos (8/15:ℝ) by linarith)
  have hslo := sin_lower_seven (x:=(8/15:ℝ)) (by norm_num)
  have hshi := Arithmetic.sin_le_sin9 (x:=(8/15:ℝ)) (by norm_num)
  have hclo := cos_lower_six (x:=(8/15:ℝ)) (by norm_num)
  have hid : axisF (8/15:ℝ)=
      (1-Real.cos (8/15:ℝ)-(8/15)*Real.sin (8/15:ℝ))/2+
        (axial-1/2)*(Real.sin (8/15:ℝ)-(8/15)*Real.cos (8/15:ℝ)) := by
    dsimp [axisF,axialD,axialCharge]
    ring
  rw [hid]
  norm_num [Arithmetic.sin9,Arithmetic.sin7] at hslo hshi hclo
  nlinarith only [hcoeff,hslo,hshi,hclo]

/-- The increasing axis curvature makes F decrease and then increase.
Its two endpoint bounds therefore control the entire axis interval. -/
theorem axisF_nonpos {t : ℝ} (ht : t∈Icc 0 (8/15:ℝ)) : axisF t≤0 := by
  by_cases hdd : axialDD t≤0
  · have hm : AntitoneOn axisF (Icc 0 t) := by
      apply antiOn_of_hasDeriv_nonpos
        (fun x _ => (axisF_hasDerivAt x).continuousAt.continuousWithinAt)
        (fun x _ => axisF_hasDerivAt x)
      intro x hx
      have hd := axisDD_monotone ⟨hx.1.le,hx.2.le.trans ht.2⟩ ht hx.2.le
      exact mul_nonpos_of_nonneg_of_nonpos hx.1.le (hd.trans hdd)
    have hh := hm ⟨le_rfl,ht.1⟩ ⟨ht.1,le_rfl⟩ ht.1
    simpa [axisF,axialCharge] using hh
  · have hm : MonotoneOn axisF (Icc t (8/15:ℝ)) := by
      apply monoOn_of_hasDeriv_nonneg
        (fun x _ => (axisF_hasDerivAt x).continuousAt.continuousWithinAt)
        (fun x _ => axisF_hasDerivAt x)
      intro x hx
      have hd := axisDD_monotone ht ⟨ht.1.trans hx.1.le,hx.2.le⟩ hx.1.le
      exact mul_nonneg (ht.1.trans hx.1.le) (by linarith)
    have hh := hm ⟨le_rfl,ht.2⟩ ⟨ht.2,le_rfl⟩ ht.2
    exact hh.trans (by linarith [axisF_at_cut])

theorem circleF_nonpos {t : ℝ} (ht : t∈Icc GlobalGA.TwoPositive.ASupport.alpha frameCap) : circleF t≤0 := by
  have ha : 0≤TwoPositive.ASupport.alpha := by linarith [alpha_bounds.1]
  have hm : AntitoneOn circleF (Icc TwoPositive.ASupport.alpha frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => (circleF_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => circleF_hasDerivAt x)
    intro x hx
    have hx' : x∈Icc 0 frameCap := ⟨ha.trans hx.1.le,hx.2.le⟩
    exact mul_nonpos_of_nonneg_of_nonpos hx'.1 (circle_curvature hx')
  have hstart : circleF TwoPositive.ASupport.alpha=axisF TwoPositive.ASupport.alpha := by
    simp only [circleF,axisF,transition_value,transition_derivative]
  have hh := hm ⟨le_rfl,alpha_bounds.2.le⟩ ht ht.1
  rw [hstart] at hh
  exact hh.trans (axisF_nonpos ⟨ha,transition_upper.le⟩)

theorem axis_ratio_antitone {x y : ℝ} (hx : 0<x) (hxy : x≤y) (hy : y≤GlobalGA.TwoPositive.ASupport.alpha) :
    axialCharge y/y≤axialCharge x/x := by
  have hm : AntitoneOn (fun t : ℝ => axialCharge t/t) (Icc x y) := by
    apply antiOn_of_hasDeriv_nonpos (d := fun t => axisF t/t^2)
    · intro t ht
      exact ((axial_derivative t).div (hasDerivAt_id' t)
        (ne_of_gt (hx.trans_le ht.1))).continuousAt.continuousWithinAt
    · intro t ht
      convert (axial_derivative t).div (hasDerivAt_id' t)
        (ne_of_gt (hx.trans ht.1)) using 1
      simp only [axisF]
      ring
    · intro t ht
      have hF := axisF_nonpos (show t∈Icc 0 (8/15:ℝ) from
        ⟨(hx.trans ht.1).le,(ht.2.le.trans hy).trans transition_upper.le⟩)
      exact div_nonpos_of_nonpos_of_nonneg hF (sq_nonneg t)
  exact hm ⟨le_rfl,hxy⟩ ⟨hxy,le_rfl⟩ hxy

theorem circle_ratio_antitone {x y : ℝ} (hx : GlobalGA.TwoPositive.ASupport.alpha≤x) (hxy : x≤y) (hy : y≤frameCap) :
    circleCharge y/y≤circleCharge x/x := by
  have hx0 : 0<x := by linarith [alpha_bounds.1]
  have hm : AntitoneOn (fun t : ℝ => circleCharge t/t) (Icc x y) := by
    apply antiOn_of_hasDeriv_nonpos (d := fun t => circleF t/t^2)
    · intro t ht
      exact ((circle_derivative t).div (hasDerivAt_id' t)
        (ne_of_gt (hx0.trans_le ht.1))).continuousAt.continuousWithinAt
    · intro t ht
      convert (circle_derivative t).div (hasDerivAt_id' t)
        (ne_of_gt (hx0.trans ht.1)) using 1
      simp only [circleF]
      ring
    · intro t ht
      exact div_nonpos_of_nonpos_of_nonneg
        (circleF_nonpos ⟨hx.trans ht.1.le,ht.2.le.trans hy⟩) (sq_nonneg t)
  exact hm ⟨le_rfl,hxy⟩ ⟨hxy,le_rfl⟩ hxy

theorem ratio_antitone {x y : ℝ} (hx : 0<x) (hxy : x≤y) (hy : y≤frameCap) :
    TwoPositive.ASupport.charge y/y≤TwoPositive.ASupport.charge x/x := by
  by_cases hycut : y≤GlobalGA.TwoPositive.ASupport.alpha
  · simpa [TwoPositive.ASupport.charge,hycut,hxy.trans hycut] using axis_ratio_antitone hx hxy hycut
  · by_cases hxcut : x≤GlobalGA.TwoPositive.ASupport.alpha
    · have hleft := axis_ratio_antitone hx hxcut le_rfl
      have hright := circle_ratio_antitone le_rfl (lt_of_not_ge hycut).le hy
      rw [← transition_value] at hright
      simpa [TwoPositive.ASupport.charge,hycut,hxcut] using hright.trans hleft
    · simpa [TwoPositive.ASupport.charge,hycut,hxcut] using circle_ratio_antitone (lt_of_not_ge hxcut).le hxy hy

theorem nonpositive {t : ℝ} (ht : t∈Icc 0 frameCap) : TwoPositive.ASupport.charge t≤0 := by
  by_cases hcut : t≤GlobalGA.TwoPositive.ASupport.alpha
  · have hp := mul_nonpos_of_nonpos_of_nonneg
      (show 1/2-axial≤0 by linarith [axial_bounds.1]) (transport_trig ht).2.2.1
    simp only [TwoPositive.ASupport.charge,if_pos hcut,axialCharge]
    linarith [Real.cos_le_one t]
  · have hh := double_angle t
    have hp := mul_nonneg (half_trig ht).1
      (show 0≤R-Real.cos (t/2) by linarith [radius_bounds.1,Real.cos_le_one (t/2)])
    simp only [TwoPositive.ASupport.charge,if_neg hcut,circleCharge]
    nlinarith only [hh.1,hp]

/-- Equation (5): the two charges combine at the sum of the selected
nonnegative totals without an assumption of global concavity. -/
theorem subadditive {a e : ℝ} (ha : 0≤a) (he : 0≤e) (hs : a+e≤frameCap) :
    TwoPositive.ASupport.charge (a+e)≤TwoPositive.ASupport.charge a+TwoPositive.ASupport.charge e := by
  rcases eq_or_lt_of_le ha with rfl|ha
  · simp
  rcases eq_or_lt_of_le he with rfl|he
  · simp
  have hsum : 0<a+e := by linarith
  have hA := (div_le_div_iff₀ hsum ha).mp
    (ratio_antitone ha (by linarith : a≤a+e) hs)
  have hE := (div_le_div_iff₀ hsum he).mp
    (ratio_antitone he (by linarith : e≤a+e) hs)
  apply le_of_mul_le_mul_right _ hsum
  linarith only [hA,hE]

theorem weighted {a e l : ℝ} (ha : 0≤a) (he : 0≤e)
    (hs : a+e≤frameCap) (hl : 1≤l) :
    l*TwoPositive.ASupport.charge (a+e)≤l*TwoPositive.ASupport.charge a+TwoPositive.ASupport.charge e := by
  have hh := mul_le_mul_of_nonneg_left (subadditive ha he hs) (by linarith : 0≤l)
  have hj := nonpositive (show e∈Icc 0 frameCap from ⟨he,by linarith⟩)
  have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) hj
  nlinarith only [hh,hp]

end SquaresInCircles.Eight.TableFree.GlobalGA.PrimaryCharge
