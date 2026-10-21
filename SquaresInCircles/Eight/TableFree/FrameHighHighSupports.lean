module

public import SquaresInCircles.Eight.TableFree.FrameMidHighSupports
public import SquaresInCircles.Eight.TableFree.FrameHighHighVaryingCalculus

/-!
# Closed-arc support selection for all high/high signs

The small negative-target multiplier has no interior minimum: if both
coefficients were negative, the exact trigonometric circle would violate
the coefficient norm.  The varying family keeps its multiplier and angle
correlated throughout the full interval.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighHighSupports
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalSupport
open FrameDiagonalSelection FrameDiagonalTrigonometry

theorem positive_target_endpoints {B x : ℝ} (hB : B∈arc false)
    (hx : x∈Icc (7/20:ℝ) (6/5)) :
    min (target false true (39/100) x 0) (target false true (39/100) x b1)≤
      target false true (39/100) x B := by
  apply target_endpoints_of_one_coefficient hB
  right
  have hs := sum_early hx
  norm_num [targetV,transverse,sign,v]
  linarith

theorem middle_negative_target {B x : ℝ} (hB : B∈arc false)
    (hx : x∈Icc (3/5:ℝ) (4/5)) :
    target false false (43/100) x b1≤target false false (43/100) x B := by
  have hD := difference_080_upper ⟨by linarith [hx.1],hx.2⟩
  have hC := sum_middle ⟨hx.1,by linarith [hx.2]⟩
  apply target_last_of_coefficients hB
  · norm_num [targetU,primary,sign,u]
    linarith
  · norm_num [targetV,transverse,sign,v]
    linarith

theorem small_negative_coefficients (x : ℝ) :
    0≤targetU false false (17/50) x ∨ 0≤targetV false false (17/50) x := by
  by_contra h
  push_neg at h
  have hU : u<(17/50)*(Real.sin x-Real.cos x) := by
    norm_num [targetU,primary,sign] at h
    linarith [h.1]
  have hV : v<(17/50)*(Real.sin x+Real.cos x) := by
    norm_num [targetV,transverse,sign] at h
    linarith [h.2]
  have hpU := mul_pos (sub_pos.mpr hU)
    (show 0<(17/50)*(Real.sin x-Real.cos x)+u by
      have hu : 0<u := by norm_num [u]
      linarith)
  have hpV := mul_pos (sub_pos.mpr hV)
    (show 0<(17/50)*(Real.sin x+Real.cos x)+v by
      have hv : 0<v := by norm_num [v]
      linarith)
  have hid : ((17/50:ℝ)*(Real.sin x-Real.cos x))^2+
      ((17/50:ℝ)*(Real.sin x+Real.cos x))^2=2*(17/50:ℝ)^2 := by
    linear_combination (289/1250:ℝ)*(Real.sin_sq_add_cos_sq x)
  norm_num [u,v] at hpU hpV
  nlinarith

theorem small_negative_target_endpoints {B x : ℝ} (hB : B∈arc false) :
    min (target false false (17/50) x 0) (target false false (17/50) x b1)≤
      target false false (17/50) x B :=
  target_endpoints_of_one_coefficient hB (small_negative_coefficients x)

theorem varying_negative_target {B x : ℝ} (hB : B∈arc false)
    (hx : x∈FrameHighHighVaryingCalculus.domain) :
    target false false (FrameHighHighVaryingCalculus.lam x) x b1≤
      target false false (FrameHighHighVaryingCalculus.lam x) x B := by
  let l := FrameHighHighVaryingCalculus.lam x
  have hl : (177/500:ℝ)≤l ∧ l≤247/500 :=
    FrameHighHighVaryingCalculus.multiplier_bounds hx
  have hD := difference_095_upper ⟨by linarith [hx.1],hx.2⟩
  have hC := sum_middle hx
  have hld := mul_le_mul_of_nonneg_left hD.le (show 0≤l by linarith [hl.1])
  have hlc := mul_le_mul (show (177/500:ℝ)≤l from hl.1) hC.le
    (by norm_num : (0:ℝ)≤69/50) (by linarith [hl.1] : 0≤l)
  have hUbound : -targetU false false l x<(127/5000:ℝ) := by
    norm_num [targetU,primary,sign,u]
    nlinarith [hl.2]
  apply target_last_of_derivative hB
  intro z hz
  have hr := slope_high_bounds hz
  by_cases hU : 0≤targetU false false l x
  · have hp := mul_nonneg hU hr.1
    norm_num [targetV,transverse,sign,v]
    linarith
  · have hp := mul_le_mul_of_nonneg_left hr.2.le
      (neg_nonneg.mpr (lt_of_not_ge hU).le)
    norm_num [targetV,transverse,sign,v]
    nlinarith

theorem opposite_source_cut {b : ℝ} (hb : b∈arc false) :
    source false false (73/200) b1≤source false false (73/200) b := by
  apply source_last_of_derivative hb
  intro z hz
  have hr := slope_high_bounds hz
  norm_num [sourceU,sourceV,primary,transverse,sign,u,v]
  linarith [hr.2]

end SquaresInCircles.Eight.TableFree.FrameHighHighSupports
