module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalSelection

/-!
# Actual middle-source and high-target support selection

The negative middle source uses a concave support whose second endpoint
is strictly larger.  The target selections use the original signed
coefficient derivatives on the entire closed intrinsic arc.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighSupports
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalSupport
open FrameDiagonalSelection FrameDiagonalTrigonometry FrameDiagonalCuts
open FramePairCalculus

theorem positive_source {b : ℝ} (hb : b∈arc true) :
    source true true (7/20) b1≤source true true (7/20) b := by
  apply source_first_of_derivative hb
  intro z hz
  have hr := slope_mid_bounds hz
  norm_num [sourceU,sourceV,primary,transverse,sign,k,q]
  linarith [hr.1]

theorem negative_source_endpoints :
    source true false (2/5) b1+(1/2000:ℝ)<source true false (2/5) b2 := by
  dsimp [source,linear,sourceU,sourceV,primary,transverse,sign]
  rw [A_b1,A_b2,b1_eq,b2_eq]
  norm_num [k,q]
  linarith [a1_precise.2,a2_precise.1]

theorem negative_source {b : ℝ} (hb : b∈arc true) :
    source true false (2/5) b1≤source true false (2/5) b := by
  have he := source_endpoints hb
    (show 0≤sourceU true false (2/5) by norm_num [sourceU,primary,sign,k])
  change min (source true false (2/5) b1) (source true false (2/5) b2)≤_ at he
  have hc : source true false (2/5) b1≤source true false (2/5) b2 := by
    linarith [negative_source_endpoints]
  exact (le_min le_rfl hc).trans he

theorem high_target_early {B x : ℝ} (hB : B∈arc false)
    (hx : x∈Icc 0 (61/100:ℝ)) :
    target false false (11/20) x b1≤target false false (11/20) x B := by
  have hxq := rational_quadrant ⟨hx.1,by linarith [hx.2]⟩
  have hD := difference_061_negative hx
  have hw := FrameCoreArc.width_one_le x
  rw [(first_width hxq).1] at hw
  apply target_last_of_coefficients hB
  · norm_num [targetU,primary,sign,u]
    linarith
  · norm_num [targetV,transverse,sign,v]
    linarith

theorem high_target_negative {B x : ℝ} (hB : B∈arc false)
    (hx : x∈Icc (9/10:ℝ) (6/5)) :
    target false false (2/5) x b1≤target false false (2/5) x B := by
  have hC := sum_negative hx
  have hW := weighted_negative hx
  apply target_last_of_derivative hB
  intro z hz
  have hr := slope_high_bounds hz
  by_cases hU : 0≤targetU false false (2/5) x
  · have hp := mul_nonneg hU hr.1
    norm_num [targetU,targetV,primary,transverse,sign,u,v] at hp ⊢
    linarith
  · have hU' : targetU false false (2/5) x≤0 := (lt_of_not_ge hU).le
    have hp := mul_le_mul_of_nonneg_left hr.2.le (neg_nonneg.mpr hU')
    norm_num [targetU,targetV,primary,transverse,sign,u,v] at hp ⊢
    linarith

theorem high_target_opposite {B x : ℝ} (hB : B∈arc false)
    (hx : x∈Icc (1:ℝ) (13/10)) :
    target false true (2/5) x 0≤target false true (2/5) x B := by
  have hD := difference_100_positive hx
  have hC := sum_high hx
  apply target_first_of_coefficients hB
  · norm_num [targetU,primary,sign,u]
    linarith
  · norm_num [targetV,transverse,sign,v]
    linarith

theorem positive_high_source {lam b : ℝ} (hb : b∈arc false)
    (hlam : lam∈Icc (17/50:ℝ) (43/100)) :
    source false true lam 0≤source false true lam b := by
  apply source_first_of_coefficients hb
  · norm_num [sourceU,primary,sign,u]
    linarith [hlam.1]
  · norm_num [sourceV,transverse,sign,v]
    linarith [hlam.2]

theorem middle_target_positive {B x : ℝ} (hB : B∈arc true)
    (hx : x∈Icc (11/10:ℝ) (71/50)) :
    target true true (1/2) x b1≤target true true (1/2) x B := by
  have hD := difference_110_lower hx
  have hC := sum_target_middle hx
  have ht := FrameLowPair.quadrant
    (rational_quadrant ⟨by linarith [hx.1],hx.2⟩)
  have hU : 0≤targetU true true (1/2) x := by
    norm_num [targetU,primary,sign,k]
    linarith
  have hUb : targetU true true (1/2) x<(1319906/1000000:ℝ) := by
    norm_num [targetU,primary,sign,k]
    linarith
  apply target_first_of_derivative hB
  intro z hz
  have hr := slope_mid_bounds hz
  have hp := mul_le_mul_of_nonneg_left hr.2.le hU
  norm_num [targetU,targetV,primary,transverse,sign,k,q] at hUb hp ⊢
  linarith

theorem middle_target_opposite_endpoints {B x : ℝ} (hB : B∈arc true) :
    min (target true true (2/5) x b1) (target true true (2/5) x b2)≤
      target true true (2/5) x B := by
  apply target_endpoints hB
  have hs := Real.sin_le_one x
  have hc := Real.neg_one_le_cos x
  norm_num [targetU,primary,sign,k]
  linarith

end SquaresInCircles.Eight.TableFree.FrameMidHighSupports
