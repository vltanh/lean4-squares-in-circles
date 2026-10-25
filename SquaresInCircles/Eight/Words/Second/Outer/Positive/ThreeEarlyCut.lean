module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyCutBounds

/-!
# Eight squares: positive original derivative at the moving source `0.35` cut

The exact quotient curvature is bounded above by four positive
terms.  The negative target-label term dominates their sum on the
whole early arc, giving a strictly concave derivative.  Its two
actual endpoint values therefore prove positivity everywhere.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.EarlyCut

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

private lemma div_upper {n d nh dl : ℝ} (hn : n≤nh) (hd : dl≤d)
    (hnh : 0≤nh) (hdl : 0<dl) : n/d≤nh/dl := by
  have hdp := hdl.trans_le hd
  exact (div_le_div_iff₀ hdp hdl).2 (mul_le_mul hn hd hdl.le hnh)

lemma quotient_curvature {φ : ℝ} (hφ : Domain φ) :
    quotientSecond parameter φ<(149/50:ℝ) := by
  have hh := geometry hφ
  have hu := hh.1
  have hw := hh.2.1
  have hy := hh.2.2.1
  have hf := hh.2.2.2.1
  have hfp := hh.2.2.2.2
  have hu0 : 0≤u parameter φ := by linarith [hu.1]
  have hw0 : 0≤w parameter φ := by linarith [hw.1]
  have hy0 : 0≤y parameter φ := by linarith [hy.1]
  have hf0 : 0≤SecondWord.PositiveThree.SourceCurve.f parameter φ := by linarith [hf.1]
  have hfp0 : 0≤fp parameter φ := by linarith [hfp.1]
  have hs0 : 0≤Real.sin φ := by linarith [(lower_trig (domain hφ).2).1]
  have hf2 := pow_le_pow_left₀ hf0 hf.2 2
  have hw2 := pow_le_pow_left₀ hw0 hw.2 2
  have hu2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤151/100) hu.1 2
  have hu3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤151/100) hu.1 3
  have hn1 := mul_le_mul (z_upper hφ) (sine_upper hφ) hs0
    (by norm_num : (0:ℝ)≤557/500)
  have hd1 := mul_le_mul hy.1 hu.1 (by norm_num : (0:ℝ)≤151/100) hy0
  have ht1 := div_upper hn1 hd1 (by norm_num) (by norm_num)
  have hn2 := mul_le_mul hy.2 hf2 (sq_nonneg _) (by norm_num : (0:ℝ)≤351/200)
  have ht2 := div_upper hn2 hu.1 (by norm_num) (by norm_num)
  have hyw := mul_le_mul hy.2 hw.2 hw0 (by norm_num : (0:ℝ)≤351/200)
  have hn3 := mul_le_mul hyw hfp.2 hfp0
    (by norm_num : (0:ℝ)≤(351/200)*(1279/1000))
  have ht3 := div_upper hn3 hu2 (by norm_num) (by norm_num)
  have hyw2 := mul_le_mul (mul_le_mul_of_nonneg_left hy.2 (by norm_num : (0:ℝ)≤2))
    hw2 (sq_nonneg _) (by norm_num : (0:ℝ)≤2*(351/200))
  have hn4 := mul_le_mul hyw2 hf2 (sq_nonneg _)
    (by norm_num : (0:ℝ)≤2*(351/200)*(1279/1000)^2)
  have ht4 := div_upper hn4 hu3 (by norm_num) (by norm_num)
  have hsum := quotientSecond_le (domain hφ)
  dsimp [quotientUpper] at hsum
  norm_num at ht1 ht2 ht3 ht4
  linarith

lemma slope_curvature {φ : ℝ} (hφ : Domain φ) :
    slopeSecond (VLabel.d1 (7/20)) parameter φ< -(27/1000:ℝ) := by
  have hquot := quotient_curvature hφ
  have hg0 : 0≤VLabel.d1 (7/20) := by linarith [source_first.1]
  have hq1 := mul_le_mul_of_nonneg_left hquot.le hg0
  have hq2 := mul_lt_mul_of_pos_right source_first.2
    (by norm_num : (0:ℝ)<149/50)
  have hvel := velocities hφ
  have hlabel := label_curvature hφ
  have hbp2 := pow_le_pow_left₀
    (by norm_num : (0:ℝ)≤(151/100)*(79/125)) hvel.1 2
  have hlabel0 : 0≤LLabel.d3 (target parameter φ) := by linarith [hlabel.2]
  have hthird := mul_le_mul hlabel.2.le hbp2
    (by norm_num : (0:ℝ)≤((151/100)*(79/125))^2) hlabel0
  have hlast := opposite_product_upper hlabel.1 hvel.2
  dsimp [slopeSecond]
  nlinarith

lemma slope_concave : ConcaveOn ℝ (Icc lowerAngle (13/10))
    (slope (VLabel.d1 (7/20)) parameter) :=
  concave_of_deriv2
    (fun φ hφ => slope_hasDerivAt _ (domain hφ) (target_mem hφ))
    (fun φ hφ => slopeFirst_hasDerivAt _ (domain hφ) (target_mem hφ))
    (fun φ hφ => by linarith [slope_curvature hφ])

theorem slope_positive {φ : ℝ} (hφ : Domain φ) :
    0<slope (VLabel.d1 (7/20)) parameter φ := by
  have hh := slope_concave.min_le_of_mem_Icc left_mem right_mem hφ
  exact (lt_min left_slope right_slope).trans_le hh

theorem original_derivative {φ : ℝ} (hφ : Domain φ) :
    0<FirstContact.first (target parameter φ) φ := by
  have he := original_slope (domain hφ) (target_mem hφ)
  have hk : (1/2:ℝ)-parameter=7/20 := by norm_num [parameter]
  rw [hk] at he
  rw [he]
  exact slope_positive hφ

end SquaresInCircles.Eight.SecondWord.PositiveThree.EarlyCut
