module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeZeroBounds

/-!
# Eight squares: positive original derivative on the entire zero-source arc

The quotient curvature bound uses the same four positive terms as
the short-source argument.  The previously established target
curvature already makes the comparison slope strictly concave;
its actual two endpoint values close the full later interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

private lemma div_upper {n d nh dl : ℝ} (hn : n≤nh) (hd : dl≤d)
    (hnh : 0≤nh) (hdl : 0<dl) : n/d≤nh/dl := by
  exact (div_le_div_iff₀ (hdl.trans_le hd) hdl).2
    (mul_le_mul hn hd hdl.le hnh)

lemma quotient_curvature {φ : ℝ} (hφ : Domain φ) :
    quotientSecond parameter φ<(179/50:ℝ) := by
  have hh := geometry hφ
  have hu := hh.1
  have hw := hh.2.1
  have hy := hh.2.2.1
  have hf := hh.2.2.2.1
  have hfp := hh.2.2.2.2
  have hw0 : 0≤w parameter φ := by linarith [hw.1]
  have hy0 : 0≤y parameter φ := by linarith [hy.1]
  have hf0 : 0≤SecondWord.PositiveThree.SourceCurve.f parameter φ := by linarith [hf.1]
  have hfp0 : 0≤fp parameter φ := by linarith [hfp.1]
  have ht := lower_trig (domain hφ).2
  have hs0 : 0≤Real.sin φ := by linarith [ht.1]
  have hf2 : (SecondWord.PositiveThree.SourceCurve.f parameter φ)^2≤1 := by nlinarith [hf.2]
  have hw2 := pow_le_pow_left₀ hw0 hw.2 2
  have hu2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/2) hu.1 2
  have hu3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/2) hu.1 3
  have hn1 := mul_le_mul (z_bounds (domain hφ)).2 ht.2.1 hs0 (by norm_num : (0:ℝ)≤3/2)
  have hd1 := mul_le_mul hy.1 hu.1 (by norm_num : (0:ℝ)≤3/2) hy0
  have ht1 := div_upper hn1 hd1 (by norm_num) (by norm_num)
  have hn2 := mul_le_mul hy.2 hf2 (sq_nonneg _) (by norm_num : (0:ℝ)≤333/250)
  have ht2 := div_upper hn2 hu.1 (by norm_num) (by norm_num)
  have hyw := mul_le_mul hy.2 hw.2 hw0 (by norm_num : (0:ℝ)≤333/250)
  have hn3 := mul_le_mul hyw hfp.2 hfp0
    (by norm_num : (0:ℝ)≤(333/250)*(1291/1000))
  have ht3 := div_upper hn3 hu2 (by norm_num) (by norm_num)
  have hyw2 := mul_le_mul (mul_le_mul_of_nonneg_left hy.2 (by norm_num : (0:ℝ)≤2))
    hw2 (sq_nonneg _) (by norm_num : (0:ℝ)≤2*(333/250))
  have hn4 := mul_le_mul hyw2 hf2 (sq_nonneg _)
    (by norm_num : (0:ℝ)≤2*(333/250)*(1291/1000)^2)
  have ht4 := div_upper hn4 hu3 (by norm_num) (by norm_num)
  have hsum := quotientSecond_le (domain hφ)
  dsimp [quotientUpper] at hsum
  norm_num at ht1 ht2 ht3 ht4
  linarith

lemma opposite_product_upper {x y : ℝ}
    (hx : x∈Icc (-(567/500:ℝ)) (21/10))
    (hy : y∈Icc (-(273/1000:ℝ)) (137/100)) : -x*y<(777/500:ℝ) := by
  by_cases hxs : 0≤x
  · by_cases hys : 0≤y
    · nlinarith [mul_nonneg hxs hys]
    · have hh := mul_le_mul hx.2 (show -y≤273/1000 by linarith [hy.1])
        (neg_nonneg.mpr (le_of_not_ge hys)) (by norm_num : (0:ℝ)≤21/10)
      nlinarith
  · by_cases hys : 0≤y
    · have hh := mul_le_mul (show -x≤567/500 by linarith [hx.1]) hy.2 hys
        (by norm_num : (0:ℝ)≤567/500)
      nlinarith
    · nlinarith [mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hxs) (le_of_not_ge hys)]

lemma slope_curvature {φ : ℝ} (hφ : Domain φ) :
    slopeSecond g parameter φ< -(21/100:ℝ) := by
  have hq := mul_lt_mul_of_pos_left (quotient_curvature hφ)
    (show 0<g by norm_num [g])
  have hvel := velocities hφ
  have hlabel := label_curvature hφ
  have hbp2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤(3/2)*(799/1000)) hvel.1 2
  have hthird := mul_le_mul hlabel.2.le hbp2
    (by norm_num : (0:ℝ)≤((3/2)*(799/1000))^2)
    (by linarith [hlabel.2] : 0≤LLabel.d3 (target parameter φ))
  have hlast := opposite_product_upper hlabel.1 hvel.2
  dsimp [slopeSecond,g] at *
  nlinarith

lemma slope_concave : ConcaveOn ℝ (Icc (13/10) (Real.pi/2)) (slope g parameter) :=
  concave_of_deriv2
    (fun φ hφ => slope_hasDerivAt g (domain hφ) (target_mem hφ))
    (fun φ hφ => slopeFirst_hasDerivAt g (domain hφ) (target_mem hφ))
    (fun φ hφ => by linarith [slope_curvature hφ])

theorem slope_positive {φ : ℝ} (hφ : Domain φ) : 0<slope g parameter φ :=
  (lt_min left_slope right_slope).trans_le
    (slope_concave.min_le_of_mem_Icc left_mem right_mem hφ)

theorem original_derivative {φ : ℝ} (hφ : Domain φ) :
    0<FirstContact.first (target parameter φ) φ := by
  have hg : g≤VLabel.d1 (1/2-parameter) := by
    norm_num [parameter,g]
    exact V_zero_first_lower.le
  exact (slope_positive hφ).trans_le
    (original_slope_of_lower (domain hφ) (target_mem hφ) hg)

end SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact
