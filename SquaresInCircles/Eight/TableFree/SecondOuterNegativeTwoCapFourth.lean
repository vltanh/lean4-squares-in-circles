module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoCapSupport

/-!
# Positive fourth derivative on the full endpoint-angle contact

The target lies beyond the source on the same circle.  The increasing
fourth-derivative kernel pays the source fourth derivative.  A single
whole-domain projection bound pays the possibly negative target second
derivative.  The remaining term is positive.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.CapCurve

open CommonQuarter CorePairGeometry Arithmetic

lemma small_reference_mem : (61/500:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma small_reference_second : (-57/50:ℝ)<TLabel.d2 (61/500) := by
  have hh := TLabel.second_chart_reference (outer_domain small_reference_mem)
    (l := (2348/1250:ℝ)) (u := (3757/2000:ℝ))
    (dlo := (-57/50:ℝ)) (dhi := (-113/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hh.1

lemma small_reference_third : (173/100:ℝ)<TLabel.d3 (61/500) := by
  have hb := outer_domain small_reference_mem
  have hu := shifted_chart_reference hb
    (l := (2348/1250:ℝ)) (u := (3757/2000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hp := U_positive hb
  have he := TLabel.third_numerator hb
  have hpow := pow_le_pow_left₀ hp.le hu.2.le 5
  have hp5 := pow_pos hp 5
  norm_num [TLabel,W,Q0] at he hpow
  nlinarith

lemma target_curvature_lower {b : ℝ} (hb : Domain b) :
    (-57/50:ℝ)<TLabel.d2 (height b) ∧ (173/100:ℝ)<TLabel.d3 (height b) := by
  have ht := target_mem hb
  have hh := (height_positive hb.1).le
  exact ⟨small_reference_second.trans_le
    (T_second_monotone small_reference_mem ht hh),
    small_reference_third.trans_le (T_third_monotone small_reference_mem ht hh)⟩

lemma leading_fourth_positive {b : ℝ} (hb : Domain b) :
    0< -PLabel.d4 b+TLabel.d4 (height b)*(k b)^4 := by
  have hp := P_fourth_positive hb.1
  have hdom := target_fourth_dominates hb.1 (target_mem hb)
    (target_above_source hb.1).le
  have hk := (k_bounds hb.1).1
  have hk0 : 0<k b := by linarith
  have hpow := pow_lt_pow_left₀ (by norm_num : (0:ℝ)≤21/25) hk (by norm_num : (4:ℕ)≠0)
  have hpaid : 1<8*(k b)^4 := by norm_num at hpow; linarith
  have hleft := mul_lt_mul_of_pos_left hpaid hp
  have hright := mul_lt_mul_of_pos_right hdom (pow_pos hk0 4)
  nlinarith

lemma middle_fourth_positive {b : ℝ} (hb : Domain b) :
    0<6*TLabel.d3 (height b)*(k b)^2*k1 b+
      TLabel.d2 (height b)*(3*(k1 b)^2+4*k b*k2 b) := by
  have hk := k_bounds hb.1
  have hk0 : 0<k b := by linarith [hk.1]
  have hden : 0<6*(k b)^2*k1 b := by positivity
  have hnum : 0<3*(k1 b)^2+4*k b*k2 b := by positivity
  have hr0 : 0<curvatureRatio b := div_pos hnum hden
  have hr := curvatureRatio_upper hb
  have ht := target_curvature_lower hb
  have hproduct := mul_pos (show 0<TLabel.d2 (height b)+57/50 by linarith [ht.1]) hr0
  have hsum : 0<TLabel.d3 (height b)+TLabel.d2 (height b)*curvatureRatio b := by
    nlinarith [ht.2]
  have hfactor := mul_pos hden hsum
  have he : 6*(k b)^2*k1 b*curvatureRatio b=3*(k1 b)^2+4*k b*k2 b := by
    dsimp [curvatureRatio]
    field_simp [hden.ne']
  nlinarith

theorem fourth_positive {b : ℝ} (hb : Domain b) : 0<fourth b := by
  have hlead := leading_fourth_positive hb
  have hmiddle := middle_fourth_positive hb
  have hlast := mul_pos (show 0<TLabel.d1 (height b) by
    linarith [T_first_lower (target_mem hb)]) (k_bounds hb.1).2.2.2
  dsimp [fourth]
  linarith

lemma third_monotone {b : ℝ} (hb : Domain b) : MonotoneOn third (Icc 0 b) :=
  monoOn_of_hasDeriv_nonneg
    (fun t ht => (third_hasDerivAt (before hb ht)).continuousAt.continuousWithinAt)
    (fun t ht => third_hasDerivAt (before hb (Ioo_subset_Icc_self ht)))
    (fun t ht => (fourth_positive (before hb (Ioo_subset_Icc_self ht))).le)

lemma negative_second_concave {b : ℝ} (hb : Domain b) :
    ConcaveOn ℝ (Icc 0 b) (fun t => -second t) := by
  apply concave_of_deriv2
    (fun t ht => (second_hasDerivAt (before hb ht)).neg)
    (fun t ht => (third_hasDerivAt (before hb ht)).neg)
  intro t ht
  linarith [fourth_positive (before hb ht)]

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.CapCurve
