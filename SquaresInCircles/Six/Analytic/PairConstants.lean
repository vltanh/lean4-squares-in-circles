import SquaresInCircles.Six.Analytic.CandidateBounds

/-!
# Candidate constants for the analytic pair argument

All bounds follow from the exact candidate quadratic and positive products.
No normalization or numerical evaluator is imported to prove a constant.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Stress

lemma pair_multiplier_bounds :
    (46:ℝ)/125<rStar ∧ rStar<37/100 ∧ (889:ℝ)/1000<mStar ∧ mStar<893/1000 := by
  have hr := candidate_ratio_bounds
  have hl := mul_le_mul
    (show (271:ℝ)/198≤1+rStar by linarith [hr.1]) hr.2.2.1.le
    (by norm_num : (0:ℝ)≤115/177) one_add_rStar_pos.le
  have hu := mul_le_mul
    (show 1+rStar≤(434:ℝ)/317 by linarith [hr.2.1]) hr.2.2.2.le
    kStar_pos.le (by norm_num : (0:ℝ)≤434/317)
  change (271/198:ℝ)*(115/177)≤mStar at hl
  change mStar≤(434/317:ℝ)*(922/1415) at hu
  exact ⟨by linarith [hr.1],by linarith [hr.2.1],
    by norm_num at hl; linarith,by norm_num at hu; linarith⟩

lemma pair_coarse_constants :
    (46:ℝ)/125<rStar ∧ rStar<37/100 ∧ (889:ℝ)/1000<mStar ∧ mStar<893/1000 ∧
      0<cStar ∧ cStar<113/1000 ∧ 0<rhoStar ∧ rhoStar<1113/1000 ∧
      0<Six.radius ∧ Six.radius<1689/1000 := by
  obtain ⟨hrl,hru,hml,hmu⟩ := pair_multiplier_bounds
  refine ⟨hrl,hru,hml,hmu,cStar_pos,?_,?_,rhoStar_upper,
    Six.radius_pos,candidate_radius_bounds.2⟩
  · dsimp [cStar]
    linarith [rhoStar_upper]
  · linarith [rhoStar_gt_11_10]

lemma north_curvature_reserve : Six.radius*rStar/(1+rStar)<457/1000 := by
  have hr := pair_multiplier_bounds
  have hratio : rStar/(1+rStar)≤(37:ℝ)/137 := by
    apply (div_le_iff₀ one_add_rStar_pos).mpr
    linarith [hr.2.1]
  have hnonneg : 0≤rStar/(1+rStar) := div_nonneg rStar_pos.le one_add_rStar_pos.le
  have hp := mul_le_mul candidate_radius_bounds.2.le hratio hnonneg
    (by norm_num : (0:ℝ)≤1689/1000)
  have hb : Six.radius*rStar/(1+rStar)≤(1689/1000:ℝ)*(37/137) := by
    simpa only [mul_div_assoc] using hp
  norm_num at hb
  linarith

lemma alternate_north_curvature_reserve : rhoStar*rStar/(1+rStar)<301/1000 := by
  have hr := pair_multiplier_bounds
  have hratio : rStar/(1+rStar)≤(37:ℝ)/137 := by
    apply (div_le_iff₀ one_add_rStar_pos).mpr
    linarith [hr.2.1]
  have hnonneg : 0≤rStar/(1+rStar) := div_nonneg rStar_pos.le one_add_rStar_pos.le
  have hp := mul_le_mul rhoStar_upper.le hratio hnonneg
    (by norm_num : (0:ℝ)≤1113/1000)
  have hb : rhoStar*rStar/(1+rStar)≤(1113/1000:ℝ)*(37/137) := by
    simpa only [mul_div_assoc] using hp
  norm_num at hb
  linarith

end SquaresInCircles.Six.Analytic
