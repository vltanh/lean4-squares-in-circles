import SquaresInCircles.Six.Analytic.PairConstants
import SquaresInCircles.Six.Stress.VertexEnvelope

/-!
# Rational constants at the geometric pair endpoints

The new lower bound for s comes from one evaluation of its exact defining
quadratic and its negative slope on the small-root interval. Every other
bound is a positive product, a division with a proved positive denominator,
or the defining circle/cap identity. No numerical root estimate is assumed.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Stress

lemma pair_offset_bounds : (8424567:ℝ)/100000000<Six.sStar ∧ Six.sStar<842457/10000000 := by
  refine ⟨?_,Six.sStar_bounds.2⟩
  have hp : 0<(8424567/100000000:ℝ)^2-
      Six.AStar*(8424567/100000000)+Six.BStar := by
    dsimp [Six.AStar,Six.BStar]
    linarith [Six.hStar_lower,Six.hStar_upper]
  by_contra! hs
  have hm := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤8424567/100000000-Six.sStar by linarith)
    (show 8424567/100000000+Six.sStar-Six.AStar≤0 by
      linarith [Six.sStar_lt_fifth,Six.AStar_bounds.1])
  nlinarith [Six.sStar_polynomial]

lemma pair_transverse_bounds : (4202266:ℝ)/10000000<Six.tStar ∧ Six.tStar<4202267/10000000 := by
  have hs := pair_offset_bounds
  have hcL : (121320343:ℝ)/100000000≤-20+30*Six.hStar := by
    linarith [Six.hStar_lower]
  have hcU : -20+30*Six.hStar≤(60660173:ℝ)/50000000 := by
    linarith [Six.hStar_upper]
  have hc0 : 0≤-20+30*Six.hStar := by linarith
  have hlo := mul_le_mul hcL hs.1.le
    (by norm_num : (0:ℝ)≤8424567/100000000) hc0
  have hhi := mul_le_mul hcU hs.2.le Six.sStar_pos.le
    (by norm_num : (0:ℝ)≤60660173/50000000)
  dsimp [Six.tStar]
  constructor <;> nlinarith [Six.hStar_lower,Six.hStar_upper]

lemma pair_ratio_sharp_bounds :
    (3687847:ℝ)/10000000<rStar ∧ rStar<3687848/10000000 ∧
      (6499903:ℝ)/10000000<kStar ∧ kStar<6499904/10000000 := by
  have hs := pair_offset_bounds
  have ht := pair_transverse_bounds
  refine ⟨?_,?_,?_,?_⟩
  · rw [rStar,lt_div_iff₀ rStar_den_pos]
    linarith [hs.1]
  · rw [rStar,div_lt_iff₀ rStar_den_pos]
    linarith [hs.2]
  · rw [kStar,lt_div_iff₀ kStar_den_pos]
    linarith [hs.1,ht.1]
  · rw [kStar,div_lt_iff₀ kStar_den_pos]
    linarith [hs.2,ht.2]

lemma pair_multiplier_sharp_bounds :
    (8896967:ℝ)/10000000<mStar ∧ mStar<8896971/10000000 := by
  have h := pair_ratio_sharp_bounds
  have hl := mul_le_mul
    (show (13687847:ℝ)/10000000≤1+rStar by linarith [h.1]) h.2.2.1.le
    (by norm_num : (0:ℝ)≤6499903/10000000) one_add_rStar_pos.le
  have hu := mul_le_mul
    (show 1+rStar≤(13687848:ℝ)/10000000 by linarith [h.2.1]) h.2.2.2.le
    kStar_pos.le (by norm_num : (0:ℝ)≤13687848/10000000)
  change (13687847/10000000:ℝ)*(6499903/10000000)≤mStar at hl
  change mStar≤(13687848/10000000:ℝ)*(6499904/10000000) at hu
  constructor <;> norm_num at hl hu ⊢ <;> linarith

private lemma qStar_between_endpoint_polynomials :
    (14255886729137489:ℝ)/5000000000000000<Six.qStar ∧
      Six.qStar<(142558873796849:ℝ)/50000000000000 := by
  have hs := pair_offset_bounds
  have hl := mul_nonneg (sub_nonneg.mpr hs.1.le)
    (show 0≤Six.sStar+8424567/100000000 by linarith [Six.sStar_pos])
  have hu := mul_nonneg (sub_nonneg.mpr hs.2.le)
    (show 0≤842457/10000000+Six.sStar by linarith [Six.sStar_pos])
  dsimp [Six.qStar]
  constructor <;> nlinarith

lemma pair_radius_sharp_bounds :
    (16885429:ℝ)/10000000<Six.radius ∧ Six.radius<16885431/10000000 := by
  have hq := qStar_between_endpoint_polynomials
  constructor
  · by_contra! h
    have hp := mul_nonneg (sub_nonneg.mpr h)
      (show 0≤16885429/10000000+Six.radius by linarith [Six.radius_pos])
    nlinarith [Six.radius_sq,hq.1]
  · by_contra! h
    have hp := mul_nonneg (sub_nonneg.mpr h)
      (show 0≤Six.radius+16885431/10000000 by linarith [Six.radius_pos])
    nlinarith [Six.radius_sq,hq.2]

lemma pair_rho_sharp_bounds :
    (11128165:ℝ)/10000000<rhoStar ∧ rhoStar<11128167/10000000 := by
  have hq := qStar_between_endpoint_polynomials
  constructor
  · by_contra! h
    have hp := mul_nonneg (sub_nonneg.mpr h)
      (show 0≤11128165/10000000+rhoStar+1 by linarith [rhoStar_gt_11_10])
    nlinarith [rhoStar_identity,hq.1]
  · by_contra! h
    have hp := mul_nonneg (sub_nonneg.mpr h)
      (show 0≤rhoStar+11128167/10000000+1 by linarith [rhoStar_gt_11_10])
    nlinarith [rhoStar_identity,hq.2]

lemma pair_central_sharp_bounds :
    (1128165:ℝ)/10000000<cStar ∧ cStar<1128167/10000000 := by
  dsimp [cStar]
  constructor <;> linarith [pair_rho_sharp_bounds.1,pair_rho_sharp_bounds.2]

lemma pair_base_sharp_upper : pairBase<(709742:ℝ)/10000000 := by
  have hm := pair_multiplier_sharp_bounds
  have ht := pair_transverse_bounds
  have hp := mul_le_mul hm.2.le
    (show 1/2-Six.tStar≤(797734:ℝ)/10000000 by linarith [ht.1])
    (show 0≤1/2-Six.tStar by linarith [ht.2])
    (by norm_num : (0:ℝ)≤8896971/10000000)
  change pairBase≤(8896971/10000000:ℝ)*(797734/10000000) at hp
  norm_num at hp
  linarith

end SquaresInCircles.Six.Analytic
