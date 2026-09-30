import SquaresInCircles.Six.Candidate
import SquaresInCircles.Six.Stress.ExactSupport

/-!
# Candidate-radius constants independent of normalization

These definitions and elementary bounds have been separated from the packing
normalization interface. They use only the candidate algebra and geometric
support definitions; no normalization certificate or fixed-stress table is
imported to prove an inequality about a constant.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

def rhoStar : ℝ := rhoAt Six.radius
def cStar : ℝ := rhoStar - 1

lemma radius_gt_three_halves : 3 / 2 < Six.radius := by
  have hs := Six.sStar_pos
  have hq : 5 / 2 < Six.qStar := by
    dsimp [Six.qStar]
    nlinarith [sq_nonneg Six.sStar]
  nlinarith [Six.radius_sq, Six.radius_pos]

lemma radius_gt_half : 1 / 2 < Six.radius := by linarith [radius_gt_three_halves]

lemma rhoStar_identity : rhoStar ^ 2 + rhoStar + 1 / 2 = Six.qStar := by
  have hnonneg : 0 ≤ Six.radius ^ 2 - 1 / 4 := by
    nlinarith [radius_gt_half, Six.radius_pos]
  have h := Real.sq_sqrt hnonneg
  dsimp [rhoStar, rhoAt]
  rw [← Six.radius_sq]
  nlinarith

lemma rhoStar_gt_11_10 : 11 / 10 < rhoStar := by
  have hs := Six.sStar_bounds.1
  have hp := mul_nonneg (show 0 ≤ Six.sStar - 2 / 25 by linarith)
    (show 0 ≤ Six.sStar + 2 / 25 by linarith [Six.sStar_pos])
  have hq : (8 / 5 : ℝ) ^ 2 < Six.radius ^ 2 - 1 / 4 := by
    rw [Six.radius_sq]
    dsimp [Six.qStar]
    nlinarith
  have hroot := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ (8 / 5) ^ 2) hq
  rw [Real.sqrt_sq (by norm_num)] at hroot
  dsimp [rhoStar, rhoAt]
  linarith

lemma rhoStar_lt_rho0 : rhoStar < rho0 := by
  have hroot := Real.sqrt_lt_sqrt
    (show 0 ≤ Six.radius ^ 2 - 1 / 4 by nlinarith [radius_gt_half, Six.radius_pos])
    (show Six.radius ^ 2 - 1 / 4 < Q0 - 1 / 4 by
      rw [Six.radius_sq]; linarith [Six.qStar_lt_Q0])
  dsimp [rhoStar, rhoAt, rho0]
  linarith

lemma rhoStar_upper : rhoStar < 1113 / 1000 := rhoStar_lt_rho0.trans rho0_upper
lemma cStar_pos : 0 < cStar := by dsimp [cStar]; linarith [rhoStar_gt_11_10]
lemma cStar_lt_c0 : cStar < c0 := by dsimp [cStar, c0]; linarith [rhoStar_lt_rho0]

lemma sharp_coordinate_bound {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hc : (a + 1 / 2) ^ 2 + (u + 1 / 2) ^ 2 ≤ Six.qStar) : a ≤ rhoStar := by
  have hs : (a + 1 / 2) ^ 2 ≤ Six.radius ^ 2 - 1 / 4 := by
    rw [Six.radius_sq]
    nlinarith [sq_nonneg u]
  have hh := Real.le_sqrt_of_sq_le hs
  dsimp [rhoStar, rhoAt]
  linarith

lemma sharp_center_radius {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hc : (a + 1 / 2) ^ 2 + (u + 1 / 2) ^ 2 ≤ Six.qStar) :
    a ^ 2 + u ^ 2 ≤ rhoStar ^ 2 := by
  by_contra! h
  have hsum : a + u < rhoStar := by nlinarith [rhoStar_identity]
  have hp := mul_pos (sub_pos.mpr hsum)
    (show 0 < rhoStar + a + u by linarith [rhoStar_gt_11_10])
  nlinarith [mul_nonneg ha hu]

lemma sharp_projection_bound {a b t : ℝ}
    (ha : 0 ≤ a) (hc : (a + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Six.qStar) :
    a * Real.cos t - b * Real.sin t ≤ rhoStar := by
  have hn := sharp_center_radius ha (abs_nonneg b) hc
  rw [sq_abs] at hn
  have hid : (a * Real.cos t - b * Real.sin t) ^ 2 +
      (a * Real.sin t + b * Real.cos t) ^ 2 = a ^ 2 + b ^ 2 := by
    linear_combination (a ^ 2 + b ^ 2) * (Real.sin_sq_add_cos_sq t)
  have hs : (a * Real.cos t - b * Real.sin t) ^ 2 ≤ rhoStar ^ 2 := by
    nlinarith [sq_nonneg (a * Real.sin t + b * Real.cos t)]
  by_contra! h
  have hp := mul_pos (sub_pos.mpr h)
    (show 0 < a * Real.cos t - b * Real.sin t + rhoStar by linarith [rhoStar_gt_11_10])
  nlinarith

end SquaresInCircles.Six.Stress
