import SquaresInCircles.Six.Stress.CandidateStressConstants

/-!
# Rational bounds for the constants of the model

`sStar > 421/5000`, since the quadratic `s² - AStar s + BStar` is positive at
`421/5000` and decreasing up to its smaller root, and `tStar > 21/50` by its
affine formula in `sStar`. Products and quotients of positive rational bounds
then bound the ratios `rStar` and `kStar` of the stress of the model, the length
`2 hStar mStar` of its force on D, the cap offset `rhoStar`, the optimal radius
`radius` and the product `2 hStar mStar rhoStar`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Stress

/-- `sStar > 421/5000`: the quadratic is positive at `421/5000` and decreasing
on `[0, 1/5]`, which contains `sStar`. -/
theorem candidate_offset_lower : (421 : ℝ) / 5000 < Six.sStar := by
  have hp : 0 < (421 / 5000 : ℝ) ^ 2 - Six.AStar * (421 / 5000) + Six.BStar := by
    dsimp [Six.AStar, Six.BStar]
    linarith [Six.hStar_lower, Six.hStar_upper]
  by_contra! hs
  have hproduct := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 421 / 5000 - Six.sStar by linarith)
    (show 421 / 5000 + Six.sStar - Six.AStar ≤ 0 by
      linarith [Six.sStar_lt_fifth, Six.AStar_bounds.1])
  nlinarith [Six.sStar_polynomial]

/-- `tStar > 21/50`, by its affine formula in `sStar`. -/
theorem candidate_transverse_lower : (21 : ℝ) / 50 < Six.tStar := by
  have hcoef : (1213 : ℝ) / 1000 ≤ -20 + 30 * Six.hStar := by
    linarith [Six.hStar_lower]
  have hcoef0 : 0 ≤ -20 + 30 * Six.hStar := by linarith
  have hp := mul_le_mul hcoef candidate_offset_lower.le
    (by norm_num : (0 : ℝ) ≤ 421 / 5000) hcoef0
  have hh : Six.hStar ≤ 70711 / 100000 := by linarith [Six.hStar_upper]
  dsimp [Six.tStar]
  nlinarith only [hp, hh]

/-- Rational bounds for the ratios `rStar` and `kStar`. -/
theorem candidate_ratio_bounds :
    (73 : ℝ) / 198 < rStar ∧ rStar < 117 / 317 ∧
      (115 : ℝ) / 177 < kStar ∧ kStar < 922 / 1415 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rStar, lt_div_iff₀ rStar_den_pos]
    linarith [candidate_offset_lower]
  · rw [rStar, div_lt_iff₀ rStar_den_pos]
    linarith [Six.sStar_lt_17_200]
  · rw [kStar, lt_div_iff₀ kStar_den_pos]
    linarith [candidate_offset_lower, candidate_transverse_lower]
  · rw [kStar, div_lt_iff₀ kStar_den_pos]
    linarith [Six.sStar_lt_17_200, Six.tStar_bounds.2]

/-- Bounds for the length `2 hStar mStar = √2 mStar` of the force on D. -/
theorem diagonal_scale_bounds :
    (251 : ℝ) / 200 < 2 * Six.hStar * mStar ∧
      2 * Six.hStar * mStar < 253 / 200 := by
  have hrat := candidate_ratio_bounds
  have hmlo : (31165 : ℝ) / 35046 ≤ mStar := by
    have hp := mul_le_mul
      (show (271 : ℝ) / 198 ≤ 1 + rStar by linarith [hrat.1]) hrat.2.2.1.le
      (by norm_num : (0 : ℝ) ≤ 115 / 177) one_add_rStar_pos.le
    dsimp [mStar]
    nlinarith only [hp]
  have hmhi : mStar ≤ (400148 : ℝ) / 448555 := by
    have hp := mul_le_mul
      (show 1 + rStar ≤ (434 : ℝ) / 317 by linarith [hrat.2.1]) hrat.2.2.2.le
      kStar_pos.le (by norm_num : (0 : ℝ) ≤ 434 / 317)
    dsimp [mStar]
    nlinarith only [hp]
  have hHlo : (7071 : ℝ) / 5000 ≤ 2 * Six.hStar := by linarith [Six.hStar_lower]
  have hHhi : 2 * Six.hStar ≤ (70711 : ℝ) / 50000 := by linarith [Six.hStar_upper]
  have hlo := mul_le_mul hHlo hmlo
    (by norm_num : (0 : ℝ) ≤ 31165 / 35046)
    (show 0 ≤ 2 * Six.hStar by positivity)
  have hhi := mul_le_mul hHhi hmhi mStar_pos.le
    (by norm_num : (0 : ℝ) ≤ 70711 / 50000)
  constructor <;> nlinarith only [hlo, hhi]

/-- `rhoStar > 111/100`. -/
theorem candidate_cap_radius_lower : (111 : ℝ) / 100 < rhoStar := by
  have hs : 21 / 250 < Six.sStar := by linarith [candidate_offset_lower]
  have hp := mul_nonneg (show 0 ≤ Six.sStar - 21 / 250 by linarith)
    (show 0 ≤ Six.sStar + 21 / 250 by linarith [Six.sStar_pos])
  have hq : (161 / 100 : ℝ) ^ 2 < Six.radius ^ 2 - 1 / 4 := by
    rw [Six.radius_sq]
    dsimp [Six.qStar]
    nlinarith only [hp, hs]
  have hroot := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ (161 / 100) ^ 2) hq
  rw [Real.sqrt_sq (by norm_num)] at hroot
  dsimp [rhoStar, rhoAt]
  linarith

/-- `8/5 < radius < 1689/1000`. -/
theorem candidate_radius_bounds :
    (8 : ℝ) / 5 < Six.radius ∧ Six.radius < 1689 / 1000 := by
  constructor
  · have hρ := candidate_cap_radius_lower
    have hs := sq_nonneg (rhoStar - 111 / 100)
    nlinarith [rhoStar_identity, Six.radius_sq, Six.radius_pos]
  · have hq : Six.radius ^ 2 < (142559 : ℝ) / 50000 := by
      simpa only [Six.radius_sq, Normalization.Q0] using Six.qStar_lt_Q0
    nlinarith [sq_nonneg (Six.radius - 1689 / 1000)]

/-- Bounds for the work `2 hStar mStar rhoStar` of the force on D. -/
theorem diagonal_constant_bounds :
    (139 : ℝ) / 100 < 2 * Six.hStar * mStar * rhoStar ∧
      2 * Six.hStar * mStar * rhoStar < 141 / 100 := by
  have hK := diagonal_scale_bounds
  have hρ := candidate_cap_radius_lower
  have hlo := mul_le_mul hK.1.le hρ.le
    (by norm_num : (0 : ℝ) ≤ 111 / 100)
    (show 0 ≤ 2 * Six.hStar * mStar by linarith [hK.1])
  have hhi := mul_le_mul hK.2.le rhoStar_upper.le
    (show 0 ≤ rhoStar by linarith)
    (by norm_num : (0 : ℝ) ≤ 253 / 200)
  constructor <;> nlinarith only [hlo, hhi]

end SquaresInCircles.Six.Analytic
