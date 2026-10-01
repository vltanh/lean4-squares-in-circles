import SquaresInCircles.Common.Basic
import SquaresInCircles.Six.Normalization.Constants

/-!
# The constants of the six-square model

Rational bounds and algebraic identities for the constants of the model:
`h = √2/2`, the coefficients `A` and `B` of the quadratic `p(s) = s² - A s + B`,
its smaller root `s*`, and `t*`, `d*` and `q*`. The far corners of E and W and
the far vertices of D lie at squared distance `q*` from the centre: for E by
the definition of `q*`, for W and D by combinations of `p(s*) = 0` and
`h² = 1/2`. The squared radius `q*` lies below the ceiling `Q0` of the
normalization.
-/

noncomputable section
namespace SquaresInCircles.Six

lemma hStar_pos : 0 < hStar := halfDiagonal_pos

lemma hStar_sq : hStar ^ 2 = 1 / 2 := halfDiagonal_sq

lemma hStar_lower : (707106781 : ℝ) / 1000000000 < hStar := by
  have hs : Real.sqrt ((1414213562 / 1000000000 : ℝ) ^ 2) < Real.sqrt 2 :=
    Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  rw [Real.sqrt_sq (by norm_num)] at hs
  dsimp [hStar]
  linarith

lemma hStar_upper : hStar < (707106782 : ℝ) / 1000000000 := by
  have hs : Real.sqrt 2 < Real.sqrt ((1414213564 / 1000000000 : ℝ) ^ 2) :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [Real.sqrt_sq (by norm_num)] at hs
  dsimp [hStar]
  linarith

lemma AStar_bounds : 10 < AStar ∧ AStar < 11 := by
  dsimp [AStar]
  constructor <;> linarith [hStar_lower, hStar_upper]

lemma BStar_bounds : 4 / 5 < BStar ∧ BStar < 1 := by
  dsimp [BStar]
  constructor <;> linarith [hStar_lower, hStar_upper]

lemma discriminant_pos : 0 < discriminant := by
  dsimp [discriminant]
  nlinarith [AStar_bounds.1, BStar_bounds.2, sq_nonneg (AStar - 10)]

lemma candidate_den_pos : 0 < AStar + Real.sqrt discriminant := by
  linarith [AStar_bounds.1, Real.sqrt_nonneg discriminant]

lemma sStar_pos : 0 < sStar := by
  dsimp [sStar]
  exact div_pos (by linarith [BStar_bounds.1]) candidate_den_pos

lemma sStar_lt_fifth : sStar < 1 / 5 := by
  rw [sStar, div_lt_iff₀ candidate_den_pos]
  linarith [BStar_bounds.2, AStar_bounds.1, Real.sqrt_nonneg discriminant]

/-- `s*` is a root of `s² - A s + B`. -/
lemma sStar_polynomial : sStar ^ 2 - AStar * sStar + BStar = 0 := by
  have hd : AStar + Real.sqrt discriminant ≠ 0 := ne_of_gt candidate_den_pos
  have hs : sStar * (AStar + Real.sqrt discriminant) = 2 * BStar := by
    rw [sStar]
    exact div_mul_cancel₀ _ hd
  have hr := Real.sq_sqrt discriminant_pos.le
  have hp : (sStar ^ 2 - AStar * sStar + BStar) *
      (AStar + Real.sqrt discriminant) ^ 2 = 0 := by
    calc
      _ = (sStar * (AStar + Real.sqrt discriminant)) ^ 2 -
          AStar * (sStar * (AStar + Real.sqrt discriminant)) *
            (AStar + Real.sqrt discriminant) +
          BStar * (AStar + Real.sqrt discriminant) ^ 2 := by ring
      _ = BStar * ((Real.sqrt discriminant) ^ 2 - discriminant) := by
        rw [hs]
        dsimp [discriminant]
        ring
      _ = 0 := by rw [hr]; ring
  exact (mul_eq_zero.mp hp).resolve_right (pow_ne_zero 2 hd)

lemma sStar_bounds : 2 / 25 < sStar ∧ sStar < 842457 / 10000000 := by
  have pl : 0 < (2 / 25 : ℝ) ^ 2 - AStar * (2 / 25) + BStar := by
    dsimp [AStar, BStar]
    linarith [hStar_lower, hStar_upper]
  have pu : (842457 / 10000000 : ℝ) ^ 2 -
      AStar * (842457 / 10000000) + BStar < 0 := by
    dsimp [AStar, BStar]
    linarith [hStar_lower, hStar_upper]
  constructor
  · by_contra! hl
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ 2 / 25 - sStar by linarith)
      (show 2 / 25 + sStar - AStar ≤ 0 by linarith [sStar_lt_fifth, AStar_bounds.1])
    nlinarith [sStar_polynomial]
  · by_contra! hu
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ sStar - 842457 / 10000000 by linarith)
      (show sStar + 842457 / 10000000 - AStar ≤ 0 by
        linarith [sStar_lt_fifth, AStar_bounds.1])
    nlinarith [sStar_polynomial]

lemma sStar_lt_17_200 : sStar < 17 / 200 := by linarith [sStar_bounds.2]

lemma tStar_bounds : 2 / 5 < tStar ∧ tStar < 211 / 500 := by
  have hc : 0 ≤ -20 + 30 * hStar := by linarith [hStar_lower]
  have hl := mul_le_mul
    (show (6 : ℝ) / 5 ≤ -20 + 30 * hStar by linarith [hStar_lower])
    sStar_bounds.1.le (by norm_num : (0 : ℝ) ≤ 2 / 25) hc
  have hu := mul_le_mul
    (show -20 + 30 * hStar ≤ (152 : ℝ) / 125 by linarith [hStar_upper])
    sStar_lt_17_200.le sStar_pos.le (by norm_num : (0 : ℝ) ≤ 152 / 125)
  dsimp [tStar]
  constructor <;> nlinarith [hStar_lower, hStar_upper]

lemma dStar_pos : 0 < dStar := by
  dsimp [dStar]
  linarith [hStar_lower, tStar_bounds.2]

lemma central_diagonal_clearance : 43 / 50 < sStar + dStar := by
  dsimp [dStar]
  linarith [sStar_bounds.1, hStar_lower, tStar_bounds.2]

lemma qStar_pos : 0 < qStar := by
  dsimp [qStar]
  nlinarith [sStar_pos, sq_nonneg sStar]

/-- The squared optimal radius lies below the ceiling `Q0` of the
normalization. -/
lemma qStar_lt_Q0 : qStar < Normalization.Q0 := by
  have hm := mul_nonneg
    (show 0 ≤ 842457 / 10000000 - sStar by linarith [sStar_bounds.2])
    (show 0 ≤ 2 * (842457 / 10000000 + sStar) + 4 by linarith [sStar_pos])
  dsimp [qStar, Normalization.Q0]
  nlinarith

lemma radius_pos : 0 < radius := Real.sqrt_pos.mpr qStar_pos

lemma radius_sq : radius ^ 2 = qStar := Real.sq_sqrt qStar_pos.le

lemma east_radius_identity :
    qStar = (sStar + 1 / 2) ^ 2 + (sStar + 3 / 2) ^ 2 := by
  dsimp [qStar]
  ring

lemma west_radius_identity :
    qStar = (3 / 2 - sStar) ^ 2 + (tStar + 1 / 2) ^ 2 := by
  have hp := sStar_polynomial
  have hh := hStar_sq
  dsimp [qStar, tStar, AStar, BStar] at *
  linear_combination (1200 * hStar - 849) * hp -
    ((320400 * sStar ^ 2 - 3200120 * sStar + 266409) / 356) * hh

lemma diagonal_radius_identity :
    qStar = 2 * dStar ^ 2 + 2 * hStar * dStar + 1 / 2 := by
  have hp := sStar_polynomial
  have hh := hStar_sq
  dsimp [qStar, dStar, tStar, AStar, BStar] at *
  linear_combination (2400 * hStar - 1698) * hp -
    ((320400 * sStar ^ 2 - 3232160 * sStar + 271927) / 178) * hh

end SquaresInCircles.Six
