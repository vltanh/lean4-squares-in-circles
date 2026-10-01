import SquaresInCircles.Six.Analytic.VertexMinorant

/-!
# An analytic replacement for the diagonal vertex certificate

The constants below are deliberately coarse rational bounds. Their candidate
instances are proved separately from the exact defining algebra.

Write A = (3 cos t + sin t)/2-R and B = R-(cos t+sin t)/2.
The unit circle gives A <= 0 and K B >= 17/16. Replacing beta by -|beta|
can only decrease the lower estimate, by sin y >= (23/24)y for 0 <= y <= 1/2.
After division by K, the remaining expression dominates vertexMinorant.
VertexMinorant is positive by concavity and two quartic chord arguments.

There is no interval evaluator, search, or certificate import in this module.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

private lemma sin_lower_twenty_three_twenty_four {y : ℝ}
    (hy : 0 ≤ y ∧ y ≤ 1 / 2) : (23 / 24) * y ≤ Real.sin y := by
  have hsq := mul_nonneg (sub_nonneg.mpr hy.2)
    (show 0 ≤ 1 / 2 + y by linarith [hy.1])
  have hfactor : 0 ≤ 1 / 4 - y ^ 2 := by nlinarith
  have hcube := mul_nonneg hy.1 hfactor
  have hsin := Real.sin_ge_sub_cube hy.1
  nlinarith only [hcube, hsin]

private lemma weighted_width_le (t : ℝ) :
    (3 / 2) * Real.cos t + (1 / 2) * Real.sin t ≤ 8 / 5 := by
  have hunit := Real.sin_sq_add_cos_sq t
  have hperp := sq_nonneg (Real.cos t - 3 * Real.sin t)
  by_contra! h
  have hp := mul_pos
    (show 0 < 3 * Real.cos t + Real.sin t - 16 / 5 by linarith)
    (show 0 < 3 * Real.cos t + Real.sin t + 16 / 5 by linarith)
  nlinarith only [hunit, hperp, hp]

private lemma width_le_three_halves (t : ℝ) :
    Real.cos t + Real.sin t ≤ 3 / 2 := by
  have hunit := Real.sin_sq_add_cos_sq t
  have hperp := sq_nonneg (Real.cos t - Real.sin t)
  by_contra! h
  have hp := mul_pos (sub_pos.mpr h)
    (show 0 < Real.cos t + Real.sin t + 3 / 2 by linarith)
  nlinarith only [hunit, hperp, hp]

/-- The trigonometric vertex expression on the entire diamond/angle domain.
The hypotheses are simple scalar bounds, not a successful-check premise. -/
theorem diagonal_vertex_expression_positive {K R rho x b t : ℝ}
    (hKlo : 5 / 4 ≤ K) (hKhi : K ≤ 253 / 200)
    (hRlo : 8 / 5 ≤ R) (hRhi : R ≤ 1689 / 1000)
    (hrho : 111 / 100 ≤ rho)
    (hx : 0 ≤ x) (hdiamond : x + |b| ≤ 11 / 25)
    (ht : 29 / 100 ≤ t ∧ t ≤ 2 / 7 + x) :
    0 < (47 / 100) * max x |b| - (99 / 100) * b +
      K * ((3 * Real.cos b - Real.sin b) * Real.cos t / 2 +
        (Real.cos b - Real.sin b) * Real.sin t / 2 -
        R * (Real.cos b - Real.sin b) + rho - 1) := by
  let A := (3 / 2) * Real.cos t + (1 / 2) * Real.sin t - R
  let B := R - (Real.cos t + Real.sin t) / 2
  let y := |b|
  let M := max x y
  have hK0 : 0 < K := by linarith
  have hy0 : 0 ≤ y := abs_nonneg b
  have hy1 : y ≤ 1 / 2 := by dsimp [y]; linarith
  have hM0 : 0 ≤ M := hx.trans (le_max_left x y)
  have hA : A ≤ 0 := by
    dsimp [A]
    linarith [weighted_width_le t]
  have hB : 17 / 20 ≤ B := by
    dsimp [B]
    linarith [width_le_three_halves t]
  have hKB : 17 / 16 ≤ K * B := by
    have hp := mul_le_mul hKlo hB (by norm_num : (0 : ℝ) ≤ 17 / 20) hK0.le
    nlinarith only [hp]
  have hKB0 : 0 ≤ K * B := by linarith
  have hcos : A ≤ A * Real.cos b := by
    simpa only [mul_one] using mul_le_mul_of_nonpos_left (Real.cos_le_one b) hA
  have hKcos := mul_le_mul_of_nonneg_left hcos hK0.le
  have hsin : (99 / 100) * y - K * B * y ≤
      -(99 / 100) * b + K * B * Real.sin b := by
    by_cases hb : b ≤ 0
    · have hs := Real.sin_le (show 0 ≤ -b by linarith)
      rw [Real.sin_neg] at hs
      have hp := mul_le_mul_of_nonneg_left
        (show b ≤ Real.sin b by linarith) hKB0
      dsimp [y]
      rw [abs_of_nonpos hb]
      nlinarith only [hp]
    · have hb0 : 0 ≤ b := (lt_of_not_ge hb).le
      have hb1 : b ≤ 1 / 2 := by simpa [y, abs_of_nonneg hb0] using hy1
      have hs := sin_lower_twenty_three_twenty_four ⟨hb0, hb1⟩
      have hsum : (47 / 24) * b ≤ Real.sin b + b := by linarith
      have hp := mul_le_mul hKB hsum
        (show 0 ≤ (47 / 24) * b by positivity) hKB0
      dsimp [y]
      rw [abs_of_nonneg hb0]
      nlinarith only [hp, hb0]
  have htrig :
      (47 / 100) * M + (99 / 100) * y + K * (A - B * y + rho - 1) ≤
      (47 / 100) * M - (99 / 100) * b +
        K * (A * Real.cos b + B * Real.sin b + rho - 1) := by
    nlinarith only [hKcos, hsin]
  have hM := mul_nonneg
    (show 0 ≤ 47 / 100 - (37 / 100) * K by linarith) hM0
  have hY := mul_nonneg
    (show 0 ≤ 99 / 100 - (39 / 50) * K by linarith) hy0
  have hRad := mul_nonneg hK0.le
    (mul_nonneg (sub_nonneg.mpr hRhi) (show 0 ≤ 1 + y by linarith))
  have hRho := mul_nonneg hK0.le (sub_nonneg.mpr hrho)
  have hid :
      (47 / 100) * M + (99 / 100) * y + K * (A - B * y + rho - 1) -
        K * vertexMinorant x y t =
      (47 / 100 - (37 / 100) * K) * M +
      (99 / 100 - (39 / 50) * K) * y +
      K * (1689 / 1000 - R) * (1 + y) + K * (rho - 111 / 100) := by
    dsimp [A, B, M, vertexMinorant]
    ring
  have hminorant : K * vertexMinorant x y t ≤
      (47 / 100) * M + (99 / 100) * y + K * (A - B * y + rho - 1) := by
    nlinarith only [hid, hM, hY, hRad, hRho]
  have hpositive := mul_pos hK0 (vertexMinorant_positive hx hy0 hdiamond ht)
  have hresult := hpositive.trans_le (hminorant.trans htrig)
  change 0 < (47 / 100) * M - (99 / 100) * b + _
  have hidentity :
      (3 * Real.cos b - Real.sin b) * Real.cos t / 2 +
        (Real.cos b - Real.sin b) * Real.sin t / 2 -
        R * (Real.cos b - Real.sin b) + rho - 1 =
      A * Real.cos b + B * Real.sin b + rho - 1 := by
    dsimp [A, B]
    ring
  rw [hidentity]
  exact hresult

end SquaresInCircles.Six.Analytic
