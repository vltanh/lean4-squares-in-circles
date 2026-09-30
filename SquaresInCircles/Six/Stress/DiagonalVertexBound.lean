import SquaresInCircles.Six.Stress.DiagonalCapBound
import SquaresInCircles.Six.Analytic.CandidateBounds
import SquaresInCircles.Six.Analytic.DiagonalVertex

/-!
# The diagonal vertex branch, without a finite-cover certificate

The coordinates X=|(w+s)/2| and Y=|(w-s)/2| satisfy X+Y<=11/25.
The true vertex premise implies |delta|>=29/100, while the diagonal-angle
range gives |delta|<=2/7+X. These are exactly the geometric hypotheses of the
analytic vertex lemma. No enlargement to an unsupported cap branch occurs.

The scalar vertex proof and the constant bounds have certificate-free import
chains. Other imported project components are still undergoing conversion;
this theorem does not claim that the entire n=6 proof is already analytic.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

private lemma diagonal_diamond {w s d : ℝ} (hd : DiagonalDomain w s d) :
    |(w + s) / 2| + |diagonalBeta w s| ≤ 11 / 25 := by
  let a := (w + s) / 2
  let b := diagonalBeta w s
  have hw : a + b = w := by dsimp [a, b, diagonalBeta]; ring
  have hs : a - b = s := by dsimp [a, b, diagonalBeta]; ring
  change |a| + |b| ≤ 11 / 25
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]
    linarith [hd.1.2]
  · rw [abs_of_nonneg ha, abs_of_neg hb]
    linarith [hd.2.1.2]
  · rw [abs_of_neg ha, abs_of_nonneg hb]
    linarith [hd.2.1.1]
  · rw [abs_of_neg ha, abs_of_neg hb]
    linarith [hd.1.1]

private lemma diagonal_max_le_abs_sum (w s : ℝ) :
    2 * max |(w + s) / 2| |diagonalBeta w s| ≤ |w| + |s| := by
  have hs := abs_add_le w s
  have hd := abs_sub_le w s
  have hsum : w + s = 2 * ((w + s) / 2) := by ring
  have hdiff : w - s = 2 * diagonalBeta w s := by dsimp [diagonalBeta]; ring
  rw [hsum, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
  rw [hdiff, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hd
  by_cases h : |(w + s) / 2| ≤ |diagonalBeta w s|
  · rw [max_eq_right h]
    exact hd
  · rw [max_eq_left (le_of_not_ge h)]
    exact hs

/-- Strict positivity on the true vertex branch, including the branch wall. -/
theorem diagonal_vertex_remainder_positive {w s d : ℝ} (hd : DiagonalDomain w s d)
    (hv : 1 ≤ 2 * Six.radius * |Real.sin (diagonalDelta w s d)|) :
    0 < pairLine w + pairLine (-s) + diagonalVertex w s d + 2 * pairBase := by
  let a := (w + s) / 2
  let b := diagonalBeta w s
  let z := diagonalDelta w s d
  let x := |a|
  let t := |z|
  have hdiamond : x + |b| ≤ 11 / 25 := diagonal_diamond hd
  have hR := Analytic.candidate_radius_bounds
  have hK := Analytic.diagonal_scale_bounds
  have hsin := abs_sin_le_abs_value z
  have hprod := mul_le_mul hR.2.le hsin (abs_nonneg (Real.sin z))
    (by norm_num : (0 : ℝ) ≤ 1689 / 1000)
  have htlo : 29 / 100 ≤ t := by
    change 1 ≤ 2 * Six.radius * |Real.sin z| at hv
    dsimp [t]
    nlinarith only [hv, hprod]
  have htriangle := abs_sub_le (d - Real.pi / 4) a
  have hsign : d - Real.pi / 4 ≤ 0 := by linarith [hd.2.2.2]
  rw [abs_of_nonpos hsign] at htriangle
  have hpi : Real.pi < (22 : ℝ) / 7 := by linarith [Real.pi_lt_d4]
  have hthi : t ≤ 2 / 7 + x := by
    change |d - Real.pi / 4 - a| ≤ 2 / 7 + |a|
    linarith [hd.2.2.1]
  have hp := Analytic.diagonal_vertex_expression_positive
    (K := diagonalK) (R := Six.radius) (rho := rhoStar)
    (x := x) (b := b) (t := t)
    (by dsimp [diagonalK]; linarith [hK.1])
    (by simpa only [diagonalK] using hK.2.le)
    hR.1.le hR.2.le Analytic.candidate_cap_radius_lower.le
    (abs_nonneg a) hdiamond ⟨htlo, hthi⟩
  have hzpi : |z| ≤ Real.pi := by
    have hz := (diagonal_parameters hd).2.1
    change |z| ≤ 71 / 100 at hz
    linarith [Real.pi_gt_d2]
  dsimp [t] at hp
  rw [Real.cos_abs, sin_abs_angle hzpi] at hp
  have hsum : 2 * max x |b| ≤ |w| + |s| := diagonal_max_le_abs_sum w s
  have hid : pairLine w + pairLine (-s) + diagonalVertex w s d + 2 * pairBase =
      (47 / 200) * (|w| + |s|) - (99 / 100) * b +
      diagonalK * ((3 * Real.cos b - Real.sin b) * Real.cos z / 2 +
        (Real.cos b - Real.sin b) * |Real.sin z| / 2 -
        Six.radius * (Real.cos b - Real.sin b) + rhoStar - 1) := by
    rw [pairLine_sum, pairBase_eq_diagonal_scale]
    dsimp [diagonalVertex, b, z, diagonalBeta]
    ring
  rw [hid]
  nlinarith only [hp, hsum]

end SquaresInCircles.Six.Stress
