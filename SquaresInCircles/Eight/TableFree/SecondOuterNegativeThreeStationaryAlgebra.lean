import Mathlib

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree
open Set

theorem stationary_radius_curvature {k p t : ℝ}
    (hk : 0 < k) (hku : k < (116 / 125 : ℝ))
    (hp : p < -(221 / 1000 : ℝ)) (ht : t < -(371 / 500 : ℝ)) :
    -1 + t / k ^ 3 - 3 * p ^ 2 / k ^ 4 < -(2 : ℝ) := by
  have hk3 : 0 < k ^ 3 := pow_pos hk 3
  have hk4 : 0 < k ^ 4 := pow_pos hk 4
  have hk3u : k ^ 3 ≤ (116 / 125 : ℝ) ^ 3 := by
    gcongr
    exact hku.le
  have hk4u : k ^ 4 ≤ (116 / 125 : ℝ) ^ 4 := by
    gcongr
    exact hku.le
  have htq : t / k ^ 3 < -(9 / 10 : ℝ) := by
    apply (div_lt_iff₀ hk3).2
    nlinarith
  have hpsq : (221 / 1000 : ℝ) ^ 2 < p ^ 2 := by
    nlinarith [sq_nonneg (p + (221 / 1000 : ℝ))]
  have hpq : (19 / 100 : ℝ) < 3 * p ^ 2 / k ^ 4 := by
    apply (lt_div_iff₀ hk4).2
    nlinarith
  linarith

theorem stationary_projection_lower {u w z v : ℝ}
    (hu : u ∈ Ioo (219 / 125 : ℝ) (353 / 200 : ℝ))
    (hw : w ∈ Icc (1 / 2 : ℝ) (23 / 25 : ℝ))
    (hz : z ∈ Icc (-(1 / 2 : ℝ)) (-(2 / 5 : ℝ)))
    (hv : (1077 / 1000 : ℝ) < v) :
    (687 / 1000 : ℝ) <
      ((9789 / 2500 : ℝ) - u) /
          (u * ((9789 / 2500 : ℝ) + 1 - 2 * u)) +
        (w / u) * z / (((9789 / 2500 : ℝ) + 1 - 2 * u) * v) := by
  let q : ℝ := (9789 / 2500 : ℝ) + 1 - 2 * u
  have hu0 : 0 < u := by linarith [hu.1]
  have hq : q ∈ Ioo (866 / 625 : ℝ) (3529 / 2500 : ℝ) := by
    dsimp [q]
    constructor <;> linarith [hu.1, hu.2]
  have hq0 : 0 < q := by linarith [hq.1]
  have hv0 : 0 < v := by linarith
  have huq : u * q ≤ (353 / 200 : ℝ) * (3529 / 2500 : ℝ) :=
    mul_le_mul hu.2.le hq.2.le hq0.le (by norm_num)
  have hfirst : (863 / 1000 : ℝ) < ((9789 / 2500 : ℝ) - u) / (u * q) := by
    apply (lt_div_iff₀ (mul_pos hu0 hq0)).2
    nlinarith [hu.2]
  have hr0 : 0 ≤ w / u := div_nonneg (by linarith [hw.1]) hu0.le
  have hru : w / u < (115 / 219 : ℝ) := by
    apply (div_lt_iff₀ hu0).2
    nlinarith [hu.1, hw.2]
  have hrz : -(115 / 438 : ℝ) ≤ (w / u) * z := by
    have hmul := mul_le_mul_of_nonneg_left hz.1 hr0
    nlinarith
  have hqv : (866 / 625 : ℝ) * (1077 / 1000 : ℝ) ≤ q * v :=
    mul_le_mul hq.1.le hv.le (by norm_num) hq0.le
  have hsecond : -(22 / 125 : ℝ) < (w / u) * z / (q * v) := by
    apply (lt_div_iff₀ (mul_pos hq0 hv0)).2
    nlinarith
  change (687 / 1000 : ℝ) <
    ((9789 / 2500 : ℝ) - u) / (u * q) + (w / u) * z / (q * v)
  linarith

theorem inverse_factor_lower {u : ℝ}
    (hu : 0 < u) (hq : 0 < (9789 / 2500 : ℝ) + 1 - 2 * u) :
    (4 / 5 : ℝ) <
      ((9789 / 2500 : ℝ) - u) /
        (u * ((9789 / 2500 : ℝ) + 1 - 2 * u)) := by
  apply (lt_div_iff₀ (mul_pos hu hq)).2
  nlinarith [sq_nonneg (u - (7707 / 5000 : ℝ))]

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree
