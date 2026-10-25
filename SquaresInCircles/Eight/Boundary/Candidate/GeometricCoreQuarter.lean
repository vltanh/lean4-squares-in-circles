module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic
public import SquaresInCircles.Common.Analysis

/-!
# Eight squares: quarter edges between core squares of opposite signs

On a quarter edge `φ = π/2 + d` from a core square with transverse sign `+1` to one with sign
`-1`, the gap `π/2 + d + arctan (b / a) + arctan (B / A)` is below `7/4`, a bound of every gap of
a cycle (`cycle_gap_lt_seven_quarters`). Since `arctan x ≥ (3/4) x` on `[0, 1]`, a core
transverse coordinate is at most `7/9` of its angle, so `b + B ≤ (7/9)(1/5 - d)`, and then no
forward axis separates the pair, on the whole frame range `|d| ≤ 7/10`
(`core_quarter_opposite_margin`, `quarter_core_opposite_excluded`). The pair tables leave these
pairs out: the word tables through `WordGeometry.original_not_core_excluded`, the affine tables
through `ExcludedArcs` (`Arithmetic/AffineCoverage.lean`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.Candidate.Geometric

/-- `arctan x ≥ (3/4) x` on `[0, 1]`: `arctan` is concave there, so it lies above its chord, of
slope `π/4 > 3/4`. -/
theorem arctan_chord {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) : (3/4:ℝ)*x ≤ Real.arctan x := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) 1) Real.arctan :=
    concave_of_deriv2 (fun y _ => Real.hasDerivAt_arctan y)
      (fun y _ => (hasDerivAt_const y (1:ℝ)).div ((hasDerivAt_pow 2 y).const_add 1)
        (by positivity))
      (fun y hy => div_nonpos_of_nonpos_of_nonneg (by norm_num; linarith [hy.1]) (by positivity))
  have h := hc.2 (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    (show 0 ≤ 1-x by linarith [hx.2]) hx.1 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.arctan_zero, Real.arctan_one] at h
  nlinarith [Real.pi_gt_three]

/-- A core transverse coordinate is at most `7/9` of its angle: `b ≤ (7/9) arctan (b / a)` when
`0 ≤ b ≤ a ≤ 7/12`. -/
theorem core_transverse_le_angle {a b : ℝ} (ha : 0 < a) (hau : a ≤ 7/12) (hb : 0 ≤ b)
    (hab : b ≤ a) : b ≤ (7/9:ℝ)*Real.arctan (b/a) := by
  have h := arctan_chord ⟨div_nonneg hb ha.le, (div_le_one ha).mpr hab⟩
  have he : (b/a)*a=b := div_mul_cancel₀ b (ne_of_gt ha)
  nlinarith [mul_le_mul_of_nonneg_right hau (div_nonneg hb ha.le)]

end SquaresInCircles.Eight.Candidate.Geometric
