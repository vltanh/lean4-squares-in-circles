import SquaresInCircles.Six.Normalization.Constants
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The cap depth

A square in the disk of squared radius `Q0` that lies beyond a line, whose
normal makes an angle `t ∈ [0, π/4]` with an axis of the square, keeps the line
within `capDepth t` of the centre. The depth has two branches:
`(ρ0 - 1/2) cos t - (1/2) sin t`, with the far corner of the square at the point
`(ρ0 + 1/2, 1/2)` of the circle, and `R0 - cos t - sin t`, with the far corner on
the circle in the direction of the normal. They switch at the angle
`arcsin (1/(2R0))`, whose sine is `1/(2R0)` and cosine `(ρ0 + 1/2)/R0`.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

def capSwitch : ℝ := Real.arcsin (1 / (2 * R0))

def capFirst (t : ℝ) : ℝ :=
  (rho0 - 1 / 2) * Real.cos t - (1 / 2) * Real.sin t

def capSecond (t : ℝ) : ℝ := R0 - Real.cos t - Real.sin t

def capDepth (t : ℝ) : ℝ :=
  if t ≤ capSwitch then capFirst t else capSecond t

lemma R0_pos : 0 < R0 := Real.sqrt_pos.mpr Q0_pos

lemma R0_gt_one : 1 < R0 := by
  have hs : Real.sqrt (1 : ℝ) < Real.sqrt Q0 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num [Q0])
  simpa only [Real.sqrt_one, R0] using hs

lemma switch_sine_bounds : 0 < 1 / (2 * R0) ∧ 1 / (2 * R0) < 1 := by
  have hp : 0 < 2 * R0 := by linarith [R0_pos]
  exact ⟨div_pos (by norm_num) hp,
    (div_lt_one hp).mpr (by linarith [R0_gt_one])⟩

lemma capSwitch_nonneg : 0 ≤ capSwitch :=
  Real.arcsin_nonneg.mpr switch_sine_bounds.1.le

lemma sin_capSwitch : Real.sin capSwitch = 1 / (2 * R0) := by
  exact Real.sin_arcsin (by linarith [switch_sine_bounds.1]) switch_sine_bounds.2.le

lemma cos_capSwitch : Real.cos capSwitch = (rho0 + 1 / 2) / R0 := by
  have hn : R0 ≠ 0 := ne_of_gt R0_pos
  have hid : 1 - (1 / (2 * R0)) ^ 2 = ((rho0 + 1 / 2) / R0) ^ 2 := by
    field_simp [hn]
    nlinarith [R0_sq, rho0_identity]
  rw [capSwitch, Real.cos_arcsin, hid, Real.sqrt_sq]
  exact div_nonneg (by linarith [rho0_gt_one]) R0_pos.le

end SquaresInCircles.Six.Normalization
