import SquaresInCircles.Six.Normalization.Constants
import SquaresInCircles.Seven.Labels

/-!
# Bounds for the chart of an exterior square

A sorted chart `(a, u)`, `1/2 ≤ a` and `0 ≤ u ≤ a`, of a square in the disk of
squared radius `Q0` has `(a + 1/2)² + (u + 1/2)² ≤ Q0`, so `a ≤ ρ0`. If the
closed square also avoids the open disk of radius `coreRadius` about the
origin, then `u < 1/2`, since otherwise `a + u ≥ 1 + coreRadius` and the far
corner would leave the disk. So its nearest point to the origin is on its near
edge, which gives `a ≥ aMin`, and then the far corner gives `u ≤ U0`.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- A sorted chart `(a, u)` whose far corner lies in the disk of squared radius
`Q0`. -/
structure ContainedChart (a u : ℝ) : Prop where
  half_le : 1 / 2 ≤ a
  u_nonneg : 0 ≤ u
  u_le : u ≤ a
  containment : (a + 1 / 2) ^ 2 + (u + 1 / 2) ^ 2 ≤ Q0

/-- The closed square avoids the open disk of radius `coreRadius` about the
origin: for `a ≥ 1/2` and `u ≥ 0`, the right side is the squared distance of its
nearest point. -/
def AvoidsCore (a u : ℝ) : Prop :=
  coreRadius ^ 2 ≤ (a - 1 / 2) ^ 2 + (max (u - 1 / 2) 0) ^ 2

namespace ContainedChart
variable {a u : ℝ} (h : ContainedChart a u)
include h

lemma seven_admissible : Seven.Admissible a u where
  u_nonneg := h.u_nonneg
  u_le := h.u_le
  half_le := h.half_le
  phi_le := by
    change (a + 1 / 2) ^ 2 + (u + 1 / 2) ^ 2 ≤ 13 / 4
    exact h.containment.trans Q0_lt_thirteen_fourths.le

lemma a_le_rho0 : a ≤ rho0 := by
  have hs : (a + 1 / 2) ^ 2 ≤ Q0 - 1 / 4 := by
    nlinarith [h.containment, h.u_nonneg, sq_nonneg u]
  have hr := Real.le_sqrt_of_sq_le hs
  dsimp [rho0]
  linarith

/-- A square that avoids the core has `u < 1/2`: its nearest point is not a
corner. -/
lemma u_lt_half (hc : AvoidsCore a u) : u < 1 / 2 := by
  by_contra! hu
  have hx : 0 ≤ a - 1 / 2 := by linarith [h.half_le]
  have hy : 0 ≤ u - 1 / 2 := by linarith
  have hd : coreRadius ^ 2 ≤ (a - 1 / 2) ^ 2 + (u - 1 / 2) ^ 2 := by
    simpa only [AvoidsCore, max_eq_left hy] using hc
  have hsum : coreRadius ≤ a + u - 1 := by
    by_contra! hs
    have hp := mul_pos (sub_pos.mpr hs)
      (show 0 < coreRadius + (a + u - 1) by linarith [coreRadius_pos])
    nlinarith [mul_nonneg hx hy]
  have ht := h.containment
  norm_num [Q0] at ht
  nlinarith [coreRadius_gt_77_200, sq_nonneg (coreRadius - 77 / 200)]

/-- A square that avoids the core has `a ≥ aMin`: its nearest point is on its
near edge. -/
lemma aMin_le (hc : AvoidsCore a u) : aMin ≤ a := by
  have hu := h.u_lt_half hc
  have hd : coreRadius ^ 2 ≤ (a - 1 / 2) ^ 2 := by
    simpa only [AvoidsCore, max_eq_right (by linarith : u - 1 / 2 ≤ 0),
      zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using hc
  have hr : coreRadius ≤ a - 1 / 2 := by
    by_contra! hs
    have hp := mul_pos (sub_pos.mpr hs)
      (show 0 < coreRadius + (a - 1 / 2) by linarith [coreRadius_pos, h.half_le])
    nlinarith
  rw [aMin_eq_coreRadius_add_half]
  linarith

/-- A square that avoids the core has `u ≤ U0`, by its far corner at
`a ≥ aMin`. -/
lemma u_le_U0 (hc : AvoidsCore a u) : u ≤ U0 := by
  have ha := h.aMin_le hc
  have hp := mul_nonneg (sub_nonneg.mpr ha)
    (show 0 ≤ a + aMin + 1 by linarith [h.half_le, aMin_gt_177_200])
  dsimp [aMin] at hp
  have hs : (u + 1 / 2) ^ 2 ≤ Q0 - (5 / 2 - rho0) ^ 2 := by
    nlinarith [h.containment]
  have hr := Real.le_sqrt_of_sq_le hs
  dsimp [U0]
  linarith

/-- Rational bounds for a square that avoids the core: `177/200 < a < 223/200`
and `u < 117/250`. -/
lemma bounds (hc : AvoidsCore a u) :
    177 / 200 < a ∧ a < 223 / 200 ∧ u < 117 / 250 :=
  ⟨lt_of_lt_of_le aMin_gt_177_200 (h.aMin_le hc),
    lt_of_le_of_lt h.a_le_rho0 rho0_lt_223_200,
    lt_of_le_of_lt (h.u_le_U0 hc) U0_lt_117_250⟩

end ContainedChart
end SquaresInCircles.Six.Normalization
