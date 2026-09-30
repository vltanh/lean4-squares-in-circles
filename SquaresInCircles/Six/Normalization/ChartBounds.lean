import SquaresInCircles.Six.Normalization.Constants
import SquaresInCircles.Seven.Labels

/-!
# The scalar part of normalization Lemma B

These are implications from an explicit strong-core exclusion, not a proof
of Proposition A. The geometric bridge must establish `AvoidsCore` from
interior-disjointness and the strong central box before using these results.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- A sorted exterior chart satisfying the rational containment ceiling. -/
structure ContainedChart (a u : ℝ) : Prop where
  half_le : 1 / 2 ≤ a
  u_nonneg : 0 ≤ u
  u_le : u ≤ a
  containment : (a + 1 / 2) ^ 2 + (u + 1 / 2) ^ 2 ≤ Q0

/-- The nearest point of the closed exterior square avoids the open core disk.
For `a ≥ 1/2` and `u ≥ 0`, its squared distance is the right-hand side. -/
def AvoidsCore (a u : ℝ) : Prop :=
  coreRadius ^ 2 ≤ (a - 1 / 2) ^ 2 + (max (u - 1 / 2) 0) ^ 2

namespace ContainedChart
variable {a u : ℝ} (h : ContainedChart a u)

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

/-- B1: the corner-nearest case is incompatible with containment and the core. -/
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

/-- B2: after B1 the nearest point is the foot on the near edge. -/
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

/-- B3: the uniform transverse bound at the left radial endpoint. -/
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

/-- The strict bounds N17 follow from the stronger closed bounds. -/
lemma bounds (hc : AvoidsCore a u) :
    177 / 200 < a ∧ a < 223 / 200 ∧ u < 117 / 250 :=
  ⟨lt_of_lt_of_le aMin_gt_177_200 (h.aMin_le hc),
    lt_of_le_of_lt h.a_le_rho0 rho0_lt_223_200,
    lt_of_le_of_lt (h.u_le_U0 hc) U0_lt_117_250⟩

/-- A rational supporting-line estimate; no trigonometric enclosure is needed. -/
lemma axial_linear_bound (hc : AvoidsCore a u) : 9 * a + 11 * u < 131 / 10 := by
  have ha : 177 / 200 < a := (h.bounds hc).1
  have ha' : a < 223 / 200 := (h.bounds hc).2.1
  by_contra! ht
  let X : ℝ := a + 1 / 2
  let Y : ℝ := u + 1 / 2
  let L : ℝ := (231 / 10 - 9 * X) / 11
  have hX : 277 / 200 ≤ X := by dsimp [X]; linarith
  have hY : 0 ≤ Y := by dsimp [Y]; linarith [h.u_nonneg]
  have hL : 0 ≤ L := by dsimp [L, X]; linarith
  have hLY : L ≤ Y := by dsimp [L, X, Y]; linarith
  have hp := mul_nonneg (sub_nonneg.mpr hLY) (add_nonneg hY hL)
  have hinc := mul_nonneg
    (show 0 ≤ 200 * X - 277 by linarith)
    (show 0 ≤ 20200 * X - 13603 by linarith)
  have hid : X ^ 2 + L ^ 2 -
      ((277 / 200 : ℝ) ^ 2 + ((231 / 10 - 9 * (277 / 200 : ℝ)) / 11) ^ 2) =
      (200 * X - 277) * (20200 * X - 13603) / 2420000 := by
    dsimp [L]
    ring
  have hbad : Q0 <
      (277 / 200 : ℝ) ^ 2 + ((231 / 10 - 9 * (277 / 200 : ℝ)) / 11) ^ 2 := by
    norm_num [Q0]
  have hct : X ^ 2 + Y ^ 2 ≤ Q0 := h.containment
  nlinarith

/-- B5: strict dominance of the axial branch of the actual Seven label. -/
lemma label_eq_axial (hc : AvoidsCore a u) : Seven.label a u = 5 * u / 4 := by
  have hs : 9 * a + 11 * u < 2 * Real.pi + 7 := by
    linarith [h.axial_linear_bound hc, Real.pi_gt_d2]
  have hside : Seven.axial u ≤ Seven.side a u := by
    dsimp [Seven.axial, Seven.side]
    linarith
  have hcap : Seven.axial u ≤ Real.pi / 4 := by
    dsimp [Seven.axial]
    linarith [(h.bounds hc).2.2, Real.pi_gt_d2]
  rw [Seven.label, min_eq_left hside, min_eq_left hcap]
  rfl

end ContainedChart
end SquaresInCircles.Six.Normalization
