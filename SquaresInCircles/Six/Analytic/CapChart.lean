import SquaresInCircles.Six.Normalization.CentralSAT
import SquaresInCircles.Six.Construction

/-!
# A square in a deep cap

Let a square at the phase `t`, `|t| ≤ π/4`, with chart `(a, b)` and
`(|a| + 1/2)² + (|b| + 1/2)² ≤ Q0`, have its centre at least
`(|cos t| + |sin t|)/2` to the right of the line `x = h`, so that it lies in
the half-plane `x ≥ h`, where `h ≥ coreRadius`. Then `|t| < 2/5`, `|b| < 1/2`,
`|b| < a`, `h + 1/2 ≤ a ≤ ρ0` and `|b| ≤ U0`; a negative `t` is reduced to a
positive one by changing the signs of `t` and `b`. In particular such a square
with a sorted chart does not lie in the half-plane `y ≥ h` or `y ≤ -h`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma contained_from_corner {a b t : ℝ}
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2 ≤ Q0) :
    ∀ p, closedSquare (orientedSquare t a b) p → inDisk (0,0) R0 p := by
  intro p hp
  apply Six.inDisk_of_phi_le _ hp
  simpa only [orientedSquare_alpha,orientedSquare_beta,phi,R0_sq] using hbox

lemma cap_from_margin {a b t h : ℝ}
    (hm : h+angularWidth t ≤ centerX t a b) :
    ∀ p, closedSquare (orientedSquare t a b) p → h ≤ p.1 := by
  intro p hp
  have hx := (closed_center_coordinate_bounds hp).1.1
  linarith

/-- The chart bounds of a square in the deep cap `x ≥ h`, for either sign of
`t`. -/
theorem signed_cap_bounds {a b t h : ℝ}
    (ht : |t| ≤ Real.pi/4) (hh : coreRadius ≤ h)
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2 ≤ Q0)
    (hm : h+angularWidth t ≤ centerX t a b) :
    |t| < 2/5 ∧ |b| < a ∧ h+1/2 ≤ a ∧ a ≤ rho0 ∧ |b| ≤ U0 ∧ |b| < 1/2 := by
  by_cases ht0 : 0 ≤ t
  · have h := deep_cap_chart_bounds ht0 ((le_abs_self t).trans ht) hh
      (contained_from_corner hbox) (cap_from_margin hm)
    simpa only [abs_of_nonneg ht0] using h
  · have hbox' : (|a|+1/2)^2+(|-b|+1/2)^2 ≤ Q0 := by
      simpa only [abs_neg] using hbox
    have hm' : h+angularWidth (-t) ≤ centerX (-t) a (-b) := by
      simpa [angularWidth,centerX,Real.cos_neg,Real.sin_neg,abs_neg] using hm
    have h := deep_cap_chart_bounds (show 0 ≤ -t by linarith)
      (show -t ≤ Real.pi/4 by simpa only [abs_of_neg (lt_of_not_ge ht0)] using ht)
      hh (contained_from_corner hbox') (cap_from_margin hm')
    simpa only [abs_of_neg (lt_of_not_ge ht0),abs_neg] using h

/-- A square at the phase `t`, `|t| ≤ π/4`, with a sorted chart does not lie in
the deep cap `y ≥ h`, `h ≥ coreRadius`: that would need `a < |b|`. -/
theorem transverse_cap_impossible {a b t h : ℝ} (hc : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hh : coreRadius ≤ h)
    (hm : h+angularWidth t ≤ a*Real.sin t+b*Real.cos t) : False := by
  have ha : 0 ≤ a := by linarith [hc.half_le]
  have hbox : (|b|+1/2)^2+(|-a|+1/2)^2 ≤ Q0 := by
    simpa only [abs_neg,abs_of_nonneg ha,add_comm] using hc.containment
  have hmargin : h+angularWidth t ≤ centerX t b (-a) := by
    dsimp [centerX]
    nlinarith only [hm]
  have h := (signed_cap_bounds ht hh hbox hmargin).2.1
  rw [abs_neg,abs_of_nonneg ha] at h
  linarith [hc.u_le,le_abs_self b]

/-- Nor in the deep cap `y ≤ -h`. -/
theorem negative_transverse_cap_impossible {a b t h : ℝ} (hc : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hh : coreRadius ≤ h)
    (hm : h+angularWidth t ≤ -(a*Real.sin t+b*Real.cos t)) : False := by
  have ha : 0 ≤ a := by linarith [hc.half_le]
  have hbox : (|-b|+1/2)^2+(|a|+1/2)^2 ≤ Q0 := by
    simpa only [abs_neg,abs_of_nonneg ha,add_comm] using hc.containment
  have hmargin : h+angularWidth t ≤ centerX t (-b) a := by
    dsimp [centerX]
    nlinarith only [hm]
  have h := (signed_cap_bounds ht hh hbox hmargin).2.1
  rw [abs_of_nonneg ha] at h
  linarith [hc.u_le,neg_le_abs b]

end SquaresInCircles.Six.Analytic
