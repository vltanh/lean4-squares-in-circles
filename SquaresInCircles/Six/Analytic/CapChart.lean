module
public import SquaresInCircles.Six.Normalization.CentralSAT
public import SquaresInCircles.Six.Construction

@[expose] public section

/-!
# Cap chart bounds before the strong central box

The inputs are the far-corner containment inequality and an actual cap margin.
No small transverse bound, pin or normalized packing is an input. Negative
nearest-frame angles are handled by changing only the two local signs.
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

/-- Analytic K3 in a signed nearest side frame; valid before any pin assignment. -/
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

/-- A deep cap cannot be faced by the short axis of a sorted chart. -/
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
