module

public import SquaresInCircles.Eight.Boundary.Reduction

/-!
# Eight squares: strict comparisons of the axes of G–A and of E–H

A sorted square that avoids the core has primary coordinate above `447/800`
(`sorted_core_primary_reserve`, `original_core_primary_reserve`). With `aG > 447/800`,
`bA < 11/25`, `0 ≤ aA + g < 71/50` and `0 ≤ κ < 13/200`, the reserve `aG - bA - (aA + g) κ`
exceeds `529/20000` (`ga_coefficient_reserve`), and when `1 - c = s κ` it is the difference,
divided by `s`, of the projections of G–A on the axes zero and one
(`ga_projection_difference`). So when GA0 is tight, GA1 falls strictly short of the width
(`ga1_strictly_unavailable`), with no upper bound on the radial state of G. In the same way, when
EH1 is tight, EH0 falls strictly short of the width, since `bH < aE` and `aH + bE ≥ 0`
(`eh0_strictly_unavailable`). At a tight contact the witness of G–A or of E–H is therefore the
tight axis.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight

/-! ## Core avoidance gives the reserve of G–A -/

theorem sorted_core_primary_reserve {a b : ℝ} (hba : b≤a)
    (hcore : (1/12 : ℝ)^2 ≤
      (max (a-1/2) 0)^2+(max (b-1/2) 0)^2) :
    447/800<a := by
  by_contra! ha
  have hA : max (a-1/2) 0 ≤ 47/800 :=
    max_le (by linarith) (by norm_num)
  have hBA : max (b-1/2) 0 ≤ max (a-1/2) 0 :=
    max_le_max (by linarith) le_rfl
  have hB : max (b-1/2) 0 ≤ 47/800 := hBA.trans hA
  have hA2 := pow_le_pow_left₀ (le_max_right (a-1/2) 0) hA 2
  have hB2 := pow_le_pow_left₀ (le_max_right (b-1/2) 0) hB 2
  norm_num at hA2 hB2
  nlinarith

theorem original_core_primary_reserve {K : UnitSquare} (hc : CoreAvoiding K)
    (hsorted : beta K (0,0) ≤ alpha K (0,0)) :
    447/800 < alpha K (0,0) := by
  apply sorted_core_primary_reserve hsorted
  simpa only [coreDistanceSq,coreRadius] using
    (coreAvoiding_iff_distance K).1 hc

/-- The reserve of the comparison of GA0 with GA1: `aG - bA - A κ > 529/20000`. -/
theorem ga_coefficient_reserve {aG bA A κ : ℝ}
    (haG : 447/800<aG) (hbA : bA<11/25)
    (hA : A<71/50) (_hA0 : 0≤A)
    (hκ : κ<13/200) (hκ0 : 0≤κ) :
    529/20000 < aG-bA-A*κ := by
  have hp : A*κ ≤ (71/50 : ℝ)*(13/200) :=
    mul_le_mul hA.le hκ.le hκ0 (by norm_num)
  linarith

theorem ga_projection_difference {aG aA bA g s c κ : ℝ}
    (hhalf : 1-c=s*κ) :
    (aA*c-bA*s-g)-(aA-aG*s-g*c) =
      s*(aG-bA-(aA+g)*κ) := by
  linear_combination -(aA+g)*hhalf

/-- When GA0 is tight, as on the stationary source, the projection of GA1 is strictly below the
width `W`, so GA1 does not separate; no upper bound on the radial state of G is used. -/
theorem ga1_strictly_unavailable {aG aA bA g s c κ W : ℝ}
    (hs : 0<s) (hhalf : 1-c=s*κ)
    (haG : 447/800<aG) (hbA : bA<11/25)
    (hA : aA+g<71/50) (hA0 : 0≤aA+g)
    (hκ : κ<13/200) (hκ0 : 0≤κ)
    (hcontact : aA*c-bA*s-g=W) :
    aA-aG*s-g*c < W := by
  have hr := ga_coefficient_reserve haG hbA hA hA0 hκ hκ0
  have hr0 : 0<aG-bA-(aA+g)*κ := by linarith
  have hdiff : 0<(aA*c-bA*s-g)-(aA-aG*s-g*c) := by
    rw [ga_projection_difference hhalf]
    exact mul_pos hs hr0
  linarith

theorem eh_projection_difference (aH bH aE bE s c : ℝ) :
    (aH+aE*s-bE*c)-(aH*c+bH*s-bE) =
      (aE-bH)*s+(aH+bE)*(1-c) := by
  ring

/-- When EH1 is tight, as on the stationary source, the projection of EH0 is strictly below the
width `W`, so the witness of E–H has the normal of EH1. -/
theorem eh0_strictly_unavailable {aH bH aE bE s c W : ℝ}
    (hs : 0<s) (hc : c≤1) (hgap : bH<aE)
    (hpositive : 0≤aH+bE) (hcontact : aH+aE*s-bE*c=W) :
    aH*c+bH*s-bE < W := by
  have hfirst : 0<(aE-bH)*s := mul_pos (sub_pos.mpr hgap) hs
  have hsecond : 0≤(aH+bE)*(1-c) :=
    mul_nonneg hpositive (sub_nonneg.mpr hc)
  have hdiff := eh_projection_difference aH bH aE bE s c
  linarith

end SquaresInCircles.Eight
