import SquaresInCircles.Six.Analytic.CardinalSouthTail.Support
import SquaresInCircles.Six.Analytic.MixedCardinalSouth.Geometry

/-!
# Close the entire cardinal-W missing-south branch

The old MixedCardinalSouth argument handles s<=12/25. A larger s is
necessarily canonical OWN-S. Four actual inequalities, CW, CS, WD, DS, then
contradict the large-tail profile with weights 4,10,3,3. No candidate D/S
inequality is assumed: the D-sourced separator comes from MissingSouthWing.

Consequently every missing south wing has W OWN. This removes the former
cardinal-W / large-OWN-S exception, without asserting that the unrestricted
OWN-W case or the independent south upper tail has been solved.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.CardinalSouthTail
open Normalization

/-- The four scalar separators are incompatible on the entire large-tail domain. -/
theorem scalar_impossible (negative : Bool)
    {v s d aw bw ad bd asouth bsouth cx cy : ℝ}
    (hv : vLower negative ≤ v ∧ v ≤ vUpper negative)
    (hs : 12/25 ≤ s ∧ s ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hS : ContainedChart asouth |bsouth|) (hcx : 0 ≤ cx) (hcy : cy ≤ c0)
    (hCW : 1/2+angularWidth v ≤ aw*Real.cos v+bw*Real.sin v+cx)
    (hCS : 1/2+angularWidth s ≤ asouth-cx*Real.sin s+cy*Real.cos s)
    (hWD : 1/2+angularWidth (d+v) ≤
      ad*Real.sin (d+v)+bd*Real.cos (d+v)-bw)
    (hDS : 1/2+angularWidth (d-s) ≤
      asouth*Real.cos (d-s)+bsouth*Real.sin (d-s)-bd) : False := by
  have hraw := v_bounds hv
  have hq : 0 ≤ d+v ∧ d+v ≤ 6/5 := by
    constructor <;> linarith [hraw.1,hraw.2,hd.1,hd.2]
  have hcr := Real.cos_nonneg_of_mem_Icc
    (show d-s ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hs.1,hs.2,hd.1,hd.2,Real.pi_gt_d2])
  have hsum : totalThreshold v s d ≤
      (4*Real.cos v*aw+(4*Real.sin v-3)*bw)+
      (3*Real.sin (d+v)*ad+(3*Real.cos (d+v)-3)*bd)+
      ((10+3*Real.cos (d-s))*asouth+3*Real.sin (d-s)*bsouth)+
      ((4-10*Real.sin s)*cx+10*Real.cos s*cy) := by
    dsimp [totalThreshold]
    linear_combination 4*hCW+10*hCS+3*hWD+3*hDS
  have hw := west_support hW v
  have hd' := diagonal_support hD hq
  have hs' := south_support hS hcr
  have hc := central_support hs hcx hcy
  have hnonpos : defect v s d ≤ 0 := by
    dsimp [defect]
    linarith only [hsum,hw,hd',hs',hc]
  have hpositive := (positive negative hv hs hd).trans_le
    (profile_le_defect negative hv hs hd)
  linarith

/-- The large positive OWN-S case is excluded using its actual central separator. -/
theorem not_missing_south_of_large_own {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=true)
    (hlarge : 12/25 ≤ P.helperAngle 4) : ¬ MissingSouthWing P := by
  intro hmissing
  let v := -P.helperAngle 2
  let s := P.helperAngle 4
  let d := P.diagonalAngle
  have hvraw : -(2/5) ≤ v ∧ v ≤ 2/5 := by
    have h := abs_lt.mp (P.cardinal_angle 2 hW)
    dsimp [v]
    constructor <;> linarith [h.1,h.2]
  have hs : 12/25 ≤ s ∧ s ≤ 2/3 :=
    ⟨hlarge,P.helper_windows.2.2.2.2.le⟩
  have hd : 1/2 ≤ d ∧ d ≤ 11/14 := by
    have hlo := normalized_diagonal_gt_half P
    have hhi := P.diagonal_angle_range.2
    constructor <;> linarith [Real.pi_lt_d4]
  have hWphase : P.phase 2=Real.pi-v := by
    have h : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
    rw [h]
    dsimp [v]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+s := P.phase_from_deviation 4
  have hDphase : P.phase 3=Real.pi+d := by
    dsimp [d,NormalizedPacking.diagonalAngle]
    ring
  have hCW : 1/2+angularWidth v ≤
      P.radial 2*Real.cos v+P.transverse 2*Real.sin v+P.center.1 := by
    have h := P.cardinal_separator 2 hW
    change 0 ≤ centralMargin .west (P.phase 2) (P.radial 2) (P.transverse 2)
      P.center.1 P.center.2 at h
    rw [hWphase] at h
    simp only [centralMargin,centerX,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hCS : 1/2+angularWidth s ≤
      P.radial 4-P.center.1*Real.sin s+P.center.2*Real.cos s := by
    have h := P.own_separator 4 hS
    rw [hSphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_add,Real.sin_add,
      south_cos,south_sin,zero_mul,neg_one_mul,add_zero,abs_neg,zero_sub,neg_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hWD : 1/2+angularWidth (d+v) ≤
      P.radial 3*Real.sin (d+v)+P.transverse 3*Real.cos (d+v)-P.transverse 2 := by
    have h := hmissing.west_wing
    change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      frameY (P.square 2) (sub (P.square 3).center (P.square 2).center) at h
    rw [P.square_def 2,P.square_def 3,hWphase,hDphase,oriented_pair_threshold,pair_frameY_left,
      show (Real.pi+d)-(Real.pi-v)=d+v by ring] at h
    exact h
  have hDS : 1/2+angularWidth (d-s) ≤
      P.radial 4*Real.cos (d-s)+P.transverse 4*Real.sin (d-s)-P.transverse 3 := by
    have h := hmissing.from_diagonal
    change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 3) (sub (P.square 4).center (P.square 3).center) at h
    rw [P.square_def 3,P.square_def 4,hDphase,hSphase,oriented_pair_threshold,pair_frameY_left,
      show (3*Real.pi/2+s)-(Real.pi+d)=Real.pi/2-(d-s) by ring,
      FixedPair.width_half_pi_sub,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] at h
    exact h
  have finish (negative : Bool)
      (hv : vLower negative ≤ v ∧ v ≤ vUpper negative) : False :=
    scalar_impossible negative hv hs hd (P.contained 2) (P.contained 3) (P.contained 4)
      P.box.1.1 P.box.2.2 hCW hCS hWD hDS
  by_cases hv0 : 0 ≤ v
  · exact finish false (by simpa [vLower,vUpper] using And.intro hv0 hvraw.2)
  · exact finish true (by
      simpa [vLower,vUpper] using And.intro hvraw.1 (le_of_not_ge hv0))

/-- No missing-south configuration survives with cardinal W, for either S bit. -/
theorem not_missing_south {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) : ¬ MissingSouthWing P := by
  intro hmissing
  obtain ⟨hS,hs⟩ := MixedCardinalSouth.remaining_case_requires_south_tail hmissing hW
  exact not_missing_south_of_large_own P hW hS hs.le hmissing

/-- The actual candidate south separator is now available for every cardinal W. -/
theorem south_wing_of_cardinal_west {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) :
    Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center) := by
  by_contra h
  exact not_missing_south P hW (missing_south_of_failure P h)

/-- The former large-S exception has been removed from the remaining domain. -/
theorem missing_south_requires_own_west {R : ℝ} {P : NormalizedPacking R}
    (hmissing : MissingSouthWing P) : P.ownBits 2=true := by
  cases hW : P.ownBits 2
  · exact False.elim (not_missing_south P hW hmissing)
  · rfl

end SquaresInCircles.Six.Analytic.CardinalSouthTail
