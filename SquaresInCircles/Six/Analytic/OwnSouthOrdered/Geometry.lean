import SquaresInCircles.Six.Analytic.OwnSouthOrdered.Support
import SquaresInCircles.Six.Analytic.CoupledWingBudgetSharp
import SquaresInCircles.Six.Analytic.CardinalSouthTail.Geometry

/-!
# An actual missing-south configuration cannot have 0 <= -w <= s

Every inequality below comes from the normalized packing and the two source
witnesses in MissingSouthWing. No candidate south separator is assumed.
The shared-center angle bound gives v+s<24/25. The four-edge scalar theorem
then excludes the entire ordered two-OWN domain.

Together with the existing cardinal-W exclusion, a remaining missing-south
configuration with OWN S must satisfy W OWN and 0< s<-w. This is a strict
reduction of the remaining cases, not a claim that the opposite ordering or
the cardinal-S case is already excluded. Compilation remains unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthOrdered
open Normalization

theorem not_missing_south_of_order {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=true)
    (horder : -P.helperAngle 2 ≤ P.helperAngle 4) : ¬ MissingSouthWing P := by
  intro hmissing
  let v := -P.helperAngle 2
  let s := P.helperAngle 4
  let d := P.diagonalAngle
  have hv : 0 ≤ v := (neg_pos.mpr (canonical_own_west_negative P hW)).le
  have hs : s ≤ 2/3 := P.helper_windows.2.2.2.2.le
  have hvs : v ≤ s := horder
  have hsum : v+s ≤ 24/25 := by
    have h := normalized_own_wing_angle_sum_lt_twenty_four_twenty_fifths P hW hS
    dsimp [v,s]
    linarith
  have hd : 1/2 ≤ d ∧ d ≤ Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  have hWphase : P.phase 2=Real.pi-v := by
    rw [P.phase_from_deviation 2,
      show cardinalCenter (matchingCardinal 2)=Real.pi from rfl]
    dsimp [v]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+s := P.phase_from_deviation 4
  have hDphase : P.phase 3=Real.pi+d := by
    dsimp [d,NormalizedPacking.diagonalAngle]
    ring
  have hCW : 1/2+angularWidth v ≤
      P.radial 2+P.center.1*Real.cos v-P.center.2*Real.sin v := by
    have h := P.own_separator 2 hW
    rw [hWphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hCS : 1/2+angularWidth s ≤
      P.radial 4-P.center.1*Real.sin s+P.center.2*Real.cos s := by
    have h := P.own_separator 4 hS
    rw [hSphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_add,Real.sin_add,
      south_cos,south_sin,zero_mul,neg_one_mul,zero_sub,neg_neg,add_zero,abs_neg] at h
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
  exact scalar_impossible hv hvs hs hsum hd
    (P.contained 2) (P.contained 3) (P.contained 4)
    (P.box.1.2.trans CandidateWestTail.ceiling_bounds.2.2.2)
    (P.box.2.2.trans CandidateWestTail.ceiling_bounds.2.2.2) hCW hCS hWD hDS

end SquaresInCircles.Six.Analytic.OwnSouthOrdered

namespace SquaresInCircles.Six.Analytic
open Normalization

/-- In the remaining two-OWN case the west tilt is strictly larger. -/
lemma MissingSouthWing.south_lt_neg_west {R : ℝ} {P : NormalizedPacking R}
    (h : MissingSouthWing P) (hS : P.ownBits 4=true) :
    P.helperAngle 4 < -P.helperAngle 2 := by
  have hW := CardinalSouthTail.missing_south_requires_own_west h
  by_contra! horder
  exact OwnSouthOrdered.not_missing_south_of_order P hW hS horder h

end SquaresInCircles.Six.Analytic
