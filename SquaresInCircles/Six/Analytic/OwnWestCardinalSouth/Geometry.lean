import SquaresInCircles.Six.Analytic.OwnWestCardinalSouth.Support
import SquaresInCircles.Six.Analytic.OwnSouthWestDominant.Geometry

/-!
# No normalized packing has a missing south wing

The last bit family is W OWN and S cardinal. Its D-sourced DS inequality
supplies r=d-s<pi/4, exactly the source-dependent hypothesis of the smooth
S support cone. The five actual inequalities then contradict the analytic
profile. The other bit families were excluded independently.
Consequently the candidate S-sourced DS inequality is now unconditional on
NormalizedPacking, without importing Classification or a finite checker.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnWestCardinalSouth
open Normalization

theorem not_missing_south {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=false) : ¬ MissingSouthWing P := by
  intro hmissing
  let v := -P.helperAngle 2
  let s := P.helperAngle 4
  let d := P.diagonalAngle
  have hv : 0 ≤ v ∧ v ≤ 2/3 := by
    have hneg := canonical_own_west_negative P hW
    dsimp [v]
    constructor <;> linarith [P.helper_windows.2.2.1.1]
  have hs : -(2/5) ≤ s ∧ s ≤ 2/5 := by
    have h := abs_lt.mp (P.cardinal_angle 4 hS)
    exact ⟨h.1.le,h.2.le⟩
  have hd : 1/2 ≤ d ∧ d ≤ Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  have hr : d-s ≤ Real.pi/4 := by
    have h := hmissing.phase_wall
    dsimp [d,s]
    linarith
  have hWphase : P.phase 2=Real.pi-v := by
    have h := P.phase_from_deviation 2
    have h2 : cardinalCenter (matchingCardinal 2) = Real.pi := rfl
    rw [h2] at h
    rw [h]
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
      P.radial 4*Real.cos s-P.transverse 4*Real.sin s+P.center.2 := by
    have h := P.cardinal_separator 4 hS
    change 0 ≤ centralMargin .south (P.phase 4) (P.radial 4) (P.transverse 4)
      P.center.1 P.center.2 at h
    rw [hSphase] at h
    simp only [centralMargin,Normalization.centerY,angularWidth,Real.cos_add,Real.sin_add,
      south_cos,south_sin,zero_mul,one_mul,neg_one_mul,zero_add,add_zero,zero_sub,neg_neg,
      abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hCD : 1/2+angularWidth d ≤
      P.radial 3+P.center.1*Real.cos d+P.center.2*Real.sin d := by
    have h := P.own_separator 3 P.diagonal_own
    rw [hDphase] at h
    have hc : Real.cos (Real.pi+d) = -Real.cos d := by rw [add_comm]; exact Real.cos_add_pi d
    have hs' : Real.sin (Real.pi+d) = -Real.sin d := by rw [add_comm]; exact Real.sin_add_pi d
    simp only [centralMargin,centralNormal,angularWidth,hc,hs',abs_neg] at h
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
  exact scalar_impossible hv hs hd hr
    (P.contained 2) (P.contained 3) (P.contained 4)
    (P.box.1.2.trans CandidateWestTail.ceiling_bounds.2.2.2)
    ⟨P.box.2.1,P.box.2.2.trans CandidateWestTail.ceiling_bounds.2.2.2⟩ hCW hCS hCD hWD hDS

end SquaresInCircles.Six.Analytic.OwnWestCardinalSouth

namespace SquaresInCircles.Six.Analytic
open Normalization

/-- The full missing-south exclusion is independent of the fixed-row classification. -/
theorem not_missing_south {R : ℝ} (P : NormalizedPacking R) : ¬ MissingSouthWing P := by
  intro h
  exact OwnWestCardinalSouth.not_missing_south P
    (CardinalSouthTail.missing_south_requires_own_west h) h.south_cardinal h

/-- Every normalized packing has the actual candidate south separating inequality. -/
theorem candidate_south_separator {R : ℝ} (P : NormalizedPacking R) :
    Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center) := by
  by_contra h
  exact not_missing_south P (missing_south_of_failure P h)

end SquaresInCircles.Six.Analytic
