import SquaresInCircles.Six.Analytic.OwnWestCardinalWing.Support
import SquaresInCircles.Six.Analytic.CardinalWestOwnSouth.Geometry

/-!
# A missing west wing must have two OWN wings

Cardinal W has already been excluded. For OWN W and cardinal S, the actual
D-sourced west edge supplies the refined core bounds; the four genuine CW,
CS, WD and DS inequalities then contradict the single analytic stress.
Neither candidate W separation nor any finite classification is assumed.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnWestCardinalWing
open Normalization

theorem not_missing_west {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=false) : ¬ MissingWestWing P := by
  intro hmissing
  let v := -P.helperAngle 2
  let s := P.helperAngle 4
  let d := P.diagonalAngle
  have hb := hmissing.own_west_domain hW
  have hg := hmissing.own_gap_reserve hW
  have hd : 16/25 ≤ d ∧ d ≤ 11/14 :=
    ⟨hb.2.le,by linarith [P.diagonal_angle_range.2,Real.pi_lt_d4]⟩
  have hv : 53/50-d ≤ v ∧ v ≤ 31/50 := by
    dsimp [v,d]
    constructor <;> linarith
  have hs : -(2/5) ≤ s ∧ s ≤ 2/5 := by
    have h := abs_lt.mp (P.cardinal_angle 4 hS)
    exact ⟨h.1.le,h.2.le⟩
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
      south_cos,south_sin,zero_mul,one_mul,neg_one_mul,zero_add,add_zero,abs_neg] at h
    simp only [zero_sub,neg_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hWD : 1/2+angularWidth (v+d) ≤
      P.radial 2*Real.sin (v+d)-P.transverse 2*Real.cos (v+d)+P.transverse 3 := by
    have h := hmissing.from_diagonal
    change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at h
    rw [P.square_def 2,P.square_def 3,hWphase,hDphase,oriented_pair_threshold,pair_frameY_right,
      show (Real.pi+d)-(Real.pi-v)=v+d by ring] at h
    nlinarith only [h]
  have hDS : 1/2+angularWidth (d-s) ≤
      P.transverse 4+P.radial 3*Real.cos (d-s)-P.transverse 3*Real.sin (d-s) := by
    have h := hmissing.south_wing
    change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at h
    rw [P.square_def 3,P.square_def 4,hDphase,hSphase,oriented_pair_threshold,pair_frameY_right,
      show (3*Real.pi/2+s)-(Real.pi+d)=Real.pi/2-(d-s) by ring,
      FixedPair.width_half_pi_sub,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] at h
    nlinarith only [h]
  exact scalar_impossible hs hd hv (P.contained 2) (P.contained 3) (P.contained 4)
    (P.box.1.2.trans CandidateWestTail.ceiling_bounds.2.2.2)
    (P.box.2.2.trans CandidateWestTail.ceiling_bounds.2.2.2) hCW hCS hWD hDS

end SquaresInCircles.Six.Analytic.OwnWestCardinalWing

namespace SquaresInCircles.Six.Analytic
open Normalization

theorem not_missing_west_of_cardinal_south {R : ℝ} (P : NormalizedPacking R)
    (hS : P.ownBits 4=false) : ¬ MissingWestWing P := by
  intro h
  exact OwnWestCardinalWing.not_missing_west P h.west_own hS h

lemma MissingWestWing.south_own {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : P.ownBits 4=true := by
  cases hS : P.ownBits 4
  · exact False.elim (not_missing_west_of_cardinal_south P hS h)
  · rfl

end SquaresInCircles.Six.Analytic
