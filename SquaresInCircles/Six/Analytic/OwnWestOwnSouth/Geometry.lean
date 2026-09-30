module
public import SquaresInCircles.Six.Analytic.OwnWestOwnSouth.Support
public import SquaresInCircles.Six.Analytic.OwnWestCardinalWing.Geometry

@[expose] public section

/-!
# The two-OWN missing-west case when the west tilt dominates

Here s<=v=-w. The actual shared-center angle budget v+s<24/25 gives
s<12/25, exactly the whole interval of the continuous-weight scalar argument.
The refined v,d bounds follow from the actual D-sourced west edge. All four
separators are retained from the original packing; none is replaced by a
selected index or a candidate-edge assumption.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnWestOwnSouth
open Normalization

theorem not_missing_west_of_order {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=true)
    (horder : P.helperAngle 4 ≤ -P.helperAngle 2) : ¬ MissingWestWing P := by
  intro hmissing
  let v := -P.helperAngle 2
  let s := P.helperAngle 4
  let d := P.diagonalAngle
  have hb := hmissing.own_west_domain hW
  have hg := hmissing.own_gap_reserve hW
  have hsum := normalized_own_wing_angle_sum_lt_twenty_four_twenty_fifths P hW hS
  have hd : 16/25 ≤ d ∧ d ≤ 11/14 :=
    ⟨hb.2.le,by linarith [P.diagonal_angle_range.2,Real.pi_lt_d4]⟩
  have hv : 53/50-d ≤ v ∧ v ≤ 31/50 := by
    dsimp [v,d]
    constructor <;> linarith
  have hs : 0 ≤ s ∧ s ≤ 12/25 := by
    have hpos := canonical_own_south_positive P hS
    dsimp [s]
    constructor <;> linarith
  have hWphase : P.phase 2=Real.pi-v := by
    rw [P.phase_from_deviation 2]
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
      south_cos,south_sin,zero_mul,one_mul,neg_one_mul,zero_add,add_zero,abs_neg] at h
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

end SquaresInCircles.Six.Analytic.OwnWestOwnSouth
