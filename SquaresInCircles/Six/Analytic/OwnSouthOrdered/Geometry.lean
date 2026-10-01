import SquaresInCircles.Six.Analytic.OwnSouthOrdered.Support
import SquaresInCircles.Six.Analytic.CoupledWingBudgetSharp
import SquaresInCircles.Six.Analytic.CardinalSouthTail.Geometry

/-!
# A missing south wing with ordered own wings

Let W and S be separated from C along their own axes, with `-w ≤ s`. Then W–D,
along the secondary axis of W, and D–S, along the secondary axis of D, are not
both separated; in particular `MissingSouthWing` fails. With `v = -w`, the
normalization gives `0 ≤ v ≤ s ≤ 2/3` and `1/2 ≤ d ≤ π/4`, and two own wings
sharing the central square have `v + s < 24/25`. In the frames of the squares
the four separating inequalities are those of `scalar_impossible`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthOrdered
open Normalization

/-- With W and S separated from C along their own axes and `-w ≤ s`, the south
wing of D is not missing. -/
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
