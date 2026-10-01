import SquaresInCircles.Six.Analytic.WestGapReserve.Support
import SquaresInCircles.Six.Analytic.LowDWestSource.Geometry

/-!
# A wider gap between W and D

If W is separated from the central square along its own axis, and W and D along
the secondary axis of D, then `d - w > 53/50`. Such a separation already has
`d - w > 1` and `d > 3/5`, and `scalar_impossible` excludes `d - w ≤ 53/50` on
the rest of the rectangle. The square S plays no part, so the bound holds for
either separator of S.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestGapReserve
open Normalization

theorem own_west_gap {R : ℝ} (P : NormalizedPacking R) (hW : P.ownBits 2=true)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    53/50 < P.diagonalAngle-P.helperAngle 2 := by
  by_contra! hshort
  let v := -P.helperAngle 2
  let d := P.diagonalAngle
  have hg := DW_Dsecondary_gap_gt_one P hsep
  have hcw : cardinalCenter (matchingCardinal 2) = Real.pi := rfl
  rw [P.phase_from_deviation 2,hcw] at hg
  have hq : 1 ≤ v+d ∧ v+d ≤ 53/50 := by
    dsimp [v,d,NormalizedPacking.diagonalAngle] at *
    constructor <;> linarith
  have hd0 := DW_Dsecondary_diagonal_gt_three_fifths P hsep
  have hd : 3/5 ≤ d ∧ d ≤ 11/14 := by
    dsimp [d]
    exact ⟨hd0.le,by linarith [P.diagonal_angle_range.2,Real.pi_lt_d4]⟩
  have hWphase : P.phase 2=Real.pi-v := by
    rw [P.phase_from_deviation 2,hcw]
    dsimp [v]
    ring
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
  have hCD : 1/2+angularWidth d ≤
      P.radial 3+P.center.1*Real.cos d+P.center.2*Real.sin d := by
    have h := P.own_separator 3 P.diagonal_own
    rw [hDphase] at h
    have hcpi : Real.cos (Real.pi+d) = -Real.cos d := by rw [add_comm,Real.cos_add_pi]
    have hspi : Real.sin (Real.pi+d) = -Real.sin d := by rw [add_comm,Real.sin_add_pi]
    simp only [centralMargin,centralNormal,angularWidth,hcpi,hspi,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hWD : 1/2+angularWidth (v+d) ≤
      P.radial 2*Real.sin (v+d)-P.transverse 2*Real.cos (v+d)+P.transverse 3 := by
    have h := hsep
    change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at h
    rw [P.square_def 2,P.square_def 3,hWphase,hDphase,oriented_pair_threshold,pair_frameY_right,
      show (Real.pi+d)-(Real.pi-v)=v+d by ring] at h
    nlinarith only [h]
  exact scalar_impossible hq hd (P.contained 2) (P.contained 3)
    (P.box.1.2.trans CandidateWestTail.ceiling_bounds.2.2.2)
    (P.box.2.2.trans CandidateWestTail.ceiling_bounds.2.2.2) hCW hCD hWD

end SquaresInCircles.Six.Analytic.WestGapReserve

namespace SquaresInCircles.Six.Analytic
open Normalization

lemma MissingWestWing.own_gap_reserve {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) (hW : P.ownBits 2=true) :
    53/50 < P.diagonalAngle-P.helperAngle 2 :=
  WestGapReserve.own_west_gap P hW h.from_diagonal

end SquaresInCircles.Six.Analytic
