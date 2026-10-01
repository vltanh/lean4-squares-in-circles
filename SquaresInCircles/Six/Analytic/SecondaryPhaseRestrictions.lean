import SquaresInCircles.Six.Analytic.NonnegativeWestSecondary
import SquaresInCircles.Six.Analytic.SouthSecondaryComplete

/-!
# Phase gaps of separations along the secondary axis of D

If W and D are separated along the secondary axis of D, their phases differ by
more than `π/4`, so the angles of W and D satisfy `w < d - π/4`. Likewise, if
D and S are separated along the secondary axis of D, then `s > d - π/4`. Both
follow from `nonnegative_W_Dsecondary_excluded`, the projection bound for a
square that avoids the core, together with `|b_D| < 229/1000`; for S it is
applied with the transverse coordinates negated.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

/-- A separation of W and D along the secondary axis of D needs a phase gap
above `π/4`. -/
theorem DW_Dsecondary_gap_gt_quarter {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    Real.pi/4 < P.phase 3-P.phase 2 := by
  by_contra! hsmall
  have hq : 0 ≤ P.phase 3-P.phase 2 ∧ P.phase 3-P.phase 2 ≤ Real.pi/4 :=
    ⟨sub_nonneg.mpr P.primary_order.2.2.1.le,hsmall⟩
  have hbD := (normalized_diagonal_core_bounds P).2.2
  have hbound := nonnegative_W_Dsecondary_excluded
    (P.contained 2) (P.avoidsCore 2) hq
    ((le_abs_self (P.transverse 3)).trans_lt hbD)
  change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at hsep
  rw [P.square_def 2,P.square_def 3,oriented_pair_threshold,pair_frameY_right] at hsep
  linarith

/-- A separation of D and S along the secondary axis of D needs a phase gap
above `π/4`. -/
theorem DS_Dsecondary_gap_gt_quarter {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) :
    Real.pi/4 < P.phase 4-P.phase 3 := by
  by_contra! hsmall
  have hq : 0 ≤ P.phase 4-P.phase 3 ∧ P.phase 4-P.phase 3 ≤ Real.pi/4 :=
    ⟨sub_nonneg.mpr P.primary_order.2.2.2.1.le,hsmall⟩
  have hc : ContainedChart (P.radial 4) |-(P.transverse 4)| := by
    simpa only [abs_neg] using P.contained 4
  have hcore : AvoidsCore (P.radial 4) |-(P.transverse 4)| := by
    simpa only [abs_neg] using P.avoidsCore 4
  have hbD := (normalized_diagonal_core_bounds P).2.2
  have hbound := nonnegative_W_Dsecondary_excluded hc hcore hq
    ((neg_le_abs (P.transverse 3)).trans_lt hbD)
  change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
    frameY (P.square 3) (sub (P.square 4).center (P.square 3).center) at hsep
  rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_left] at hsep
  nlinarith only [hsep,hbound]

/-- In angles: a separation of W and D along the secondary axis of D gives
`w < d - π/4`. -/
theorem DW_Dsecondary_west_of_wall {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    P.helperAngle 2 < P.diagonalAngle-Real.pi/4 := by
  have h := DW_Dsecondary_gap_gt_quarter P hsep
  have hw : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hd : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  rw [hw,hd] at h
  linarith

/-- In angles: a separation of D and S along the secondary axis of D gives
`s > d - π/4`. -/
theorem DS_Dsecondary_south_of_wall {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) :
    P.diagonalAngle-Real.pi/4 < P.helperAngle 4 := by
  have h := DS_Dsecondary_gap_gt_quarter P hsep
  have hs : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hd : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  rw [hd,hs] at h
  linarith

end SquaresInCircles.Six.Analytic
