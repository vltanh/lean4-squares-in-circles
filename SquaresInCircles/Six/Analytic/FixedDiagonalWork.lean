import SquaresInCircles.Six.Analytic.FixedPairReflection
import SquaresInCircles.Six.Analytic.FixedDiagonalRemainder
import SquaresInCircles.Six.Stress.StrictSupport

/-!
# The work of the diagonal square

If W–D and D–S are separated along the second axes of W and of S, as in the
model, the sum of the two separating inequalities with the weight `m*` and the
support of D in the disk of radius `R₆` bound the diagonal term:
`diagonalValue w s d ≤ m*(-1 - b_W + b_S)`, where `b_W` and `b_S` are the
transverse coordinates of W and S. In a strictly smaller disk the bound is
strict, by the strict support of D, whose force is nonzero.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

/-- W and D are separated along the second axis of W, and D and S along the second
axis of S, as in the model. -/
def CandidateDSeparators {R : ℝ} (P : NormalizedPacking R) : Prop :=
  Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center) ∧
    Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)

lemma width_half_pi_sub (x : ℝ) : angularWidth (Real.pi/2-x)=angularWidth x := by
  simp [angularWidth,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,add_comm]

/-- The sum of the separating inequalities of W–D and D–S, with the weight
`m*`. -/
lemma diagonal_edge_work {R : ℝ} (P : NormalizedPacking R) (h : CandidateDSeparators P) :
    mStar*(1+angularWidth (P.diagonalAngle-P.helperAngle 2)+
        angularWidth (P.diagonalAngle-P.helperAngle 4))≤
      (diagonalLocalForce (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle).1*P.radial 3+
      (diagonalLocalForce (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle).2*P.transverse 3-
      mStar*P.transverse 2+mStar*P.transverse 4 := by
  have hw := h.1
  have hs := h.2
  have hW : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hD : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]; ring
  have hS : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  change Seven.SAT.threshold (P.square 2) (P.square 3)≤
    frameY (P.square 2) (sub (P.square 3).center (P.square 2).center) at hw
  change Seven.SAT.threshold (P.square 3) (P.square 4)≤
    frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at hs
  rw [P.square_def 2,P.square_def 3,hW,hD,oriented_pair_threshold,pair_frameY_left] at hw
  rw [P.square_def 3,P.square_def 4,hD,hS,oriented_pair_threshold,pair_frameY_right] at hs
  have hq : (Real.pi+P.diagonalAngle)-(Real.pi+P.helperAngle 2)=
      P.diagonalAngle-P.helperAngle 2 := by ring
  have hr : (3*Real.pi/2+P.helperAngle 4)-(Real.pi+P.diagonalAngle)=
      Real.pi/2-(P.diagonalAngle-P.helperAngle 4) := by ring
  rw [hq] at hw
  rw [hr,width_half_pi_sub,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] at hs
  have hwm := mul_le_mul_of_nonneg_left hw mStar_pos.le
  have hsm := mul_le_mul_of_nonneg_left hs mStar_pos.le
  dsimp [diagonalLocalForce]
  nlinarith only [hwm,hsm]

lemma diagonal_candidate_box {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar) :
    (|P.radial 3|+1/2)^2+(|P.transverse 3|+1/2)^2≤Six.radius^2 := by
  have h := (P.packing.phi_le (3:Fin 5).succ).trans hR
  change phi (alpha (P.square 3) (0,0)) (beta (P.square 3) (0,0))≤Six.qStar at h
  rw [P.square_def,orientedSquare_alpha,orientedSquare_beta] at h
  simpa only [Six.radius_sq,phi] using h

/-- The support of D bounds the diagonal term by the transverse coordinates of W
and S. -/
theorem actual_diagonal_work {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2≤Six.qStar) (h : CandidateDSeparators P) :
    diagonalValue (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle≤
      mStar*(-1-P.transverse 2+P.transverse 4) := by
  have hedge := diagonal_edge_work P h
  have hsupp := scalar_center_support
    (x := (diagonalLocalForce (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle).1)
    (y := (diagonalLocalForce (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle).2)
    radius_gt_half (diagonal_candidate_box P hR)
  dsimp [diagonalValue]
  nlinarith only [hedge,hsupp]

lemma diagonal_force_nonzero {w s d : ℝ} (hd : DiagonalDomain w s d) :
    (diagonalLocalForce w s d).1≠0 ∨ (diagonalLocalForce w s d).2≠0 := by
  left
  apply ne_of_gt
  rw [diagonal_force_formula]
  exact mul_pos (mul_pos diagonalK_pos (diagonal_trig_signs hd).1)
    (diagonal_trig_signs hd).2.1

/-- In a disk strictly smaller than the optimal one the bound is strict. -/
theorem actual_diagonal_work_strict {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2<Six.qStar) (h : CandidateDSeparators P)
    (hd : DiagonalDomain (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle) :
    diagonalValue (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle<
      mStar*(-1-P.transverse 2+P.transverse 4) := by
  have hedge := diagonal_edge_work P h
  have hbox := (P.packing.phi_le (3:Fin 5).succ).trans_lt hR
  change phi (alpha (P.square 3) (0,0)) (beta (P.square 3) (0,0))<Six.qStar at hbox
  rw [P.square_def,orientedSquare_alpha,orientedSquare_beta] at hbox
  have hbox' : (|P.radial 3|+1/2)^2+(|P.transverse 3|+1/2)^2<Six.radius^2 := by
    simpa only [Six.radius_sq,phi] using hbox
  have hsupp := scalar_center_support_strict
    (x := (diagonalLocalForce (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle).1)
    (y := (diagonalLocalForce (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle).2)
    radius_gt_half (diagonal_force_nonzero hd) hbox'
  dsimp [diagonalValue]
  nlinarith only [hedge,hsupp]

end SquaresInCircles.Six.Analytic.FixedPair
