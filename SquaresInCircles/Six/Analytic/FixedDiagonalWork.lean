module
public import SquaresInCircles.Six.Analytic.FixedPairReflection
public import SquaresInCircles.Six.Analytic.FixedDiagonalRemainder
public import SquaresInCircles.Six.Stress.StrictSupport

@[expose] public section

/-!
# Actual diagonal work for the fixed-pair proof

Both hypotheses below are original geometric separator inequalities. Their
classification is deliberately a separate task; neither is inserted into
NormalizedPacking. Adding the two inequalities exposes exactly the transverse
work left by FixedPair.actual_pair_sum. The strict form uses the already
proved strict support theorem at a smaller radius, not a positivity oracle.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

/-- The two candidate D edges, as actual oriented separating inequalities. -/
def CandidateDSeparators {R : ℝ} (P : NormalizedPacking R) : Prop :=
  Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center) ∧
    Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)

lemma width_half_pi_sub (x : ℝ) : angularWidth (Real.pi/2-x)=angularWidth x := by
  simp [angularWidth,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,add_comm]

/-- Threshold sum before applying a support bound to D. -/
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

/-- Exact support bounds the diagonal work left over by the two pair terms. -/
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

/-- The same work inequality is strict at a strictly smaller radius. -/
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

/-- No domain theorem or candidate-graph classification is smuggled into this
sum: both D-edge hypotheses are visible in the statement. -/
theorem actual_candidate_work {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2≤Six.qStar) (h : CandidateDSeparators P) : ∃ u v : Fin 4,
    value (P.ownBits 1) (P.ownBits 2) u (P.helperAngle 1) (P.helperAngle 2)+
      value (P.ownBits 0) (P.ownBits 4) v (-P.helperAngle 0) (-P.helperAngle 4)+
      diagonalValue (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle≤0 := by
  obtain ⟨u,v,hpair⟩ := actual_pair_sum P hR
  have hdiag := actual_diagonal_work P hR h
  exact ⟨u,v,by linarith⟩

end SquaresInCircles.Six.Analytic.FixedPair
