import SquaresInCircles.Six.Analytic.CardinalLowDiagonalSupport
import SquaresInCircles.Six.Analytic.LowDiagonalOwn

/-!
# Every normalized packing has d>1/2, without the former low-D tables

OWN W uses the compensated frozen-center concavity argument. Cardinal W uses
the two analytic rotating-length stresses on the six sign/order vertices.
All primary directions have already been excluded by PrimaryClassification.
The final statement therefore has no selected-axis or W-bit hypothesis.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma cardinal_low_frozen_nonpositive (ds : Bool) {w d aw bw ad bd cx cy : ℝ}
    (hw : -2/5≤w ∧ w≤2/5) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d)
    (hCW : 0≤centralMargin .west (Real.pi+w) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi+w) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (if ds then normalY (orientedSquare (Real.pi+d) ad bd)
        else normalY (orientedSquare (Real.pi+w) aw bw))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi+w) aw bw).center)) :
    cardLowFrozen ds w d aw bw ad bd cx cy≤0 := by
  obtain ⟨hcw,_,hdt,hqt⟩ := cardinal_low_trig hw hd hwd
  have hcq : 0≤Real.cos (d-w) := by linarith [hqt.1]
  have hW : 1/2-cx-aw*Real.cos w+bw*Real.sin w+(Real.cos w+|Real.sin w|)/2≤0 := by
    simp only [centralMargin,centerX,angularWidth,Real.cos_pi_add,Real.sin_pi_add,
      abs_neg,abs_of_nonneg hcw] at hCW
    nlinarith only [hCW]
  have hD : 1/2-ad+(1/2-cx)*Real.cos d+(1/2-cy)*Real.sin d≤0 := by
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,Real.sin_pi_add,
      abs_neg,abs_of_nonneg hdt.1,abs_of_nonneg hdt.2] at hCD
    nlinarith only [hCD]
  have hq : (Real.pi+d)-(Real.pi+w)=d-w := by ring
  cases ds
  · change Seven.SAT.threshold (orientedSquare (Real.pi+w) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      frameY (orientedSquare (Real.pi+w) aw bw)
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi+w) aw bw).center) at hWD
    rw [oriented_pair_threshold,pair_frameY_left,hq,
      angularWidth,abs_of_nonneg hcq,abs_of_nonneg hqt.2] at hWD
    dsimp [cardLowFrozen,cardLowWForce,cardLowDForce,cardLowAlpha,cardLowBeta,cardLowMu,dot]
    nlinarith only [hW,hD,hWD]
  · change Seven.SAT.threshold (orientedSquare (Real.pi+w) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      frameY (orientedSquare (Real.pi+d) ad bd)
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi+w) aw bw).center) at hWD
    rw [oriented_pair_threshold,pair_frameY_right,hq,
      angularWidth,abs_of_nonneg hcq,abs_of_nonneg hqt.2] at hWD
    dsimp [cardLowFrozen,cardLowWForce,cardLowDForce,cardLowAlpha,cardLowBeta,cardLowMu,dot]
    nlinarith only [hW,hD,hWD]

/-- Either secondary source contradicts cardinal W on the whole low-D region. -/
theorem cardinal_low_diagonal_impossible (ds : Bool) {w d aw bw ad bd cx cy : ℝ}
    (hw : -2/5≤w ∧ w≤2/5) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hCW : 0≤centralMargin .west (Real.pi+w) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi+w) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (if ds then normalY (orientedSquare (Real.pi+d) ad bd)
        else normalY (orientedSquare (Real.pi+w) aw bw))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi+w) aw bw).center)) : False := by
  have hp := cardinal_low_diagonal_positive ds hw hd hwd
  have hs := cardLowGap_le_frozen ds hw hd hwd hW hD hc
  have hn := cardinal_low_frozen_nonpositive ds hw hd hwd hCW hCD hWD
  linarith

/-- The low-diagonal tail in the cardinal-W case. -/
theorem cardinal_west_diagonal_gt_half {R : ℝ} (P : NormalizedPacking R)
    (hcard : P.ownBits 2=false) : 1/2<P.diagonalAngle := by
  by_contra! hd
  have hwabs := abs_lt.mp (P.cardinal_angle 2 hcard)
  have hw : -2/5≤P.helperAngle 2 ∧ P.helperAngle 2≤2/5 := ⟨hwabs.1.le,hwabs.2.le⟩
  have hdiag : 0≤P.diagonalAngle ∧ P.diagonalAngle≤1/2 :=
    ⟨P.diagonal_angle_range.1.le,hd⟩
  have hWphase : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hwd : P.helperAngle 2≤P.diagonalAngle := by
    have hh := P.primary_order.2.2.1
    rw [hWphase,hDphase] at hh
    linarith
  obtain ⟨k,hsep,hcases⟩ := DW_secondary_exists P
  rcases hcases with rfl | rfl
  · change Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center) at hsep
    apply cardinal_low_diagonal_impossible false hw hdiag hwd (P.contained 2) (P.contained 3) P.box
      (by simpa only [hWphase] using P.cardinal_separator 2 hcard)
      (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own)
    simpa only [P.square_def,hWphase,hDphase,Bool.false_eq_true,if_false] using hsep
  · change Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center) at hsep
    apply cardinal_low_diagonal_impossible true hw hdiag hwd (P.contained 2) (P.contained 3) P.box
      (by simpa only [hWphase] using P.cardinal_separator 2 hcard)
      (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own)
    simpa only [P.square_def,hWphase,hDphase,if_true] using hsep

/-- Analytic replacement for the complete low-D classification/tail bound. -/
theorem normalized_diagonal_gt_half {R : ℝ} (P : NormalizedPacking R) :
    1/2<P.diagonalAngle := by
  cases hbit : P.ownBits 2
  · exact cardinal_west_diagonal_gt_half P hbit
  · exact own_west_diagonal_gt_half P hbit

end SquaresInCircles.Six.Analytic
