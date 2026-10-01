import SquaresInCircles.Six.Analytic.FixedCandidateClosure

/-!
# Actual separator witnesses survive the analytic scalar closure

Existence of two small scalar values is not, by itself, enough for contact
reconstruction: the same source indices must still satisfy the actual pair
separating inequalities. This module retains those witnesses throughout.

No fixed-row classification or pair-envelope certificate is imported. The
geometric reduction remains the explicit `ReductionHypotheses` premise.
Compilation is deferred; these are source proof bodies, not kernel-audit output.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

/-- The two selected axes are actual separating axes of the labelled packing. -/
def SelectedPairs {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) : Prop :=
  Seven.SAT.threshold (P.square 2) (P.square 1) ≤
    dot (preferredPairAxis NWsigns (P.square 2) (P.square 1) u)
      (sub (P.square 1).center (P.square 2).center) ∧
  Seven.SAT.threshold (P.square 4) (P.square 0) ≤
    dot (preferredPairAxis ESsigns (P.square 4) (P.square 0) v)
      (sub (P.square 0).center (P.square 4).center)

lemma selected_pairs_exist {R : ℝ} (P : NormalizedPacking R) :
    ∃ u v : Fin 4, SelectedPairs P u v := by
  obtain ⟨u,hu⟩ := P.NW_source
  obtain ⟨v,hv⟩ := P.ES_source
  exact ⟨u,v,hu,hv⟩

/-- N/W work for a specified actual source, rather than an opaque existential. -/
lemma northwest_work_of_selected {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (u : Fin 4)
    (hsel : Seven.SAT.threshold (P.square 2) (P.square 1) ≤
      dot (preferredPairAxis NWsigns (P.square 2) (P.square 1) u)
        (sub (P.square 1).center (P.square 2).center)) :
    value (P.ownBits 1) (P.ownBits 2) u (P.helperAngle 1) (P.helperAngle 2) ≤
      P.center.1-P.center.2+mStar*(P.transverse 2+1/2) := by
  have hn : P.phase 1=Real.pi/2+P.helperAngle 1 := P.phase_from_deviation 1
  have hw : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hN : Seven.SAT.threshold (axisSquare P.center) (P.square 1) ≤
      dot (chosenCenterAxis P 1) (sub (P.square 1).center P.center) :=
    chosen_center_separates P 1
  have hW : Seven.SAT.threshold (axisSquare P.center) (P.square 2) ≤
      dot (chosenCenterAxis P 2) (sub (P.square 2).center P.center) :=
    chosen_center_separates P 2
  rw [P.square_def,central_threshold,chosen_north_axis,hn,width_half_pi_add] at hN
  rw [P.square_def,central_threshold,chosen_west_axis,hw,width_pi_add] at hW
  rw [preferred_northwest_axis,P.square_def 2,P.square_def 1,hw,hn,northwest_threshold] at hsel
  have hNbox := (P.packing.phi_le (1:Fin 5).succ).trans hR
  have hWbox := (P.packing.phi_le (2:Fin 5).succ).trans hR
  change phi (alpha (P.square 1) (0,0)) (beta (P.square 1) (0,0)) ≤ Six.qStar at hNbox
  change phi (alpha (P.square 2) (0,0)) (beta (P.square 2) (0,0)) ≤ Six.qStar at hWbox
  rw [P.square_def,orientedSquare_alpha,orientedSquare_beta] at hNbox hWbox
  apply pair_work_bound (P.ownBits 1) (P.ownBits 2) u
    (Stress.PinPacking.sharp_central_box P.toPinPacking hR) ?_ ?_ hN hW hsel
  · simpa only [Six.radius_sq,phi] using hNbox
  · simpa only [Six.radius_sq,phi] using hWbox

/-- E/S work retains the source chosen before the local coordinate reflection. -/
lemma eastsouth_work_of_selected {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (v : Fin 4)
    (hsel : Seven.SAT.threshold (P.square 4) (P.square 0) ≤
      dot (preferredPairAxis ESsigns (P.square 4) (P.square 0) v)
        (sub (P.square 0).center (P.square 4).center)) :
    value (P.ownBits 0) (P.ownBits 4) v (-P.helperAngle 0) (-P.helperAngle 4) ≤
      P.center.2-P.center.1+mStar*(-P.transverse 4+1/2) := by
  have he : P.phase 0=P.helperAngle 0 := by
    simpa [matchingCardinal,cardinalCenter] using P.phase_from_deviation 0
  have hs : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hE := chosen_center_separates P 0
  have hS := chosen_center_separates P 4
  change Seven.SAT.threshold (axisSquare P.center) (P.square 0) ≤ _ at hE
  change Seven.SAT.threshold (axisSquare P.center) (P.square 4) ≤ _ at hS
  rw [P.square_def,central_threshold,he] at hE
  rw [P.square_def,central_threshold,hs,width_three_half_pi_add] at hS
  have hthr : Seven.SAT.threshold (P.square 4) (P.square 0)=
      1/2+angularWidth ((-P.helperAngle 0)-(-P.helperAngle 4)) := by
    rw [P.square_def 4,P.square_def 0,hs,he,eastsouth_threshold]
  rw [hthr] at hsel
  have hEbox := (P.packing.phi_le (0:Fin 5).succ).trans hR
  have hSbox := (P.packing.phi_le (4:Fin 5).succ).trans hR
  change phi (alpha (P.square 0) (0,0)) (beta (P.square 0) (0,0)) ≤ Six.qStar at hEbox
  change phi (alpha (P.square 4) (0,0)) (beta (P.square 4) (0,0)) ≤ Six.qStar at hSbox
  rw [P.square_def,orientedSquare_alpha,orientedSquare_beta] at hEbox hSbox
  have hc := Stress.PinPacking.sharp_central_box P.toPinPacking hR
  have hNE : (orientedSquare (Real.pi/2+(-P.helperAngle 0))
      (P.radial 0) (-P.transverse 0)).center=Six.diagonalPoint (P.square 0).center := by
    rw [P.square_def,he]
    simpa only [sub_eq_add_neg] using
      reflected_east_center (P.helperAngle 0) (P.radial 0) (P.transverse 0)
  have hWS : (orientedSquare (Real.pi+(-P.helperAngle 4))
      (P.radial 4) (-P.transverse 4)).center=Six.diagonalPoint (P.square 4).center := by
    rw [P.square_def,hs]
    simpa only [sub_eq_add_neg] using
      reflected_south_center (P.helperAngle 4) (P.radial 4) (P.transverse 4)
  apply pair_work_bound (P.ownBits 0) (P.ownBits 4) v
    (an := P.radial 0) (bn := -P.transverse 0) (aw := P.radial 4)
    (c := Six.diagonalPoint P.center) ⟨hc.2,hc.1⟩ ?_ ?_ ?_ ?_ ?_
  · simpa only [Six.radius_sq,phi,abs_neg] using hEbox
  · simpa only [Six.radius_sq,phi,abs_neg] using hSbox
  · rw [width_neg,chosen_east_swap,hNE,← swap_sub,swap_dot]
    exact hE
  · rw [width_neg,chosen_south_swap,hWS,← swap_sub,swap_dot]
    exact hS
  · rw [preferred_eastsouth_swap,hNE,hWS,← swap_sub,swap_dot]
    exact hsel

lemma candidate_work_of_selected {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (hD : CandidateDSeparators P)
    (u v : Fin 4) (hsel : SelectedPairs P u v) : candidateWork P u v ≤ 0 := by
  have hNW := northwest_work_of_selected P hR u hsel.1
  have hES := eastsouth_work_of_selected P hR v hsel.2
  have hdiag := actual_diagonal_work P hR hD
  dsimp [candidateWork]
  linarith

/-- Rigidity for these same selected sources. No new source is chosen after
passing to equality. The unresolved reduction remains an explicit premise. -/
theorem rigidity_of_selected {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (h : ReductionHypotheses P)
    (u v : Fin 4) (hsel : SelectedPairs P u v) :
    (P.helperAngle 0=0 ∧ P.helperAngle 1=0 ∧ P.helperAngle 2=0 ∧
      P.helperAngle 4=0 ∧ P.diagonalAngle=Real.pi/4) ∧
    (u=0 ∨ u=3) ∧ (v=0 ∨ v=3) ∧ candidateWork P u v=0 ∧ R=Six.radius := by
  have hwork := candidate_work_of_selected P hR h.diagonal_edges u v hsel
  have hzero := le_antisymm hwork (candidate_work_nonnegative P h u v)
  obtain ⟨he,hn,hw,hs,hd⟩ := angles_of_nonpositive_work P h u v hwork
  have hremzero : remainder 0 0 (Real.pi/4)=0 := by
    have hlo := candidate_work_lower P h u v
    have hnonneg := remainder_nonnegative h.diagonal_domain
    have hz : remainder (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle=0 := by
      apply le_antisymm _ hnonneg
      nlinarith [abs_nonneg (P.helperAngle 0),abs_nonneg (P.helperAngle 1)]
    simpa only [hw,hs,hd] using hz
  have hDvalue : diagonalValue 0 0 (Real.pi/4)= -2*pairBase := by
    have hh : diagonalValue 0 0 (Real.pi/4)+2*pairBase=0 := by
      simpa [remainder,line] using hremzero
    linarith
  have hf := hzero
  dsimp [candidateWork] at hf
  rw [he,hn,hw,hs,hd,neg_zero,hDvalue] at hf
  have hNW := lower_bound (no := P.ownBits 1) (wo := P.ownBits 2) u
    (domain_origin (P.ownBits 1) (P.ownBits 2))
  have hES := lower_bound (no := P.ownBits 0) (wo := P.ownBits 4) v
    (domain_origin (P.ownBits 0) (P.ownBits 4))
  norm_num [line] at hNW hES
  have hu : value (P.ownBits 1) (P.ownBits 2) u 0 0=pairBase := by linarith
  have hv : value (P.ownBits 0) (P.ownBits 4) v 0 0=pairBase := by linarith
  exact ⟨⟨he,hn,hw,hs,hd⟩,equality_sources_at_origin _ _ u hu,
    equality_sources_at_origin _ _ v hv,hzero,radius_of_reduction P hR h⟩

/-- Candidate data with its genuine geometric witnesses attached. -/
theorem candidate_data_with_selection {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (h : ReductionHypotheses P) : ∃ u v : Fin 4,
    SelectedPairs P u v ∧
    (P.helperAngle 0=0 ∧ P.helperAngle 1=0 ∧ P.helperAngle 2=0 ∧
      P.helperAngle 4=0 ∧ P.diagonalAngle=Real.pi/4) ∧
    (u=0 ∨ u=3) ∧ (v=0 ∨ v=3) ∧ candidateWork P u v=0 ∧ R=Six.radius := by
  obtain ⟨u,v,hsel⟩ := selected_pairs_exist P
  exact ⟨u,v,hsel,rigidity_of_selected P hR h u v hsel⟩

end SquaresInCircles.Six.Analytic.FixedPair
