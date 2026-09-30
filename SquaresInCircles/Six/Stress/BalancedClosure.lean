module
public import SquaresInCircles.Six.Stress.BalancedFactorization
public import SquaresInCircles.Six.Stress.PairLowerBound

@[expose] public section

/-!
# Common candidate-graph closure: analytic conversion in progress

The diagonal remainder now has a human-analytic proof. The separate pair
lower bound and the fixed-stress graph classification still have computational
certificate dependencies. They are imported explicitly and remain blockers
under HUMAN_ANALYTIC_STANDARD.md. Therefore the endpoints below are not yet
accepted as the requested human-analytic n=6 proof.

The implication from the pair and diagonal bounds to angle rigidity and radius
equality is ordinary stress algebra; no problem predicate is changed.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization Classification

/-- Quantitative lower bound for the actual balanced defect. -/
theorem balanced_defect_lower {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    diagonalRemainder (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle+
      (1/1000)*(|P.helperAngle 1|+|P.helperAngle 0|)≤balancedDefect P u v := by
  obtain ⟨hn,hw,he,hs⟩ := common_pair_domains P
  have hNW := pair_lower_bound (P.ownBits 1) (P.ownBits 2) u hn hw
  have hES := pair_lower_bound (P.ownBits 0) (P.ownBits 4) v he hs
  rw [abs_neg] at hES
  rw [balanced_defect_factorization]
  dsimp [diagonalRemainder]
  linarith

/-- This conclusion still consumes the not-yet-converted pair lower bound. -/
theorem balanced_defect_nonnegative {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) :
    0≤balancedDefect P u v := by
  have h := balanced_defect_lower P u v
  have hd := diagonal_remainder_nonnegative (common_diagonal_domain P)
  nlinarith [abs_nonneg (P.helperAngle 1),abs_nonneg (P.helperAngle 0)]

def CandidateAngles {R : ℝ} (P : NormalizedPacking R) : Prop :=
  P.helperAngle 0=0 ∧ P.helperAngle 1=0 ∧ P.helperAngle 2=0 ∧ P.helperAngle 4=0 ∧
    P.diagonalAngle=Real.pi/4

def CandidateSources (u v : Fin 4) : Prop := (u=0 ∨ u=3) ∧ (v=0 ∨ v=3)

/-- Radius-bounded actual packings force equality in the supplied scalar bounds. -/
theorem balanced_rigidity {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar)
    (u v : Fin 4) (hsel : BalancedSelected P u v) :
    CandidateAngles P ∧ CandidateSources u v ∧ balancedDefect P u v=0 := by
  have hupper := balanced_defect_nonpositive P hR u v hsel
  have hlower := balanced_defect_lower P u v
  have hdiag := diagonal_remainder_nonnegative (common_diagonal_domain P)
  have hzero : balancedDefect P u v=0 := le_antisymm hupper (balanced_defect_nonnegative P u v)
  have hsum : |P.helperAngle 0|+|P.helperAngle 1|≤0 := by linarith
  have he : P.helperAngle 0=0 := abs_eq_zero.mp (by linarith [abs_nonneg (P.helperAngle 0),abs_nonneg (P.helperAngle 1)])
  have hn : P.helperAngle 1=0 := abs_eq_zero.mp (by linarith [abs_nonneg (P.helperAngle 0),abs_nonneg (P.helperAngle 1)])
  have hdiagzero : diagonalRemainder (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle=0 := by
    apply le_antisymm _ hdiag
    nlinarith [abs_nonneg (P.helperAngle 0),abs_nonneg (P.helperAngle 1)]
  obtain ⟨hw,hs,hd⟩ := diagonal_remainder_zero (common_diagonal_domain P) hdiagzero
  have hDvalue : diagonalValue 0 0 (Real.pi/4)= -2*pairBase := by
    rw [hw,hs,hd] at hdiagzero
    simp only [diagonalRemainder,neg_zero,pairLine_zero,zero_add] at hdiagzero
    linarith
  have hfactor := balanced_defect_factorization P u v
  rw [hzero,he,hn,hw,hs,hd,neg_zero,hDvalue] at hfactor
  have hNW := pair_lower_bound (P.ownBits 1) (P.ownBits 2) u
    (n := (0:ℝ)) (w := (0:ℝ)) (by norm_num) (by norm_num)
  have hES := pair_lower_bound (P.ownBits 0) (P.ownBits 4) v
    (n := (0:ℝ)) (w := (0:ℝ)) (by norm_num) (by norm_num)
  simp only [pairLine_zero,abs_zero,mul_zero,add_zero] at hNW hES
  have hu : pairValue (P.ownBits 1) (P.ownBits 2) u 0 0=pairBase := by linarith
  have hv : pairValue (P.ownBits 0) (P.ownBits 4) v 0 0=pairBase := by linarith
  exact ⟨⟨he,hn,hw,hs,hd⟩,
    ⟨pair_zero_equality_sources _ _ u hu,pair_zero_equality_sources _ _ v hv⟩,hzero⟩

/-- This uses the common envelope route rather than separate survivor claims. -/
theorem normalized_pattern_eight {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar) :
    P.patternCode=8 := by
  obtain ⟨u,v,hsel⟩ := exists_balanced_selection P
  have ha := (balanced_rigidity P hR u v hsel).1
  exact P.pattern_eight_of_zero_helpers ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1

/-- The stress implication is analytic; its remaining pair/classification
premises still require replacement before this is an analytic-only endpoint. -/
theorem normalized_radius_eq {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar) :
    R=Six.radius := by
  obtain ⟨u,v,hsel⟩ := exists_balanced_selection P
  have hcentral : dot ((balancedSystem P u v).force 0) (P.model 0).center≤0 := by
    rw [balanced_central_force_zero]
    norm_num [dot]
  have hdefect : 0≤(balancedSystem P u v).thresholdSum-
      ∑ i,if i=0 then 0 else exactSupport Six.radius (P.model i) ((balancedSystem P u v).force i) :=
    balanced_defect_nonnegative P u v
  exact (balancedSystem P u v).radius_eq_of_nonnegative_defect P.model 0 0 P.packing
    radius_gt_half (by simpa only [Six.radius_sq] using hR)
    (balanced_weights_nonnegative P u v) (balanced_separates P u v hsel)
    (balanced_threshold_pos P u v) hcentral hdefect

/-- Selected equality data, subject to the dependency boundary documented above. -/
theorem normalized_candidate_data {R : ℝ} (P : NormalizedPacking R) (hR : R^2≤Six.qStar) :
    ∃ u v : Fin 4, BalancedSelected P u v ∧ CandidateAngles P ∧ CandidateSources u v ∧
      balancedDefect P u v=0 ∧ R=Six.radius := by
  obtain ⟨u,v,hsel⟩ := exists_balanced_selection P
  obtain ⟨ha,hs,hzero⟩ := balanced_rigidity P hR u v hsel
  exact ⟨u,v,hsel,ha,hs,hzero,normalized_radius_eq P hR⟩

end SquaresInCircles.Six.Stress
