module
public import SquaresInCircles.Six.Analytic.FixedPairLowerBound
public import SquaresInCircles.Six.Analytic.FixedDiagonalWork

@[expose] public section

/-!
# Candidate-graph closure using only the analytic fixed-pair bounds

The remaining geometry is exposed as ReductionHypotheses, not added to the
original Packing predicate and not supplied by an axiom. The reduction consists
of the actual two D separators, the two bit-dependent pair domains, and d>=1/2.
Once these have been proved, the statements below finish angle/source rigidity
and the exact-radius inference without the old pair or fixed-row certificates.

This conditional closure does NOT by itself prove ReductionHypotheses for an
arbitrary packing. That classification/domain obligation remains open.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

structure ReductionHypotheses {R : ℝ} (P : NormalizedPacking R) : Prop where
  diagonal_edges : CandidateDSeparators P
  northwest_domain : Domain (P.ownBits 1) (P.ownBits 2) (P.helperAngle 1) (P.helperAngle 2)
  eastsouth_domain : Domain (P.ownBits 0) (P.ownBits 4) (-P.helperAngle 0) (-P.helperAngle 4)
  diagonal_half : 1/2≤P.diagonalAngle

lemma ReductionHypotheses.diagonal_domain {R : ℝ} {P : NormalizedPacking R}
    (h : ReductionHypotheses P) :
    DiagonalDomain (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle :=
  pair_domains_diagonal_domain h.northwest_domain h.eastsouth_domain
    ⟨h.diagonal_half,P.diagonal_angle_bounds.2⟩

lemma domain_origin (no wo : Bool) : Domain no wo 0 0 := by
  cases no <;> cases wo <;> norm_num [Domain]

def candidateWork {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) : ℝ :=
  value (P.ownBits 1) (P.ownBits 2) u (P.helperAngle 1) (P.helperAngle 2)+
    value (P.ownBits 0) (P.ownBits 4) v (-P.helperAngle 0) (-P.helperAngle 4)+
    diagonalValue (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle

/-- Quantitative scalar bound for the actual fixed pair expressions. -/
theorem candidate_work_lower {R : ℝ} (P : NormalizedPacking R)
    (h : ReductionHypotheses P) (u v : Fin 4) :
    remainder (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle+
      (1/1000)*(|P.helperAngle 1|+|P.helperAngle 0|)≤candidateWork P u v := by
  have hNW := lower_bound u h.northwest_domain
  have hES := lower_bound v h.eastsouth_domain
  rw [abs_neg] at hES
  dsimp [candidateWork,remainder]
  linarith

lemma candidate_work_nonnegative {R : ℝ} (P : NormalizedPacking R)
    (h : ReductionHypotheses P) (u v : Fin 4) : 0≤candidateWork P u v := by
  have hbound := candidate_work_lower P h u v
  have hdiag := remainder_nonnegative h.diagonal_domain
  nlinarith [abs_nonneg (P.helperAngle 1),abs_nonneg (P.helperAngle 0)]

/-- Any actual selected pair work reaching zero has the candidate angles. -/
theorem angles_of_nonpositive_work {R : ℝ} (P : NormalizedPacking R)
    (h : ReductionHypotheses P) (u v : Fin 4) (hwork : candidateWork P u v≤0) :
    P.helperAngle 0=0 ∧ P.helperAngle 1=0 ∧ P.helperAngle 2=0 ∧
      P.helperAngle 4=0 ∧ P.diagonalAngle=Real.pi/4 := by
  have hlo := candidate_work_lower P h u v
  have hdiag := remainder_nonnegative h.diagonal_domain
  have he : P.helperAngle 0=0 := abs_eq_zero.mp (by
    nlinarith [abs_nonneg (P.helperAngle 1),abs_nonneg (P.helperAngle 0)])
  have hn : P.helperAngle 1=0 := abs_eq_zero.mp (by
    nlinarith [abs_nonneg (P.helperAngle 1),abs_nonneg (P.helperAngle 0)])
  have hz : remainder (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle=0 := by
    apply le_antisymm _ hdiag
    nlinarith [abs_nonneg (P.helperAngle 1),abs_nonneg (P.helperAngle 0)]
  obtain ⟨hw,hs,hd⟩ := remainder_zero h.diagonal_domain hz
  exact ⟨he,hn,hw,hs,hd⟩

/-- The strict support of D forbids a smaller radius once the geometric
reduction has been supplied. No equality-only guess about the force is needed. -/
theorem radius_of_reduction {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2≤Six.qStar) (h : ReductionHypotheses P) : R=Six.radius := by
  have hnot : ¬ R^2<Six.qStar := by
    intro hr
    obtain ⟨u,v,hpair⟩ := actual_pair_sum P hR
    have hdiag := actual_diagonal_work_strict P hr h.diagonal_edges h.diagonal_domain
    have hnegative : candidateWork P u v<0 := by dsimp [candidateWork]; linarith
    exact (not_lt_of_ge (candidate_work_nonnegative P h u v)) hnegative
  have heq : R^2=Six.radius^2 := by
    rw [Six.radius_sq]
    exact le_antisymm hR (le_of_not_gt hnot)
  nlinarith [Six.radius_pos,P.packing.1]

/-- Complete candidate angle and source data, conditional solely on the
still-visible analytic classification/domain obligation. -/
theorem candidate_data_of_reduction {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2≤Six.qStar) (h : ReductionHypotheses P) : ∃ u v : Fin 4,
    (P.helperAngle 0=0 ∧ P.helperAngle 1=0 ∧ P.helperAngle 2=0 ∧
      P.helperAngle 4=0 ∧ P.diagonalAngle=Real.pi/4) ∧
    (u=0 ∨ u=3) ∧ (v=0 ∨ v=3) ∧ candidateWork P u v=0 ∧ R=Six.radius := by
  obtain ⟨u,v,huv⟩ := actual_candidate_work P hR h.diagonal_edges
  have hwork : candidateWork P u v≤0 := huv
  have hzero : candidateWork P u v=0 :=
    le_antisymm hwork (candidate_work_nonnegative P h u v)
  have ha := angles_of_nonpositive_work P h u v hwork
  rcases ha with ⟨he,hn,hw,hs,hd⟩
  have hremzero : remainder (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle=0 := by
    have hb := candidate_work_lower P h u v
    have hr := remainder_nonnegative h.diagonal_domain
    apply le_antisymm _ hr
    nlinarith [abs_nonneg (P.helperAngle 0),abs_nonneg (P.helperAngle 1)]
  rw [hw,hs,hd] at hremzero
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
  exact ⟨u,v,⟨he,hn,hw,hs,hd⟩,equality_sources_at_origin _ _ u hu,
    equality_sources_at_origin _ _ v hv,hzero,radius_of_reduction P hR h⟩

end SquaresInCircles.Six.Analytic.FixedPair
