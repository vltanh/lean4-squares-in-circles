import SquaresInCircles.Six.Analytic.FixedPairLowerBound
import SquaresInCircles.Six.Analytic.FixedDiagonalWork

/-!
# The radius from the stress

`ReductionHypotheses` collects what the stress needs of a normalized packing: D
is separated from W and from S along the secondary axes of W and of S, as in the
model, the angles of the two pairs lie in their domains, and the angle of D is
at least `1/2`. The work of the stress, `candidateWork`, is then at least
`(|n| + |e|)/1000`, by the pair lower bounds and the nonnegative diagonal
remainder, so it vanishes only at the angles of the model. In a disk of squared
radius less than `qStar` the separating inequalities and the strict support of D
would make it negative; so if the squared radius of the disk is at most `qStar`,
the radius is exactly `radius`.
-/
noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

/-- The separators of D along the secondary axes of W and of S, the pair
domains of the angles, and `d ≥ 1/2`. -/
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

/-- The values of the pairs N, W and E, S and of the diagonal part of the
stress, at the angles of the packing. -/
def candidateWork {R : ℝ} (P : NormalizedPacking R) (u v : Fin 4) : ℝ :=
  value (P.ownBits 1) (P.ownBits 2) u (P.helperAngle 1) (P.helperAngle 2)+
    value (P.ownBits 0) (P.ownBits 4) v (-P.helperAngle 0) (-P.helperAngle 4)+
    diagonalValue (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle

/-- The work of the stress is at least the diagonal remainder plus
`(|n| + |e|)/1000`. -/
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

/-- If the work of the stress is not positive, the angles are those of the
model. -/
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

/-- A normalized packing in a disk of radius `R` with `R² ≤ qStar` that
satisfies the reduction hypotheses has `R = radius`. -/
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

end SquaresInCircles.Six.Analytic.FixedPair
