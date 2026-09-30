import SquaresInCircles.Six.Analytic.SecondaryReduction
import SquaresInCircles.Six.Analytic.FixedCandidateClosure
import SquaresInCircles.Six.Analytic.SouthOwnLowerTail

/-!
# Remove already-proved facts from the final reduction obligation

The E/N pair ranges, cardinal W/S ranges, OWN-W upper bound, d>1/2 and the
lower OWN-S tail are analytic consequences of the actual packing. The remaining
pair-domain requirements are only the outer OWN-W and OWN-S tails. The original
three-bound interface is retained for compatibility and proved equivalent to
this smaller frontier.

The two mixed-wing exclusions and the two remaining outer-tail inequalities
are not assumed true. No extra premise is inserted into Packing or the
normalized model, and no old fixed-row theorem instantiates those obligations.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Normalization

/-- Original interface, retained to avoid changing earlier conditional theorems. -/
def OwnWingTailBounds {R : ℝ} (P : NormalizedPacking R) : Prop :=
  (P.ownBits 2=true → -11/25 ≤ P.helperAngle 2) ∧
  (P.ownBits 4=true → -2/25 ≤ P.helperAngle 4 ∧ P.helperAngle 4 ≤ 11/25)

/-- Only the two outer tails remain: the lower OWN-S bound has been proved. -/
def OwnWingOuterBounds {R : ℝ} (P : NormalizedPacking R) : Prop :=
  (P.ownBits 2=true → -11/25 ≤ P.helperAngle 2) ∧
  (P.ownBits 4=true → P.helperAngle 4 ≤ 11/25)

lemma own_tail_bounds_iff_outer_bounds {R : ℝ} (P : NormalizedPacking R) :
    OwnWingTailBounds P ↔ OwnWingOuterBounds P := by
  constructor
  · rintro ⟨hW,hS⟩
    exact ⟨hW,fun hs => (hS hs).2⟩
  · rintro ⟨hW,hS⟩
    exact ⟨hW,fun hs => ⟨(normalized_own_south_lower_tail P hs).le,hS hs⟩⟩

lemma north_pair_range {R : ℝ} (P : NormalizedPacking R) :
    if P.ownBits 1 then -3/10 ≤ P.helperAngle 1 ∧ P.helperAngle 1 ≤ 5/12
    else -203/1000 ≤ P.helperAngle 1 ∧ P.helperAngle 1 ≤ 203/1000 := by
  cases h : P.ownBits 1
  · have hn := abs_lt.mp (P.north_cardinal_angle_203 h)
    simpa only [h,Bool.false_eq_true,if_false] using And.intro hn.1.le hn.2.le
  · have hn := P.helper_windows.2.1
    simpa only [h,if_true] using And.intro hn.1.le hn.2.le

lemma east_pair_range {R : ℝ} (P : NormalizedPacking R) :
    if P.ownBits 0 then -3/10 ≤ -P.helperAngle 0 ∧ -P.helperAngle 0 ≤ 5/12
    else -203/1000 ≤ -P.helperAngle 0 ∧ -P.helperAngle 0 ≤ 203/1000 := by
  cases h : P.ownBits 0
  · have he := abs_lt.mp (P.east_cardinal_angle_203 h)
    simp only [h,Bool.false_eq_true,if_false]
    constructor <;> linarith [he.1,he.2]
  · have he := P.helper_windows.1
    simp only [h,if_true]
    constructor <;> linarith [he.1,he.2]

/-- For N/W only the negative OWN-W tail remains. -/
theorem northwest_domain_iff_own_tail {R : ℝ} (P : NormalizedPacking R) :
    Domain (P.ownBits 1) (P.ownBits 2) (P.helperAngle 1) (P.helperAngle 2) ↔
      (P.ownBits 2=true → -11/25 ≤ P.helperAngle 2) := by
  constructor
  · intro h hW
    have hw := h.2
    simp only [hW,if_true] at hw
    exact hw.1
  · intro htail
    refine ⟨north_pair_range P,?_⟩
    cases hW : P.ownBits 2
    · have hw := abs_lt.mp (P.cardinal_angle 2 hW)
      simpa only [hW,Bool.false_eq_true,if_false] using And.intro hw.1.le hw.2.le
    · have hneg := canonical_own_west_negative P hW
      simp only [hW,if_true]
      exact ⟨htail hW,by linarith⟩

/-- This reflects only the scalar E/S calculation, not the global D window. -/
theorem eastsouth_domain_iff_own_tail {R : ℝ} (P : NormalizedPacking R) :
    Domain (P.ownBits 0) (P.ownBits 4) (-P.helperAngle 0) (-P.helperAngle 4) ↔
      (P.ownBits 4=true → -2/25 ≤ P.helperAngle 4 ∧ P.helperAngle 4 ≤ 11/25) := by
  constructor
  · intro h hS
    have hs := h.2
    simp only [hS,if_true] at hs
    constructor <;> linarith [hs.1,hs.2]
  · intro htail
    refine ⟨east_pair_range P,?_⟩
    cases hS : P.ownBits 4
    · have hs := abs_lt.mp (P.cardinal_angle 4 hS)
      simp only [hS,Bool.false_eq_true,if_false]
      constructor <;> linarith [hs.1,hs.2]
    · have hs := htail hS
      simp only [hS,if_true]
      constructor <;> linarith [hs.1,hs.2]

/-- Neither normalization nor d>1/2 is an unproved premise of this interface. -/
theorem reduction_iff_edges_and_own_tails {R : ℝ} (P : NormalizedPacking R) :
    ReductionHypotheses P ↔ (CandidateDSeparators P ∧ OwnWingTailBounds P) := by
  constructor
  · intro h
    exact ⟨h.diagonal_edges,(northwest_domain_iff_own_tail P).mp h.northwest_domain,
      (eastsouth_domain_iff_own_tail P).mp h.eastsouth_domain⟩
  · rintro ⟨hedges,hW,hS⟩
    exact ⟨hedges,(northwest_domain_iff_own_tail P).mpr hW,
      (eastsouth_domain_iff_own_tail P).mpr hS,(normalized_diagonal_gt_half P).le⟩

/-- Backwards-compatible formulation of the reduction equivalence. -/
theorem reduction_iff_remaining_obligations {R : ℝ} (P : NormalizedPacking R) :
    ReductionHypotheses P ↔
      (¬ MissingWestWing P ∧ ¬ MissingSouthWing P) ∧ OwnWingTailBounds P := by
  rw [reduction_iff_edges_and_own_tails,candidate_edges_iff_no_missing_wing]

/-- Four substantive facts remain, not five: the lower OWN-S tail is supplied
by its whole-domain canonical-separator proof. -/
theorem reduction_iff_four_obligations {R : ℝ} (P : NormalizedPacking R) :
    ReductionHypotheses P ↔
      (¬ MissingWestWing P ∧ ¬ MissingSouthWing P) ∧ OwnWingOuterBounds P := by
  rw [reduction_iff_remaining_obligations,own_tail_bounds_iff_outer_bounds]

/-- A closing implication, still conditional on the unresolved case reductions. -/
theorem radius_of_edges_and_own_tails {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (hedges : CandidateDSeparators P) (htails : OwnWingTailBounds P) :
    R=Six.radius :=
  radius_of_reduction P hR ((reduction_iff_edges_and_own_tails P).mpr ⟨hedges,htails⟩)

theorem radius_of_edges_and_outer_tails {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (hedges : CandidateDSeparators P) (htails : OwnWingOuterBounds P) :
    R=Six.radius :=
  radius_of_edges_and_own_tails P hR hedges ((own_tail_bounds_iff_outer_bounds P).mpr htails)

end SquaresInCircles.Six.Analytic.FixedPair
