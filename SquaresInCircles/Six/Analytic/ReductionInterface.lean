import SquaresInCircles.Six.Analytic.SecondaryReduction
import SquaresInCircles.Six.Analytic.FixedCandidateClosure
import SquaresInCircles.Six.Analytic.SouthOwnLowerTail
import SquaresInCircles.Six.Analytic.CandidateWestTail.Geometry

/-!
# Exact remaining obligations of the analytic reduction

Normalization supplies the E/N and cardinal-wing ranges and d>1/2. The lower
OWN-S tail is proved independently. The new four-edge analytic stress proves
the OWN-W outer tail once both actual candidate D separators are available.
Thus only the two missing-wing exclusions and the upper OWN-S tail remain as
independent obligations. The older interfaces are retained for compatibility.

These equivalences do not assert the unresolved statements or insert them into
Packing. No generated fixed-row theorem discharges an obligation here.
Compilation and kernel acceptance are deferred.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Normalization

/-- Original interface retained for earlier conditional closure theorems. -/
def OwnWingTailBounds {R : ℝ} (P : NormalizedPacking R) : Prop :=
  (P.ownBits 2=true → -11/25 ≤ P.helperAngle 2) ∧
  (P.ownBits 4=true → -2/25 ≤ P.helperAngle 4 ∧ P.helperAngle 4 ≤ 11/25)

def OwnWingOuterBounds {R : ℝ} (P : NormalizedPacking R) : Prop :=
  (P.ownBits 2=true → -11/25 ≤ P.helperAngle 2) ∧
  (P.ownBits 4=true → P.helperAngle 4 ≤ 11/25)

/-- The only tail still required after both candidate D edges are proved. -/
def SouthOuterBound {R : ℝ} (P : NormalizedPacking R) : Prop :=
  P.ownBits 4=true → P.helperAngle 4 ≤ 11/25

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

theorem reduction_iff_edges_and_own_tails {R : ℝ} (P : NormalizedPacking R) :
    ReductionHypotheses P ↔ (CandidateDSeparators P ∧ OwnWingTailBounds P) := by
  constructor
  · intro h
    exact ⟨h.diagonal_edges,(northwest_domain_iff_own_tail P).mp h.northwest_domain,
      (eastsouth_domain_iff_own_tail P).mp h.eastsouth_domain⟩
  · rintro ⟨hedges,hW,hS⟩
    exact ⟨hedges,(northwest_domain_iff_own_tail P).mpr hW,
      (eastsouth_domain_iff_own_tail P).mpr hS,(normalized_diagonal_gt_half P).le⟩

theorem reduction_iff_remaining_obligations {R : ℝ} (P : NormalizedPacking R) :
    ReductionHypotheses P ↔
      (¬ MissingWestWing P ∧ ¬ MissingSouthWing P) ∧ OwnWingTailBounds P := by
  rw [reduction_iff_edges_and_own_tails,candidate_edges_iff_no_missing_wing]

theorem reduction_iff_four_obligations {R : ℝ} (P : NormalizedPacking R) :
    ReductionHypotheses P ↔
      (¬ MissingWestWing P ∧ ¬ MissingSouthWing P) ∧ OwnWingOuterBounds P := by
  rw [reduction_iff_remaining_obligations,own_tail_bounds_iff_outer_bounds]

/-- The west outer tail is derived here, not supplied by the caller. -/
theorem reduction_iff_edges_and_south_tail {R : ℝ} (P : NormalizedPacking R) :
    ReductionHypotheses P ↔ CandidateDSeparators P ∧ SouthOuterBound P := by
  rw [reduction_iff_edges_and_own_tails]
  constructor
  · rintro ⟨hedges,hW,hS⟩
    exact ⟨hedges,fun hs => (hS hs).2⟩
  · rintro ⟨hedges,hS⟩
    refine ⟨hedges,?_,?_⟩
    · intro hW
      exact (CandidateWestTail.normalized_own_west_tail_of_edges P hedges hW).le
    · intro hs
      exact ⟨(normalized_own_south_lower_tail P hs).le,hS hs⟩

/-- Three independent statements remain. This is an equivalence, not a claim
that either mixed source exclusion or the south upper tail has been proved. -/
theorem reduction_iff_three_obligations {R : ℝ} (P : NormalizedPacking R) :
    ReductionHypotheses P ↔
      (¬ MissingWestWing P ∧ ¬ MissingSouthWing P) ∧ SouthOuterBound P := by
  rw [reduction_iff_edges_and_south_tail,candidate_edges_iff_no_missing_wing]

theorem radius_of_edges_and_own_tails {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (hedges : CandidateDSeparators P) (htails : OwnWingTailBounds P) :
    R=Six.radius :=
  radius_of_reduction P hR ((reduction_iff_edges_and_own_tails P).mpr ⟨hedges,htails⟩)

theorem radius_of_edges_and_outer_tails {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (hedges : CandidateDSeparators P) (htails : OwnWingOuterBounds P) :
    R=Six.radius :=
  radius_of_edges_and_own_tails P hR hedges ((own_tail_bounds_iff_outer_bounds P).mpr htails)

theorem radius_of_edges_and_south_tail {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (hedges : CandidateDSeparators P) (htail : SouthOuterBound P) :
    R=Six.radius :=
  radius_of_reduction P hR ((reduction_iff_edges_and_south_tail P).mpr ⟨hedges,htail⟩)

end SquaresInCircles.Six.Analytic.FixedPair
