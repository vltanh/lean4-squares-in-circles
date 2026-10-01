import SquaresInCircles.Six.Analytic.SecondaryReduction
import SquaresInCircles.Six.Analytic.FixedCandidateClosure
import SquaresInCircles.Six.Analytic.SouthOwnLowerTail
import SquaresInCircles.Six.Analytic.CandidateWestTail.Geometry

/-!
# The reduction hypotheses

`ReductionHypotheses P` asks that W–D and D–S be separated along the secondary
axes of W and of S, as in the model, that the angles of the pairs N, W and E, S
lie in their domains, and that `d ≥ 1/2`. The normalization gives `d > 1/2`
and bounds the angles of E and N, and of W and S when they are separated from
C along the matching sides; so the hypotheses come down to the two separations
and bounds on the angles of W and S when they are separated along their own
axes. The bound `w ≥ -11/25` follows from the two separations
(`CandidateWestTail`), and `s ≥ -2/25` holds in every normalized packing, which
leaves `s ≤ 11/25` (`reduction_iff_edges_and_south_tail`).
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Normalization

/-- The angle bounds for W and S when they are separated from C along their own
axes: `w ≥ -11/25` and `-2/25 ≤ s ≤ 11/25`. -/
def OwnWingTailBounds {R : ℝ} (P : NormalizedPacking R) : Prop :=
  (P.ownBits 2=true → -11/25 ≤ P.helperAngle 2) ∧
  (P.ownBits 4=true → -2/25 ≤ P.helperAngle 4 ∧ P.helperAngle 4 ≤ 11/25)

/-- The bound `s ≤ 11/25` when S is separated from C along its own axis. -/
def SouthOuterBound {R : ℝ} (P : NormalizedPacking R) : Prop :=
  P.ownBits 4=true → P.helperAngle 4 ≤ 11/25

lemma north_pair_range {R : ℝ} (P : NormalizedPacking R) :
    if P.ownBits 1 then -3/10 ≤ P.helperAngle 1 ∧ P.helperAngle 1 ≤ 5/12
    else -203/1000 ≤ P.helperAngle 1 ∧ P.helperAngle 1 ≤ 203/1000 := by
  cases h : P.ownBits 1
  · have hn := abs_lt.mp (P.north_cardinal_angle_203 h)
    simp only [Bool.false_eq_true,ite_false]
    constructor <;> linarith [hn.1,hn.2]
  · have hn := P.helper_windows.2.1
    simpa only [h,ite_true] using And.intro hn.1.le hn.2.le

lemma east_pair_range {R : ℝ} (P : NormalizedPacking R) :
    if P.ownBits 0 then -3/10 ≤ -P.helperAngle 0 ∧ -P.helperAngle 0 ≤ 5/12
    else -203/1000 ≤ -P.helperAngle 0 ∧ -P.helperAngle 0 ≤ 203/1000 := by
  cases h : P.ownBits 0
  · have he := abs_lt.mp (P.east_cardinal_angle_203 h)
    simp only [Bool.false_eq_true,ite_false]
    constructor <;> linarith [he.1,he.2]
  · have he := P.helper_windows.1
    simp only [ite_true]
    constructor <;> linarith [he.1,he.2]

/-- The angles of N and W lie in the domain exactly when `w ≥ -11/25` for W
separated from C along its own axis. -/
theorem northwest_domain_iff_own_tail {R : ℝ} (P : NormalizedPacking R) :
    Domain (P.ownBits 1) (P.ownBits 2) (P.helperAngle 1) (P.helperAngle 2) ↔
      (P.ownBits 2=true → -11/25 ≤ P.helperAngle 2) := by
  constructor
  · intro h hW
    have hw := h.2
    simp only [hW,ite_true] at hw
    exact hw.1
  · intro htail
    refine ⟨north_pair_range P,?_⟩
    cases hW : P.ownBits 2
    · have hw := abs_lt.mp (P.cardinal_angle 2 hW)
      simp only [Bool.false_eq_true,ite_false]
      constructor <;> linarith [hw.1,hw.2]
    · have hneg := canonical_own_west_negative P hW
      simp only [ite_true]
      exact ⟨htail hW,by linarith⟩

/-- The angles of E and S, with signs reversed as in the reflection in the
diagonal, lie in the domain exactly when `-2/25 ≤ s ≤ 11/25` for S separated
from C along its own axis. -/
theorem eastsouth_domain_iff_own_tail {R : ℝ} (P : NormalizedPacking R) :
    Domain (P.ownBits 0) (P.ownBits 4) (-P.helperAngle 0) (-P.helperAngle 4) ↔
      (P.ownBits 4=true → -2/25 ≤ P.helperAngle 4 ∧ P.helperAngle 4 ≤ 11/25) := by
  constructor
  · intro h hS
    have hs := h.2
    simp only [hS,ite_true] at hs
    constructor <;> linarith [hs.1,hs.2]
  · intro htail
    refine ⟨east_pair_range P,?_⟩
    cases hS : P.ownBits 4
    · have hs := abs_lt.mp (P.cardinal_angle 4 hS)
      simp only [Bool.false_eq_true,ite_false]
      constructor <;> linarith [hs.1,hs.2]
    · have hs := htail hS
      simp only [ite_true]
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

/-- The reduction hypotheses hold exactly when W–D and D–S are separated as in
the model and `SouthOuterBound` holds. -/
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

end SquaresInCircles.Six.Analytic.FixedPair
