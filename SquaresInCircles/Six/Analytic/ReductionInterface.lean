import SquaresInCircles.Six.Analytic.SecondaryReduction
import SquaresInCircles.Six.Analytic.FixedCandidateClosure

/-!
# Remove already-proved facts from the final reduction obligation

The E/N pair ranges, the complete cardinal W/S ranges, the OWN-W upper bound,
and d>1/2 already follow analytically from normalization and source geometry.
Only the three explicitly stated OWN-wing tail inequalities remain in the pair
Domain premise. The equivalences below prevent those missing tails from being
hidden among facts that have already been established.

These are exact interface theorems, not proofs of the two mixed-source
exclusions or of the three remaining tail inequalities. They do not add any
assumption to Packing or NormalizedPacking, and no old fixed-row theorem is
imported to instantiate the unresolved obligations.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Normalization

/-- The remaining individual bounds, with the canonical OWN hypotheses kept. -/
def OwnWingTailBounds {R : ℝ} (P : NormalizedPacking R) : Prop :=
  (P.ownBits 2=true → -11/25 ≤ P.helperAngle 2) ∧
  (P.ownBits 4=true → -2/25 ≤ P.helperAngle 4 ∧ P.helperAngle 4 ≤ 11/25)

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

/-- For N/W only the negative OWN-W tail remains; its positive side has the
stronger strict sign already proved by canonical separator preference. -/
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

/-- Reflection of the scalar E/S calculation turns the OWN-S interval into
exactly these two signed inequalities; no new global reflection is used. -/
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

/-- This states the exact remaining mathematical work. In particular neither
normalization nor d>1/2 is left as an unproved input to the final interface. -/
theorem reduction_iff_edges_and_own_tails {R : ℝ} (P : NormalizedPacking R) :
    ReductionHypotheses P ↔ (CandidateDSeparators P ∧ OwnWingTailBounds P) := by
  constructor
  · intro h
    exact ⟨h.diagonal_edges,(northwest_domain_iff_own_tail P).mp h.northwest_domain,
      (eastsouth_domain_iff_own_tail P).mp h.eastsouth_domain⟩
  · rintro ⟨hedges,hW,hS⟩
    exact ⟨hedges,(northwest_domain_iff_own_tail P).mpr hW,
      (eastsouth_domain_iff_own_tail P).mpr hS,(normalized_diagonal_gt_half P).le⟩

/-- The source alternatives are the genuine missing-wing cases, not merely
arbitrary choices of a separating index at a tie. This does not exclude them. -/
theorem reduction_iff_remaining_obligations {R : ℝ} (P : NormalizedPacking R) :
    ReductionHypotheses P ↔
      (¬ MissingWestWing P ∧ ¬ MissingSouthWing P) ∧ OwnWingTailBounds P := by
  rw [reduction_iff_edges_and_own_tails,candidate_edges_iff_no_missing_wing]

/-- A usable closing implication once the remaining substantive inequalities
are provided. No unconditional radius conclusion is asserted by this lemma. -/
theorem radius_of_edges_and_own_tails {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (hedges : CandidateDSeparators P) (htails : OwnWingTailBounds P) :
    R=Six.radius :=
  radius_of_reduction P hR ((reduction_iff_edges_and_own_tails P).mpr ⟨hedges,htails⟩)

end SquaresInCircles.Six.Analytic.FixedPair
