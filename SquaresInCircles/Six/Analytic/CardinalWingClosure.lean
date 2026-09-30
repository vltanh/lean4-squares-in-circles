module
public import SquaresInCircles.Six.Analytic.MixedCardinalWest.Geometry
public import SquaresInCircles.Six.Analytic.MixedCardinalSouth.Geometry
public import SquaresInCircles.Six.Analytic.ReductionInterface

@[expose] public section

/-!
# Complete analytic reduction for two cardinal wings

Both mixed source alternatives are now excluded in this central-bit branch.
Its pair-domain bounds come directly from the cardinal angle estimates, so no
OWN-tail assumption remains. The resulting radius statement uses the analytic
fixed-pair closure, not the historical fixed-row or pair-certificate route.

This is a completed branch, not the unrestricted endpoint: a packing with one
or both wings canonically OWN still requires the remaining reductions.
Compilation and kernel acceptance are deferred.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Normalization

/-- Both candidate D edges are forced when W and S are cardinal. -/
theorem candidate_edges_of_cardinal_wings {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=false) : CandidateDSeparators P := by
  refine ⟨MixedCardinalWest.west_wing P hW hS,?_⟩
  apply MixedCardinalSouth.south_wing P hW
  have hs := (abs_lt.mp (P.cardinal_angle 4 hS)).2
  linarith

/-- In this bit branch the two remaining OWN-tail implications are vacuous,
not additional facts assumed of a normalized packing. -/
theorem outer_tails_of_cardinal_wings {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=false) : OwnWingOuterBounds P := by
  constructor
  · intro h
    simp only [hW,Bool.false_eq_true] at h
  · intro h
    simp only [hS,Bool.false_eq_true] at h

/-- An actual inhabitant of the final reduction data for the both-cardinal
branch, with no generated stress rows or external arithmetic premises. -/
theorem reduction_of_cardinal_wings {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=false) : ReductionHypotheses P := by
  apply (reduction_iff_edges_and_own_tails P).mpr
  exact ⟨candidate_edges_of_cardinal_wings P hW hS,
    (own_tail_bounds_iff_outer_bounds P).mpr (outer_tails_of_cardinal_wings P hW hS)⟩

/-- Source-level closure of the complete both-cardinal wing branch. -/
theorem radius_of_cardinal_wings {R : ℝ} (P : NormalizedPacking R)
    (hR : R^2 ≤ Six.qStar) (hW : P.ownBits 2=false) (hS : P.ownBits 4=false) :
    R=Six.radius :=
  radius_of_reduction P hR (reduction_of_cardinal_wings P hW hS)

/-- Any still-missing west wing has at least one OWN central choice. -/
theorem missing_west_requires_own {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : P.ownBits 2=true ∨ P.ownBits 4=true := by
  cases hW : P.ownBits 2
  · cases hS : P.ownBits 4
    · exact False.elim (MixedCardinalWest.not_missing_west P hW hS h)
    · exact Or.inr hS
  · exact Or.inl hW

/-- For a missing south wing, a cardinal W forces the genuinely large OWN-S
tail. This locates the unresolved region without assuming its exclusion. -/
theorem missing_south_requires_own_or_large_tail {R : ℝ} {P : NormalizedPacking R}
    (h : MissingSouthWing P) :
    P.ownBits 2=true ∨ (P.ownBits 4=true ∧ 12/25 < P.helperAngle 4) := by
  cases hW : P.ownBits 2
  · exact Or.inr (MixedCardinalSouth.remaining_case_requires_south_tail h hW)
  · exact Or.inl hW

end SquaresInCircles.Six.Analytic.FixedPair
