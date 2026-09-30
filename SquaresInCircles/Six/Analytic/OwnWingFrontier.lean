module
public import SquaresInCircles.Six.Analytic.CoupledWingBudgetSharp
public import SquaresInCircles.Six.Analytic.CardinalSouthTail.Geometry
public import SquaresInCircles.Six.Analytic.LowDWestSource.Geometry
public import SquaresInCircles.Six.Analytic.MixedCardinalWest.Geometry

@[expose] public section

/-!
# Smaller domains for the still-open mixed-source exclusions

The full cardinal-W missing-south branch is now excluded analytically.
For a missing west wing, the existing one-radian W/D gap and the sharper
OWN/OWN sum give d-s>1/25 whenever both wings are OWN. This strict reserve
is obtained in the original normalized frame; no second reflection changes
the diagonal half-window.

These are necessary consequences of a hypothetical missing wing, not claims
that every remaining OWN configuration has been excluded. The unrestricted
south upper tail remains a separate obligation. Compilation is unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

/-- The former cardinal-W / large-OWN-S exception is no longer part of the frontier. -/
lemma MissingSouthWing.west_own {R : ℝ} {P : NormalizedPacking R}
    (h : MissingSouthWing P) : P.ownBits 2=true :=
  CardinalSouthTail.missing_south_requires_own_west h

/-- A missing west wing with cardinal W must have OWN S. -/
lemma MissingWestWing.south_own_of_cardinal_west {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) (hW : P.ownBits 2=false) : P.ownBits 4=true := by
  cases hS : P.ownBits 4
  · exact False.elim (MixedCardinalWest.not_missing_west P hW hS h)
  · exact hS

/-- The actual D-sourced west gap, expressed in the helper coordinates. -/
lemma MissingWestWing.diagonal_minus_west_gt_one {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : 1 < P.diagonalAngle-P.helperAngle 2 := by
  have hg := DW_Dsecondary_gap_gt_one P h.from_diagonal
  rw [P.phase_from_deviation 2] at hg
  dsimp [NormalizedPacking.diagonalAngle]
  linarith

/-- The two OWN wings leave a strict positive d-s reserve in the missing-west case. -/
lemma MissingWestWing.own_south_phase_reserve {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) (hW : P.ownBits 2=true) (hS : P.ownBits 4=true) :
    1/25 < P.diagonalAngle-P.helperAngle 4 := by
  have hgap := h.diagonal_minus_west_gt_one
  have hsum := normalized_own_wing_angle_sum_lt_twenty_four_twenty_fifths P hW hS
  linarith

/-- A compact summary for the two-OWN missing-west branch, with no assumed tail. -/
theorem MissingWestWing.own_domain {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) (hW : P.ownBits 2=true) (hS : P.ownBits 4=true) :
    3/5 < P.diagonalAngle ∧
    1-P.diagonalAngle < -P.helperAngle 2 ∧
    P.helperAngle 4-P.helperAngle 2 < 24/25 ∧
    P.helperAngle 4 < P.diagonalAngle-1/25 := by
  exact ⟨h.diagonal_gt_three_fifths,
    by linarith [h.diagonal_minus_west_gt_one],
    normalized_own_wing_angle_sum_lt_twenty_four_twenty_fifths P hW hS,
    by linarith [h.own_south_phase_reserve hW hS]⟩

end SquaresInCircles.Six.Analytic
