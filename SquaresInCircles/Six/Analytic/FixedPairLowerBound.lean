module
public import SquaresInCircles.Six.Analytic.FixedPairEndpoints

@[expose] public section

/-!
# Analytic fixed-pair envelope

The proof chain is: exact support minorant; positive force radicands; a uniform
translated-rotor curvature identity; coordinate/diagonal concavity on the six
geometric sectors; reduction to the actual rectangle/axis/diagonal vertices;
and explicit rational Taylor endpoint inequalities. There is no interval cover,
numerical derivative certificate, generated stress table or external truth flag.

The Domain hypothesis is deliberately visible. The independent analytic
classification still has to place every relevant packing in this rectangle.
This theorem does not silently discharge that domain-reduction obligation.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress

/-- The whole-domain minorant inequality, including all three sign walls. -/
theorem minorant_lower_bound {no wo : Bool} (u : Fin 4) {n w : ℝ}
    (hd : Domain no wo n w) :
    pairBase+line w+(1/1000)*|n|≤minorant no wo u n w := by
  have hg := nonnegative_of_endpoints (endpoint_condition no wo u) hd
  dsimp [gap] at hg
  linarith

/-- The exact cap/vertex pair support obeys the same common envelope. -/
theorem lower_bound {no wo : Bool} (u : Fin 4) {n w : ℝ}
    (hd : Domain no wo n w) :
    pairBase+line w+(1/1000)*|n|≤value no wo u n w :=
  (minorant_lower_bound u hd).trans (minorant_le_value no wo u n w)

/-- Equality after dropping the strictly positive |n| term forces n=0. -/
lemma north_angle_eq_zero_of_equality {no wo : Bool} {u : Fin 4} {n w : ℝ}
    (hd : Domain no wo n w) (he : value no wo u n w=pairBase+line w) : n=0 := by
  have h := lower_bound u hd
  rw [he] at h
  apply abs_eq_zero.mp
  nlinarith [abs_nonneg n]

lemma value_at_candidate (no wo : Bool) {u : Fin 4} (hu : u=0 ∨ u=3) :
    value no wo u 0 0=pairBase := by
  have hN := (pair_candidate_forces no false hu).1
  have hW := (pair_candidate_forces false wo hu).2
  rw [value,threshold_zero,northForce_zero,westForce_zero,hN,hW,penalty_zero,
    candidate_north_exact_support,candidate_west_exact_support,sub_zero]
  exact pairBase_vertex_identity

/-- The two strict alternative axes cannot occur in an equality configuration. -/
lemma equality_sources_at_origin (no wo : Bool) (u : Fin 4)
    (he : value no wo u 0 0=pairBase) : u=0 ∨ u=3 := by
  by_contra hu
  have halt : u=1 ∨ u=2 := by omega
  have hpos := alternate_gap_origin no wo halt
  have hupper := minorant_le_value no wo u 0 0
  rw [he] at hupper
  dsimp [gap] at hpos
  norm_num [line] at hpos
  linarith

end SquaresInCircles.Six.Analytic.FixedPair
