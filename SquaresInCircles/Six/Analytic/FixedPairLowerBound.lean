import SquaresInCircles.Six.Analytic.FixedPairEndpoints

/-!
# The lower bound for the pair

On the whole domain the value of the pair stress is at least
`pairBase + line w + |n|/1000`. The gap of the minorant is concave along the
slices of each sign sector and nonnegative at the endpoints, so it is
nonnegative everywhere, and the minorant is below the value. At zero angle the
value is `pairBase` only if the edge N–W is along source `0` or `3`.
-/
noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress

/-- On the domain the minorant is at least `pairBase + line w + |n|/1000`. -/
theorem minorant_lower_bound {no wo : Bool} (u : Fin 4) {n w : ℝ}
    (hd : Domain no wo n w) :
    pairBase+line w+(1/1000)*|n|≤ minorant no wo u n w := by
  have hg := nonnegative_of_endpoints (endpoint_condition no wo u) hd
  dsimp [gap] at hg
  linarith

/-- On the domain the value of the pair stress is at least
`pairBase + line w + |n|/1000`. -/
theorem lower_bound {no wo : Bool} (u : Fin 4) {n w : ℝ}
    (hd : Domain no wo n w) :
    pairBase+line w+(1/1000)*|n|≤value no wo u n w :=
  (minorant_lower_bound u hd).trans (minorant_le_value no wo u n w)

/-- If the value at zero angle is `pairBase`, the edge N–W is along source `0`
or `3`. -/
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
