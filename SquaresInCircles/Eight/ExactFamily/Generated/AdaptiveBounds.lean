module

public import SquaresInCircles.Eight.ExactFamily.Generated.AdaptiveFormula
public import SquaresInCircles.Eight.ExactFamily.IntervalEnclosure

/-!
# Uniform estimates along the stationary curve

There are 256 closed boxes but only seven kinds of bound. The boxes and
formulas are retained unchanged; the interval calculation and its soundness
argument are shared. In particular, strict derivative signs at both ends
are still required before an adaptive stationary point is admitted.

The constants below are named quantitative witnesses, not definitions of
the optimal geometry. These decision proofs have not been executed in Lean.
-/

@[expose] public section
namespace SquaresInCircles.Eight.ExactFamily.AdaptiveGenerated
open Arithmetic Generated IntervalEnclosure

/-- The same precision as the original adaptive-box generator. -/
def adaptivePrecision : ℕ := 100

def derivativeBuffer : ℚ := 1 / 10^6
def reserveFloor : ℚ := 56793 / 5000000
def weightCeiling : ℚ := 4209 / 5000
def quadraticCeiling : ℚ := 232 / 25
def cubicCeiling : ℚ := 3 / 2

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem lower_checked : ∀ i : Fin 256,
    boundedAt adaptivePrecision (lowerBoxes i) FyFormula ⟨-1,-derivativeBuffer⟩ = true := by decide

theorem upper_checked : ∀ i : Fin 256,
    boundedAt adaptivePrecision (upperBoxes i) FyFormula ⟨derivativeBuffer,1⟩ = true := by decide

theorem reserves_checked : ∀ i : Fin 256, ∀ j : Fin 9,
    boundedAt adaptivePrecision (graphBoxes i) (reserveFormula j) ⟨reserveFloor,2⟩ = true := by decide

theorem weights_checked : ∀ i : Fin 256, ∀ j : Fin 7,
    boundedAt adaptivePrecision (graphBoxes i) (lambdaFormula j) ⟨1/100,weightCeiling⟩ = true := by decide

theorem hTwo_checked : ∀ i : Fin 256,
    boundedAt adaptivePrecision (graphBoxes i) hTwoFormula ⟨-29/20,-7/5⟩ = true := by decide

theorem quadratic_checked : ∀ i : Fin 256,
    boundedAt adaptivePrecision (graphBoxes i) quadraticFormula ⟨0,quadraticCeiling⟩ = true := by decide

theorem cubic_checked : ∀ i : Fin 256,
    boundedAt adaptivePrecision (graphBoxes i) cubicFormula ⟨0,cubicCeiling⟩ = true := by decide

noncomputable section

theorem lower_sign (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (lowerBoxes i).Mem env) : FyFormula.eval env < 0 := by
  have h := (boundedAt_sound (lower_checked i) he).2
  exact lt_of_le_of_lt h (by norm_num [derivativeBuffer])

theorem upper_sign (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (upperBoxes i).Mem env) : 0 < FyFormula.eval env := by
  have h := (boundedAt_sound (upper_checked i) he).1
  exact lt_of_lt_of_le (by norm_num [derivativeBuffer]) h

theorem reserve_bound (i : Fin 256) (j : Fin 9) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) :
    (56793/5000000 : ℝ) ≤ (reserveFormula j).eval env := by
  simpa [reserveFloor] using (boundedAt_sound (reserves_checked i j) he).1

theorem weight_bound (i : Fin 256) (j : Fin 7) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) :
    (lambdaFormula j).eval env ≤ 4209/5000 := by
  simpa [weightCeiling] using (boundedAt_sound (weights_checked i j) he).2

theorem hTwo_bound (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) :
    -(29/20:ℝ) ≤ hTwoFormula.eval env ∧ hTwoFormula.eval env ≤ -(7/5) := by
  simpa [QInterval.Mem] using boundedAt_sound (hTwo_checked i) he

theorem quadratic_bound (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) : quadraticFormula.eval env ≤ 232/25 := by
  simpa [quadraticCeiling] using (boundedAt_sound (quadratic_checked i) he).2

theorem cubic_bound (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) : cubicFormula.eval env ≤ 3/2 := by
  simpa [cubicCeiling] using (boundedAt_sound (cubic_checked i) he).2

end SquaresInCircles.Eight.ExactFamily.AdaptiveGenerated
