module

public import Mathlib

/-!
# Rigidity from a positive energy

The numerical certificates are needed only to establish positivity of the
coefficients. The equality argument itself is independent of their values.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Arithmetic

/-- Below the candidate value there is no room for a positive error term.
This statement has no numerical approximation to the sharp configuration. -/
theorem positive_energy_rigid {q qStar κ ρ displacement energy mismatch : ℝ}
    (hκ : 0 < κ) (hρ : 0 < ρ) (he : 0 ≤ energy) (hm : 0 ≤ mismatch)
    (hq : q ≤ qStar)
    (hbound : qStar + κ * displacement ^ 2 + energy + ρ * mismatch ≤ q) :
    q = qStar ∧ displacement = 0 ∧ mismatch = 0 := by
  have hd : 0 ≤ κ * displacement ^ 2 := mul_nonneg hκ.le (sq_nonneg _)
  have hs : 0 ≤ ρ * mismatch := mul_nonneg hρ.le hm
  have hdzero : κ * displacement ^ 2 = 0 := by linarith
  have hszero : ρ * mismatch = 0 := by linarith
  have hsq : displacement ^ 2 = 0 :=
    (mul_eq_zero.mp hdzero).resolve_left (ne_of_gt hκ)
  refine ⟨by linarith, ?_, (mul_eq_zero.mp hszero).resolve_left (ne_of_gt hρ)⟩
  nlinarith [sq_nonneg displacement]

end SquaresInCircles.Eight.Arithmetic
