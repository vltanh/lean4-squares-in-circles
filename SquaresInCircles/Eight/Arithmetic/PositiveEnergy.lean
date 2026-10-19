module

public import Mathlib

/-!
# Eight squares: rigidity from a positive energy

If `qStar + κ d² + E + ρ m ≤ q ≤ qStar` with `κ, ρ > 0` and `E, m ≥ 0`, then `q = qStar`,
`d = 0` and `m = 0` (`positive_energy_rigid`). The sharp terminal (`boundary_rigid` in
`Terminal.lean`) applies it to the lower bound of the squared radius given by the adaptive dual,
with `d` the deviation of the half-angle tangent of the tilt from that of the optimal packing,
`E` the completed squares of the centres and `m` the mismatch. Only the signs of `κ`, `ρ`, `E`
and `m` enter, not their values.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Arithmetic

/-- If `qStar` plus a positive multiple of `d²`, a nonnegative energy and a positive multiple of
a nonnegative mismatch `m` is at most `q ≤ qStar`, then `q = qStar`, `d = 0` and `m = 0`. -/
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
