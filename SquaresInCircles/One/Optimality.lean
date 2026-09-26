import SquaresInCircles.One.Construction

/-!
# One square: the lower bound

The smallest disk containing a unit square has radius `sqrt 2 / 2`, half the
diagonal. The farthest-vertex bound `phi_le_of_contained` does all the work.
-/
noncomputable section
namespace SquaresInCircles.One

/-- The farthest vertex of a square is at least half a diagonal away. -/
lemma half_le_phi {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 1/2 ≤ phi a b := by
  unfold phi
  nlinarith

theorem squared_lower (S : Fin 1 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (1:ℝ)/2 ≤ R^2 :=
  (half_le_phi (alpha_nonneg _ _) (beta_nonneg _ _)).trans (hp.phi_le 0)

theorem optimality (S : Fin 1 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : radius ≤ R :=
  le_of_sq_le_sq (by rw [radius_sq]; exact squared_lower S o R hp) hp.1

end SquaresInCircles.One
