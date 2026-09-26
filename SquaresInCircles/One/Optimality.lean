import SquaresInCircles.One.Construction

/-!
# One square: the lower bound

The smallest disk containing a unit square has radius `sqrt 2 / 2`, half the
diagonal. The farthest-vertex bound `phi_le_of_contained` does all the work.
-/
noncomputable section
namespace SquaresInCircles.One

/-- The farthest vertex of a square is at least half a diagonal away, and
farther unless the centre is at the disk centre. -/
lemma half_add_le_phi (a b : ℝ) : 1/2+a+b ≤ phi a b := by
  unfold phi
  nlinarith [sq_nonneg a,sq_nonneg b]

theorem squared_lower (S : Fin 1 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (1:ℝ)/2 ≤ R^2 := by
  linarith [half_add_le_phi (alpha (S 0) o) (beta (S 0) o),hp.phi_le 0,
    alpha_nonneg (S 0) o,beta_nonneg (S 0) o]

theorem optimality (S : Fin 1 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : radius ≤ R :=
  le_of_sq_le_sq (by rw [radius_sq]; exact squared_lower S o R hp) hp.1

end SquaresInCircles.One
