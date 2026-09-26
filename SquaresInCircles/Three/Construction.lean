import SquaresInCircles.Common.Constructions

/-!
# Three squares: construction

The T: three unit squares at the optimal radius `5 * sqrt 17 / 16`, with the
disk centre at the origin.
-/
noncomputable section
namespace SquaresInCircles.Three

/-- The optimal radius for three unit squares: the distance from the disk centre
to the corners of the T. -/
def radius : ℝ := 5 * Real.sqrt 17 / 16

lemma radius_nonneg : 0 ≤ radius := by
  unfold radius
  positivity

lemma radius_sq : radius ^ 2 = 425 / 256 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  unfold radius
  linarith

/-- The T in the frame of its disk centre: two squares side by side, and one
centred on top of them. -/
def centers : Fin 3 → Point := ![(-1/2,-5/16),(1/2,-5/16),(0,11/16)]

def model : Fin 3 → UnitSquare := fun i => axisSquare (centers i)

theorem model_packing : Packing model (0,0) radius :=
  axis_packing radius_nonneg
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [centers,AxisSeparated] at *)
    (by intro i; fin_cases i <;> norm_num [centers,radius_sq])

end SquaresInCircles.Three
