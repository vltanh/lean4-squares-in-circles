import SquaresInCircles.Common.Constructions

/-!
# Two squares: construction

The 2 × 1 rectangle centred at the disk centre, at the optimal radius `sqrt 5 /
2`.
-/
noncomputable section
namespace SquaresInCircles.Two

/-- The optimal radius for two unit squares: half the diagonal of the 2 × 1 rectangle. -/
def radius : ℝ := Real.sqrt 5 / 2

lemma radius_nonneg : 0 ≤ radius := by
  unfold radius
  positivity

lemma radius_sq : radius ^ 2 = 5 / 4 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold radius
  linarith

/-- The rectangle in the frame of its disk centre. -/
def centers : Fin 2 → Point := ![(-1/2,0),(1/2,0)]

/-- The 2 × 1 rectangle, centred at the origin. -/
def model : Fin 2 → UnitSquare := fun i => axisSquare (centers i)

theorem model_packing : Packing model (0,0) radius :=
  axis_packing radius_nonneg
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [centers,AxisSeparated] at *)
    (by intro i; fin_cases i <;> norm_num [centers,radius_sq])

end SquaresInCircles.Two
