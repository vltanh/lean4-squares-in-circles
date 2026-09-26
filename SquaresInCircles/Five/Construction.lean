import SquaresInCircles.Common.Constructions

/-!
# Five squares: construction

The plus: five unit squares at the optimal radius `sqrt (5/2)`.
-/
noncomputable section
namespace SquaresInCircles.Five

/-- The optimal radius for five unit squares: the distance from the disk centre
to the outer corners of the plus. -/
def radius : ℝ := Real.sqrt (5 / 2)

lemma radius_nonneg : 0 ≤ radius := by
  unfold radius
  positivity

lemma radius_sq : radius ^ 2 = 5 / 2 := by
  unfold radius
  exact Real.sq_sqrt (by norm_num)

/-- The plus in the frame of its disk centre. -/
def centers : Fin 5 → Point := ![(0,0),(1,0),(0,1),(-1,0),(0,-1)]

/-- The plus, centred at the origin. -/
def model : Fin 5 → UnitSquare := fun i => axisSquare (centers i)

theorem model_packing : Packing model (0,0) radius :=
  axis_packing radius_nonneg
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [centers,AxisSeparated] at *)
    (by intro i; fin_cases i <;> norm_num [centers,radius_sq])

end SquaresInCircles.Five
