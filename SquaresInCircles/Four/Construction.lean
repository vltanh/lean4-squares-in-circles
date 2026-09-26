import SquaresInCircles.Common.Constructions

/-!
# Four squares: construction

The 2×2 block: four unit squares at the optimal radius `sqrt 2`.
-/
noncomputable section
namespace SquaresInCircles.Four

/-- The optimal radius for four unit squares: half the diagonal of the 2×2 block. -/
def radius : ℝ := Real.sqrt 2

lemma radius_nonneg : 0 ≤ radius := by
  unfold radius
  positivity

lemma radius_sq : radius ^ 2 = 2 := by
  unfold radius
  exact Real.sq_sqrt (by norm_num)

/-- The block in the frame of its disk centre. -/
def centers : Fin 4 → Point := ![(1/2,1/2),(-1/2,1/2),(-1/2,-1/2),(1/2,-1/2)]

/-- The 2×2 block, centred at the origin. -/
def model : Fin 4 → UnitSquare := fun i => axisSquare (centers i)

theorem model_packing : Packing model (0,0) radius :=
  axis_packing radius_nonneg
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [centers,AxisSeparated] at *)
    (by intro i; fin_cases i <;> norm_num [centers,radius_sq])

end SquaresInCircles.Four
