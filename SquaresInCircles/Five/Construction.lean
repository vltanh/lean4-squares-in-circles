import SquaresInCircles.Common.Constructions

/-!
# Five squares: construction

The plus: five unit squares that pack the disk of the optimal radius
`sqrt (5/2)`. The radius and the model are defined with the statement, in
`Geometry.lean`.
-/
noncomputable section
namespace SquaresInCircles.Five

lemma radius_nonneg : 0 ≤ radius := by
  unfold radius
  positivity

lemma radius_sq : radius ^ 2 = 5 / 2 := by
  unfold radius
  exact Real.sq_sqrt (by norm_num)

theorem model_packing : Packing model (0,0) radius :=
  axis_packing radius_nonneg
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [centers,AxisSeparated] at *)
    (by intro i; fin_cases i <;> norm_num [centers,radius_sq])

end SquaresInCircles.Five
