module

public import SquaresInCircles.Common.Constructions

/-!
# Four squares: construction

The 2×2 block: four unit squares that pack the disk of the optimal radius
`sqrt 2`. The radius and the model are defined with the statement, in
`Geometry.lean`.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Four

lemma radius_nonneg : 0 ≤ radius := by
  unfold radius
  positivity

lemma radius_sq : radius ^ 2 = 2 := by
  unfold radius
  exact Real.sq_sqrt (by norm_num)

theorem model_packing : Packing model (0,0) radius :=
  axis_packing radius_nonneg
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [centers,AxisSeparated] at *)
    (by intro i; fin_cases i <;> norm_num [centers,radius_sq])

end SquaresInCircles.Four
