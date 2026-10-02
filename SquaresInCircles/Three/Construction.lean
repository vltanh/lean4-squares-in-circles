module

public import SquaresInCircles.Common.Constructions

/-!
# Three squares: construction

The T: three unit squares that pack the disk of the optimal radius
`5 * sqrt 17 / 16` about the origin. The radius and the model are defined with
the statement, in `Geometry.lean`.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Three

lemma radius_nonneg : 0 ≤ radius := by
  unfold radius
  positivity

lemma radius_sq : radius ^ 2 = 425 / 256 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  unfold radius
  linarith

theorem model_packing : Packing model (0,0) radius :=
  axis_packing radius_nonneg
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [centers,AxisSeparated] at *)
    (by intro i; fin_cases i <;> norm_num [centers,radius_sq])

end SquaresInCircles.Three
