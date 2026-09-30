module
public import SquaresInCircles.Common.Constructions

@[expose] public section

/-!
# Two squares: construction

The 2 × 1 rectangle centred at the disk centre packs the disk of the optimal
radius `sqrt 5 / 2`. The radius and the model are defined with the statement,
in `Geometry.lean`.
-/
noncomputable section
namespace SquaresInCircles.Two

lemma radius_nonneg : 0 ≤ radius := by unfold radius; positivity

lemma radius_sq : radius ^ 2 = 5 / 4 := by
  rw [radius,div_pow,Real.sq_sqrt (by norm_num)]; norm_num

theorem model_packing : Packing model (0,0) radius :=
  axis_packing radius_nonneg
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [centers,AxisSeparated] at *)
    (by intro i; fin_cases i <;> norm_num [centers,radius_sq])

end SquaresInCircles.Two
