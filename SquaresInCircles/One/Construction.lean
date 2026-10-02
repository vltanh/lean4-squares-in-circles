module

public import SquaresInCircles.Common.Constructions

/-!
# One square: construction

The unit square centred at the disk centre packs the disk of the optimal radius
`sqrt 2 / 2`. The radius and the model are defined with the statement, in
`Geometry.lean`.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.One

lemma radius_nonneg : 0 ≤ radius := halfDiagonal_pos.le

lemma radius_sq : radius ^ 2 = 1 / 2 := halfDiagonal_sq

theorem model_packing : Packing model (0,0) radius :=
  axis_packing radius_nonneg
    (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    (by intro i; fin_cases i; norm_num [centers,radius_sq])

end SquaresInCircles.One
