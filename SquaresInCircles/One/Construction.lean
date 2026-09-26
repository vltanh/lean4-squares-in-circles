import SquaresInCircles.Common.Constructions

/-!
# One square: construction

The unit square centred at the disk centre, at the optimal radius `sqrt 2 / 2`.
-/
noncomputable section
namespace SquaresInCircles.One

/-- The optimal radius for one unit square: half the diagonal of the square. -/
def radius : ℝ := Real.sqrt 2 / 2

lemma radius_nonneg : 0 ≤ radius := by
  unfold radius
  positivity

lemma radius_sq : radius ^ 2 = 1 / 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  unfold radius
  linarith

/-- The square in the frame of its disk centre. -/
def centers : Fin 1 → Point := ![(0,0)]

/-- The unit square centred at the origin. -/
def model : Fin 1 → UnitSquare := fun i => axisSquare (centers i)

theorem model_packing : Packing model (0,0) radius :=
  axis_packing radius_nonneg
    (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    (by intro i; fin_cases i; norm_num [centers,radius_sq])

end SquaresInCircles.One
