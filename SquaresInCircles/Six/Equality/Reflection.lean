import SquaresInCircles.Six.Normalization.Complete
import SquaresInCircles.Six.Normalization.CentralSquare

/-!
# The diagonal reflection of the model

The model is symmetric under the reflection in the diagonal
`y = x`, which exchanges N with E and W with S and maps C and D to themselves,
so its reflection is congruent to it by a relabelling alone. Reflecting both
sides of a congruence gives a congruence with the opposite rotation
(`congruent_diagonal`). Hence a configuration congruent to `T` or to the
reflection of `T`, as the normalization produces, is congruent to the model
whenever `T` is.
-/

noncomputable section
namespace SquaresInCircles.Six.Equality

/-- The relabelling of the model by the diagonal reflection: in the order
C, N, E, W, S, D it exchanges N with E and W with S. -/
def mirror : Equiv.Perm (Fin 6) where
  toFun := ![0,2,1,4,3,5]
  invFun := ![0,2,1,4,3,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The reflection of a square of the model is the square with the exchanged
label. -/
lemma model_reflection_open (i : Fin 6) (p : Point) :
    openSquare (reflectDiagonalSquare (model (mirror i))) p ↔ openSquare (model i) p := by
  fin_cases i
  all_goals first
    | exact (reflectDiagonal_open _ p).trans (diagonal_axis_open _ p)
    | exact Iff.rfl

/-- The reflection of the model is congruent to the model, by a relabelling
alone. -/
theorem model_reflection_congruent :
    Congruent (fun i => reflectDiagonalSquare (model i)) (0,0) model :=
  congruent_of_origin_sets mirror model_reflection_open
    (fun i => same_open_same_closed _ _ (model_reflection_open i))

/-- A configuration congruent to `T`, or to the diagonal reflection of `T`, is
congruent to the model when `T` is. -/
theorem congruent_of_reflection {S T : Fin 6 → UnitSquare} {o : Point}
    (hST : CongruentOrDiagonal S o T)
    (hT : Congruent T (0,0) model) : Congruent S o model := by
  rcases hST with h | h
  · exact congruent_trans h hT
  · exact congruent_trans (congruent_trans h (congruent_diagonal hT)) model_reflection_congruent

end SquaresInCircles.Six.Equality
