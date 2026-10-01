import SquaresInCircles.Six.Construction
import SquaresInCircles.Six.Normalization.PinReflection
import SquaresInCircles.Six.CongruenceTools

/-!
# The diagonal reflection of the model

The model is symmetric under the reflection in the diagonal `y = x`, which
exchanges N with E and W with S and maps C and D to themselves, so its
reflection is congruent to it by a relabelling alone. Reflecting both sides of
a congruence gives a congruence with the opposite rotation. Hence a
configuration congruent to `T` or to the reflection of `T`, as the
normalization produces, is congruent to the model whenever `T` is.
-/

noncomputable section
namespace SquaresInCircles.Six.Equality

/-- The relabelling of the model by the diagonal reflection: in the order
C, N, E, W, S, D it exchanges N with E and W with S. -/
def candidateMirror : Equiv.Perm (Fin 6) where
  toFun := ![0,2,1,4,3,5]
  invFun := ![0,2,1,4,3,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

lemma diagonalSquare_reflection : reflectDiagonalSquare diagonalSquare = diagonalSquare := rfl

/-- The reflection of a square of the model is the square with the exchanged
label. -/
lemma candidate_reflection_open (i : Fin 6) (p : Point) :
    openSquare (reflectDiagonalSquare (Six.model (candidateMirror i))) p ↔
      openSquare (Six.model i) p := by
  fin_cases i
  · change openSquare (reflectDiagonalSquare (axisSquare (sStar,sStar))) p ↔ _
    rw [reflectDiagonal_open]
    exact diagonal_axis_open (sStar,sStar) p
  · change openSquare (reflectDiagonalSquare (axisSquare (sStar+1,sStar))) p ↔ _
    rw [reflectDiagonal_open]
    exact diagonal_axis_open (sStar+1,sStar) p
  · change openSquare (reflectDiagonalSquare (axisSquare (sStar,sStar+1))) p ↔ _
    rw [reflectDiagonal_open]
    exact diagonal_axis_open (sStar,sStar+1) p
  · change openSquare (reflectDiagonalSquare (axisSquare (tStar,sStar-1))) p ↔ _
    rw [reflectDiagonal_open]
    exact diagonal_axis_open (tStar,sStar-1) p
  · change openSquare (reflectDiagonalSquare (axisSquare (sStar-1,tStar))) p ↔ _
    rw [reflectDiagonal_open]
    exact diagonal_axis_open (sStar-1,tStar) p
  · change openSquare (reflectDiagonalSquare diagonalSquare) p ↔ openSquare diagonalSquare p
    rw [diagonalSquare_reflection]

lemma candidate_reflection_closed (i : Fin 6) (p : Point) :
    closedSquare (reflectDiagonalSquare (Six.model (candidateMirror i))) p ↔
      closedSquare (Six.model i) p :=
  same_open_same_closed _ _ (candidate_reflection_open i) p

/-- The reflection of the model is congruent to the model, by a relabelling
alone. -/
theorem candidate_diagonal_congruent :
    Congruent (fun i => reflectDiagonalSquare (Six.model i)) (0,0) Six.model :=
  congruent_of_origin_sets candidateMirror candidate_reflection_open candidate_reflection_closed

lemma diagonal_conjugates_rotation (φ : Direction) (p : Point) :
    diagonalPoint (pointInDirection (0,0) (-φ) p.1 p.2) =
      pointInDirection (0,0) φ (diagonalPoint p).1 (diagonalPoint p).2 := by
  apply Prod.ext <;>
    simp only [diagonalPoint,pointInDirection,Real.Angle.cos_neg,Real.Angle.sin_neg,zero_add] <;>
    ring

/-- Reflecting both sides of a congruence gives a congruence, with the opposite
rotation. -/
theorem congruent_diagonal {n : ℕ} {S T : Fin n → UnitSquare}
    (h : Congruent S (0,0) T) :
    Congruent (fun i => reflectDiagonalSquare (S i)) (0,0)
      (fun i => reflectDiagonalSquare (T i)) := by
  obtain ⟨φ,σ,hφ⟩ := h
  refine ⟨-φ,σ,?_⟩
  intro i p
  have hh := hφ i (diagonalPoint p)
  constructor
  · rw [reflectDiagonal_open,diagonal_conjugates_rotation,reflectDiagonal_open]
    exact hh.1
  · rw [reflectDiagonal_closed,diagonal_conjugates_rotation,reflectDiagonal_closed]
    exact hh.2

/-- A configuration congruent to `T`, or to the diagonal reflection of `T`, is
congruent to the model when `T` is. -/
theorem absorb_normalization_reflection {S T : Fin 6 → UnitSquare} {o : Point}
    (hST : Normalization.CongruentOrDiagonal S o T)
    (hT : Congruent T (0,0) Six.model) : Congruent S o Six.model := by
  rcases hST with h | h
  · exact congruent_trans h hT
  · exact congruent_trans (congruent_trans h (congruent_diagonal hT)) candidate_diagonal_congruent

end SquaresInCircles.Six.Equality
