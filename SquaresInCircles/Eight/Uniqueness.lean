module

public import SquaresInCircles.Eight.Construction
public import SquaresInCircles.Eight.Equality.SharpEquality
public import SquaresInCircles.Common.Optimum

/-!
# Eight squares: uniqueness

No packing of eight unit squares fits in a disk of radius less than `radius`,
and every packing in the disk of radius `radius` is congruent to one of
`models`: the five squares with a corner on the circle are fixed, `T` and `G`
slide, and the central square moves and turns in the room they leave.

The proof works in the stationary chart of `Stationary`. The radius of the
five-corner problem is its radius `√qStar` (`FiveCorner.radius_eq_stationary`),
and the admissible models, those with the central square around the disk
centre, are its models (`models_eq_stationary`). The boundary of the seven
exterior squares of a packing is excluded except at the stationary frames
(`Equality/SharpAssembly.lean`), which gives the lower bound; at those
frames the stationary identity fixes the five squares on the circle and leaves
the two sliders and the central square free
(`Equality/SharpEquality.lean`).

The file ends with `optimum`: the case as an `Optimum`.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open GeometricModel

theorem radius_eq_stationary : radius = stationaryRadius :=
  FiveCorner.radius_eq_stationary

/-- The squares of `p` are its model about the five corners. -/
theorem model_eq (p : Parameters) : model p = p.model FiveCorner.selected := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [model, Parameters.model, Matrix.cons_val_succ, Fin.cons_succ]
  fin_cases j <;> simp [FiveCorner.exteriorSquare, FiveCorner.exteriorCenter,
    FiveCorner.exteriorAngle]

/-- Every admissible model is one of `models`. -/
theorem admissibleModels_subset : admissibleModels ⊆ models := by
  intro M hM
  obtain ⟨b, p, -, rfl⟩ := id hM
  refine ⟨p, ?_, GeometricModel.model_packing _ hM⟩
  cases b
  · exact Or.inl (by simp [reflectedModel, model_eq])
  · exact Or.inr (by simp [reflectedModel, model_eq])

/-- No packing of eight unit squares fits in a disk of radius less than
`radius`. -/
theorem lower_bound {S : Fin 8 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) : radius ≤ R := by
  rw [radius_eq_stationary]
  exact sharp_radius_lower_bound hp

/-- Every packing in the disk of radius `radius` is congruent to one of
`models`. -/
theorem uniqueness (S : Fin 8 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : ∃ M ∈ models, Congruent S o M := by
  rw [radius_eq_stationary] at hp
  obtain ⟨M, hM, hcongruent⟩ := sharp_uniqueness hp
  exact ⟨M, admissibleModels_subset (models_eq_stationary.symm ▸ hM), hcongruent⟩

/-- Every model reaches the circle, at a corner of one of the five fixed
squares. -/
theorem models_reach (M : Fin 8 → UnitSquare) (hM : M ∈ models) :
    ∃ i x, closedSquare (M i) x ∧ radius ^ 2 ≤ normSq x := by
  obtain ⟨p, hM, -⟩ := hM
  obtain ⟨i, x, hx, hr⟩ := Parameters.model_reaches p
  rcases hM with rfl | rfl
  · exact ⟨i, x, by rwa [model_eq], hr⟩
  · refine ⟨i, diagonalPoint x, ?_, ?_⟩
    · simpa [model_eq, reflectSquare_eq_reflectDiagonalSquare, reflectDiagonal_closed]
        using hx
    · simpa [normSq, diagonalPoint, add_comm] using hr

/-- The optimum for eight squares. -/
def optimum : Optimum 8 where
  radius := radius
  models := models
  models_nonempty := GeometricModel.models_nonempty.mono admissibleModels_subset
  model_packing _ hM := hM.choose_spec.2
  model_reaches := models_reach
  uniqueness := uniqueness

end SquaresInCircles.Eight
