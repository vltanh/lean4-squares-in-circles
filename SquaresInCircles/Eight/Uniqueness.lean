module

public import SquaresInCircles.Eight.Construction
public import SquaresInCircles.Eight.TableProof
public import SquaresInCircles.Common.Optimum

/-!
# Eight squares: uniqueness

No packing of eight unit squares fits in a disk of radius less than `radius`,
and every packing in the disk of radius `radius` is congruent to one of
`models`: the five squares with a corner on the circle are fixed, `T` and `G`
slide, and the central square moves and turns in the room they leave.

The proof works in the stationary chart of `ExactFamily`. The radius of the
five-corner problem is its radius `√qStar` (`FiveCorner.radius_eq_stationary`),
and the admissible models, those with the central square around the disk
centre, are its models (`models_eq_stationary`). The checked pair and owner
tables capture the boundary frames near the stationary configuration
(`TableProof.lean`). The terminal identity then gives the lower bound and
fixes the five anchor squares, leaving the two sliders and the central square
free. The geometric family is connected to that stationary family by
`models_eq_stationary`.

The file provides `optimum`, the case as an `Optimum`, and its public corollaries.
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
  exact table_lower_bound S o R hp

/-- Every packing in the disk of radius `radius` is congruent to one of
`models`. -/
theorem uniqueness (S : Fin 8 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : ∃ M ∈ models, Congruent S o M := by
  rw [radius_eq_stationary] at hp
  obtain ⟨M, hM, hcongruent⟩ := table_uniqueness S o hp
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

theorem radius_sq : radius ^ 2 = ExactFamily.qStar := by
  rw [radius_eq_stationary]
  exact stationaryRadius_sq

theorem radius_pos : 0 < radius := by
  rw [radius_eq_stationary]
  exact stationaryRadius_pos

theorem isLeast : IsLeast
    {R : ℝ | ∃ (S : Fin 8 → UnitSquare) (o : Point), Packing S o R} radius :=
  optimum.isLeast

theorem packing_iff (S : Fin 8 → UnitSquare) (o : Point) :
    Packing S o radius ↔ ∃ M ∈ models, Congruent S o M :=
  optimum.packing_iff S o

/-- The same optimal family in the stationary coordinates used by the tables. -/
theorem equality_iff_parameters (S : Fin 8 → UnitSquare) (o : Point) :
    Packing S o radius ↔ ∃ reflected : Bool, ∃ p : ExactFamily.EqualityParameters,
      p.Admissible ExactFamily.sharpData ∧
        Congruent S o (stationaryReflectedModel reflected p) := by
  rw [radius_eq_stationary]
  exact table_equality_iff_parameters S o

end SquaresInCircles.Eight
