module

public import SquaresInCircles.Eight.Construction
public import SquaresInCircles.Eight.Rigidity.Classification
public import SquaresInCircles.Common.Optimum

/-!
# Eight squares: uniqueness

Every packing at `radius` is congruent to one of `models`: five squares have
fixed corners on the circle, two slide, and the central square moves and turns.
`Construction.lean` proves that these models pack the disk and reach its circle.
`Rigidity/Classification.lean` captures the boundary frames with checked tables and applies the
terminal identity to classify the packing in stationary coordinates. The
geometric bridges identify that family with the public five-corner family.

As for one through seven squares, `optimum` assembles these facts, and the lower
bound and the converse of uniqueness follow from `Common/Optimum.lean`.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Eight
open GeometricModel

/-- Every packing in the disk of radius `radius` is congruent to an optimal model. -/
theorem uniqueness (S : Fin 8 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : ∃ M ∈ models, Congruent S o M := by
  rw [radius_eq_stationary] at hp
  obtain ⟨M, hM, hcongruent⟩ := stationary_classification S o hp
  exact ⟨M, admissibleModels_subset (models_eq_stationary.symm ▸ hM), hcongruent⟩

/-- The optimum for eight squares: the five-parameter family and its reflections. -/
def optimum : Optimum 8 where
  radius := radius
  models := models
  models_nonempty := models_nonempty
  model_packing := model_packing
  model_reaches := model_reaches
  uniqueness := uniqueness

/-- No packing of eight unit squares fits in a smaller disk. -/
theorem lower_bound {S : Fin 8 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) : radius ≤ R :=
  optimum.optimality S o R hp

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
  constructor
  · intro hp
    obtain ⟨M, ⟨b, p, hp, rfl⟩, h⟩ := stationary_classification S o hp
    exact ⟨b, p, hp, h⟩
  · rintro ⟨b, p, hp, h⟩
    exact h.packing (ExactFamily.model_packing _ ⟨b, p, hp, rfl⟩)

end SquaresInCircles.Eight
