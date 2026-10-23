module

public import SquaresInCircles.Eight.GeometricModel.EqualityFamily
public import SquaresInCircles.Eight.GeometricModel.TwoHeightMinimum
public import SquaresInCircles.Eight.GeometricModel.SharpEquality
public import SquaresInCircles.Eight.TableFree.EntryReduction
public import SquaresInCircles.Eight.ExactFamily.StatementLink
public import SquaresInCircles.Common.Optimum

/-!
# Eight squares: the geometric statement and its complete draft assembly

Uncompiled Lean source. The radius in these statements is the five-corner
minimum of StatementEightGeometric, and the model domain consists of exact
disk-containment, rail, interiority and separating-axis conditions.

FiveCornerSelection proves attainment and uniqueness of the five points.
EqualityFamily proves exact equivalence of the geometric family with the
older stationary coordinate chart, including both reflections and all weak
contacts. SharpEquality supplies unrestricted classification from a fresh
boundary at the sharp radius and the dual at the original centers.

The sharp equality route now uses the unconditional *drafted* table-free
`GlobalGAHighSourceComplete.table_free_sharp_source_entry` through
`SharpAssembly`. The seven original physical witnesses, the actual containing
radius and five original anchors feed the lower bound and exact equality
classification. No generated `Candidate.Capture` proof is imported on this
route. Neither the old unrestricted lower bound nor its equality theorem is
an input. This is uncompiled source; ordinary Lean kernel verification and
transitive dependency audit remain pending.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GeometricModel

theorem radius_stationary : FiveCorner.radius=Eight.radius :=
  FiveCorner.radius_eq_stationary

/-- Compatibility with the older proof-independent stationary statement. -/
theorem radius_legacy_statement : FiveCorner.radius=EightStatement.radius :=
  radius_stationary.trans Eight.radius_statement

theorem models_legacy_statement : models=EightStatement.models :=
  models_eq_stationary.trans Eight.models_statement

/-- Every original packing, at its actual containing radius and arbitrary
center, satisfies the geometric radius bound. -/
theorem lower_bound {S : Fin 8 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) : FiveCorner.radius ≤ R := by
  rw [radius_stationary]
  exact sharp_radius_lower_bound hp

theorem squared_radius_lower_bound {S : Fin 8 → UnitSquare} {o : Point} {q : ℝ}
    (hp : SqPacking S o q) : FiveCorner.radius^2 ≤ q := by
  rw [FiveCorner.radius_sq_eq_stationary]
  exact sharp_squared_radius_lower_bound hp

theorem no_smaller_disk {S : Fin 8 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hR : R < FiveCorner.radius) : False :=
  (not_lt_of_ge (lower_bound hp)) hR

/-- Classification is a family statement: it does not claim that the two
sliders or the central square have a unique pose. -/
theorem uniqueness (S : Fin 8 → UnitSquare) (o : Point)
    (hp : Packing S o FiveCorner.radius) :
    ∃ M ∈ models, Congruent S o M := by
  rw [radius_stationary] at hp
  obtain ⟨M,hM,hcongruent⟩ := sharp_uniqueness hp
  exact ⟨M,models_eq_stationary.symm ▸ hM,hcongruent⟩

/-- The public eight-square optimum uses geometric definitions directly. -/
def optimum : Optimum 8 where
  radius := FiveCorner.radius
  models := models
  models_nonempty := models_nonempty
  model_packing := model_packing
  model_reaches := model_reaches
  uniqueness := uniqueness

theorem isLeast :
    IsLeast {R | ∃ (S : Fin 8 → UnitSquare) (o : Point), Packing S o R}
      FiveCorner.radius := by
  refine ⟨⟨attainingModel,(0,0),attainingPacking⟩,?_⟩
  rintro R ⟨S,o,hp⟩
  exact lower_bound hp

theorem packing_iff (S : Fin 8 → UnitSquare) (o : Point) :
    Packing S o FiveCorner.radius ↔ ∃ M ∈ models, Congruent S o M :=
  optimum.packing_iff S o

theorem equality_iff_parameters (S : Fin 8 → UnitSquare) (o : Point) :
    Packing S o FiveCorner.radius ↔
      ∃ reflected : Bool, ∃ p : Parameters,
        p.Admissible FiveCorner.selected ∧ Congruent S o (reflectedModel reflected p) := by
  constructor
  · intro hp
    obtain ⟨M,⟨b,p,hp,hM⟩,hcongruent⟩ := uniqueness S o hp
    exact ⟨b,p,hp,hM ▸ hcongruent⟩
  · rintro ⟨b,p,hp,hcongruent⟩
    exact hcongruent.packing (model_packing _ ⟨b,p,hp,rfl⟩)

/-- Full Euclidean congruence witness, including arbitrary original labels. -/
theorem equality_rigid (S : Fin 8 → UnitSquare) (o : Point)
    (hp : Packing S o FiveCorner.radius) :
    ∃ M ∈ models, ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin 8)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, (openSquare (S (σ i)) (e p) ↔ openSquare (M i) p) ∧
        (closedSquare (S (σ i)) (e p) ↔ closedSquare (M i) p)) :=
  optimum.rigid_uniqueness S o hp

end SquaresInCircles.Eight.GeometricModel
