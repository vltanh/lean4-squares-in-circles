module

public import SquaresInCircles.Eight.GeometricModel.Theorem

/-!
# Eight squares — complete uncompiled table-free proof entry

This is the single-file *entry point* to the full drafted proof of the
unrestricted eight-unit-square packing theorem, not a duplicate of the
underlying analytic argument. All genuine geometric subproofs, original
source-owner exclusions, radius and equality arguments are imported
transitively through GeometricModel.Theorem.

The proof dependency backbone is:

  GlobalGAHighBT2Complete.high_GA_BT2_exclusion
    -> GlobalGAHighSourceComplete.table_free_sharp_source_entry
    -> GeometricModel.SharpAssembly.origin_sharp_rigidity
    -> GeometricModel.SharpEquality.sharp_uniqueness
    -> GeometricModel.Theorem.lower_bound/equality_iff_parameters

The source proof records the initially selected physical separating
normals and the original actual squared radius, and classifies the
five-parameter equality family with both reflections and weak contacts.
This file supplies an *unconditional* conjunction of the desired results;
it does not assume a source-entry proposition or a generated owner capture.

No Lean, lake, native compiler, tests or CI have been run. Neither the
declarations below nor their imports have been kernel-verified. The
transitive import and axiom audit is tracked in the G9 roadmap.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree

open GeometricModel

/-- The original seven-square boundary source has the stationary
physical normals and frames at the sharp circle. The underlying
theorem has no HighGABT2Exclusion or SharpSourceEntry hypothesis. -/
theorem unrestricted_source_entry : SharpSourceEntry :=
  table_free_sharp_source_entry

/-- Unrestricted radius lower bound for *the original packing*, with
arbitrary center, square labels, and physical orientations. -/
theorem unrestricted_radius_lower_bound
    {S : Fin 8 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) : FiveCorner.radius ≤ R :=
  GeometricModel.lower_bound hp

/-- Squared-radius version, for original physical squares and their
actual enclosing circle, prior to taking square roots. -/
theorem unrestricted_squared_radius_lower_bound
    {S : Fin 8 → UnitSquare} {o : Point} {q : ℝ}
    (hp : SqPacking S o q) : FiveCorner.radius^2 ≤ q :=
  GeometricModel.squared_radius_lower_bound hp

/-- Existence at the lower bound. -/
theorem unrestricted_sharp_attained :
    ∃ (S : Fin 8 → UnitSquare), Packing S (0,0) FiveCorner.radius :=
  ⟨GeometricModel.attainingModel, GeometricModel.attainingPacking⟩

/-- Complete equality classification: precisely the admissible
five-parameter family, both reflected cases, arbitrary original labels,
and the weak equality-boundary contacts. -/
theorem unrestricted_equality_iff_parameters
    (S : Fin 8 → UnitSquare) (o : Point) :
    Packing S o FiveCorner.radius ↔
      ∃ reflected : Bool, ∃ p : GeometricModel.Parameters,
        p.Admissible FiveCorner.selected ∧
          Congruent S o (GeometricModel.reflectedModel reflected p) :=
  GeometricModel.equality_iff_parameters S o

/-- Sharp radius is the least attainable disk radius. -/
theorem unrestricted_least_radius :
    IsLeast {R | ∃ (S : Fin 8 → UnitSquare) (o : Point), Packing S o R}
      FiveCorner.radius :=
  GeometricModel.isLeast

/-- All equality configurations are congruent to an admissible model
(the model itself need not be unique: two sliders are free). -/
theorem unrestricted_equality_classified
    (S : Fin 8 → UnitSquare) (o : Point)
    (hp : Packing S o FiveCorner.radius) :
    ∃ M ∈ GeometricModel.models, Congruent S o M :=
  GeometricModel.uniqueness S o hp

/-- The full rigid equality witness retains an isometry, the
arbitrary original labels and exact open/closed square preservation.
No uniqueness of the two free sliders is asserted. -/
theorem unrestricted_equality_rigid
    (S : Fin 8 → UnitSquare) (o : Point)
    (hp : Packing S o FiveCorner.radius) :
    ∃ M ∈ GeometricModel.models,
      ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin 8)),
        e (0,0)=o ∧
        (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
        (∀ i p, (openSquare (S (σ i)) (e p) ↔ openSquare (M i) p) ∧
          (closedSquare (S (σ i)) (e p) ↔ closedSquare (M i) p)) :=
  GeometricModel.equality_rigid S o hp

/-- Unrestricted, attained sharp radius and full five-parameter
classification in a single unconditional Lean statement.

This is the requested source-level final theorem entry: its four
conjuncts are proved, not named as axioms or required as hypotheses.
Kernel verification is deliberately deferred. -/
theorem unrestricted_eight_complete :
    (∀ {S : Fin 8 → UnitSquare} {o : Point} {R : ℝ},
      Packing S o R → FiveCorner.radius ≤ R) ∧
    (∃ (S : Fin 8 → UnitSquare),
      Packing S (0,0) FiveCorner.radius) ∧
    (∀ (S : Fin 8 → UnitSquare) (o : Point),
      Packing S o FiveCorner.radius ↔
        ∃ reflected : Bool, ∃ p : GeometricModel.Parameters,
          p.Admissible FiveCorner.selected ∧
            Congruent S o (GeometricModel.reflectedModel reflected p)) ∧
    IsLeast {R | ∃ (S : Fin 8 → UnitSquare) (o : Point), Packing S o R}
      FiveCorner.radius := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S o R hp
    exact unrestricted_radius_lower_bound hp
  · exact unrestricted_sharp_attained
  · intro S o
    exact unrestricted_equality_iff_parameters S o
  · exact unrestricted_least_radius

end SquaresInCircles.Eight.TableFree
