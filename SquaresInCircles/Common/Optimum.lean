module

public import SquaresInCircles.Common.Congruence

/-!
# The optimum for `n` squares

Every case proves the same three facts about `n` unit squares, at one radius:
each optimal model, a configuration about the origin, is a packing of that
radius; some square of each model reaches the circle of that radius; and every
packing of that radius is congruent to an optimal model. `Optimum` bundles
them. The rest follows here, once for all cases: the radius is the least one
that holds a packing, since a packing in a smaller disk would also pack the
optimal one, so it would be congruent to a model that reaches the larger
circle; and the packings of that radius are exactly the configurations
congruent to a model.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

/-- The optimum for `n` unit squares: the least radius of a disk that holds
them, and the optimal packings, as models about the origin. -/
structure Optimum (n : ℕ) where
  radius : ℝ
  models : Set (Fin n → UnitSquare)
  models_nonempty : models.Nonempty
  model_packing : ∀ M ∈ models, Packing M (0,0) radius
  model_reaches : ∀ M ∈ models, ∃ i p, closedSquare (M i) p ∧ radius^2 ≤ normSq p
  uniqueness : ∀ (S : Fin n → UnitSquare) (o : Point), Packing S o radius →
    ∃ M ∈ models, Congruent S o M

namespace Optimum

variable {n : ℕ} (P : Optimum n)

/-- The optimum with a single model: the optimal packing is unique. -/
def ofUnique {R : ℝ} (M : Fin n → UnitSquare) (packing : Packing M (0,0) R)
    (reaches : ∃ i p, closedSquare (M i) p ∧ R^2 ≤ normSq p)
    (uniqueness : ∀ (S : Fin n → UnitSquare) (o : Point), Packing S o R → Congruent S o M) :
    Optimum n where
  radius := R
  models := {M}
  models_nonempty := ⟨M,rfl⟩
  model_packing _ h := h ▸ packing
  model_reaches _ h := h ▸ reaches
  uniqueness S o hp := ⟨M,rfl,uniqueness S o hp⟩

/-- No packing fits in a disk smaller than the optimal one. -/
theorem optimality (S : Fin n → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) :
    P.radius ≤ R := by
  by_contra hlt
  push Not at hlt
  have hsq : R^2 < P.radius^2 := by nlinarith [hp.1]
  obtain ⟨M,hM,φ,σ,hφ⟩ := P.uniqueness S o
    ⟨hp.1.trans hlt.le,fun j p hj => (hp.2.1 j p hj).trans hsq.le,hp.2.2⟩
  obtain ⟨i,p,hpM,hR⟩ := P.model_reaches M hM
  have hin := hp.2.1 (σ i) _ ((hφ i p).2.mpr hpM)
  rw [inDisk,pointInDirection_norm] at hin
  exact absurd hin (by unfold normSq at hR; linarith)

/-- The optimal radius is the least radius of a disk that holds `n` unit
squares. -/
theorem isLeast : IsLeast {R | ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o R} P.radius :=
  let ⟨M,hM⟩ := P.models_nonempty
  ⟨⟨M,(0,0),P.model_packing M hM⟩,fun _ ⟨S,o,hp⟩ => P.optimality S o _ hp⟩

/-- The packings of the optimal radius are exactly the configurations congruent
to an optimal model. -/
theorem packing_iff (S : Fin n → UnitSquare) (o : Point) :
    Packing S o P.radius ↔ ∃ M ∈ P.models, Congruent S o M :=
  ⟨P.uniqueness S o,fun ⟨M,hM,h⟩ => h.packing (P.model_packing M hM)⟩

/-- Uniqueness with the frame replaced by an explicit isometry of the plane that
takes the origin to the disk centre. -/
theorem rigid_uniqueness (S : Fin n → UnitSquare) (o : Point) (hp : Packing S o P.radius) :
    ∃ M ∈ P.models, ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin n)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, (openSquare (S (σ i)) (e p) ↔ openSquare (M i) p) ∧
        (closedSquare (S (σ i)) (e p) ↔ closedSquare (M i) p)) :=
  let ⟨M,hM,h⟩ := P.uniqueness S o hp
  ⟨M,hM,h.rigid_witness⟩

end Optimum

end SquaresInCircles
