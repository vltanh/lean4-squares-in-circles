import SquaresInCircles.Common.NormalForm

/-!
# The optimum for `n` squares

Every case proves the same three facts about `n` unit squares: a lower bound on
the radius of any disk that holds them, that the axis-parallel squares at each
optimal layout form a packing of that radius, and that every packing of that
radius has the normal form of an optimal layout. `Optimum` bundles them.
Attainment, the converse of uniqueness and uniqueness with an explicit isometry
follow here, once for all cases.
-/
noncomputable section
namespace SquaresInCircles

/-- The optimum for `n` unit squares: the least radius of a disk that holds
them, and the layouts of the packings that attain it, as centres in the frame
of the disk centre. -/
structure Optimum (n : ℕ) where
  radius : ℝ
  layouts : Set (Fin n → Point)
  optimality : ∀ (S : Fin n → UnitSquare) (o : Point) (R : ℝ), Packing S o R → radius ≤ R
  layouts_nonempty : layouts.Nonempty
  layout_packing : ∀ c ∈ layouts, Packing (fun i => axisSquare (c i)) (0,0) radius
  uniqueness : ∀ (S : Fin n → UnitSquare) (o : Point), Packing S o radius →
    ∃ c ∈ layouts, HasNormalForm S o c

namespace Optimum

variable {n : ℕ} (P : Optimum n)

/-- The optimum with a single layout: the optimal packing is unique. -/
def ofUnique {R : ℝ} (c : Fin n → Point)
    (optimality : ∀ (S : Fin n → UnitSquare) (o : Point) (R' : ℝ), Packing S o R' → R ≤ R')
    (packing : Packing (fun i => axisSquare (c i)) (0,0) R)
    (uniqueness : ∀ (S : Fin n → UnitSquare) (o : Point), Packing S o R → HasNormalForm S o c) :
    Optimum n where
  radius := R
  layouts := {c}
  optimality := optimality
  layouts_nonempty := ⟨c,rfl⟩
  layout_packing _ h := h ▸ packing
  uniqueness S o hp := ⟨c,rfl,uniqueness S o hp⟩

/-- Some packing attains the optimal radius. -/
theorem attainment : ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o P.radius :=
  let ⟨c,hc⟩ := P.layouts_nonempty
  ⟨_,_,P.layout_packing c hc⟩

/-- The packings of the optimal radius are exactly the normal forms of the
optimal layouts. -/
theorem packing_iff (S : Fin n → UnitSquare) (o : Point) :
    Packing S o P.radius ↔ ∃ c ∈ P.layouts, HasNormalForm S o c :=
  ⟨P.uniqueness S o,fun ⟨c,hc,h⟩ => h.packing (P.layout_packing c hc)⟩

/-- Uniqueness with the frame replaced by an explicit isometry of the plane that
takes the origin to the disk centre. -/
theorem rigid_uniqueness (S : Fin n → UnitSquare) (o : Point) (hp : Packing S o P.radius) :
    ∃ c ∈ P.layouts, ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin n)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, (openSquare (S (σ i)) (e p) ↔ openAxisSquare (c i) p.1 p.2) ∧
        (closedSquare (S (σ i)) (e p) ↔ closedAxisSquare (c i) p.1 p.2)) :=
  let ⟨c,hc,h⟩ := P.uniqueness S o hp
  ⟨c,hc,h.rigid_witness⟩

end Optimum

end SquaresInCircles
