import SquaresInCircles.Common.NormalForm

/-!
# The optimum for `n` squares

Every case proves the same three facts about `n` unit squares, at one radius:
the axis-parallel squares at each optimal layout form a packing of that radius,
some square of each layout reaches the circle of that radius, and every packing
of that radius has the normal form of an optimal layout. `Optimum` bundles
them. The lower bound, attainment, the converse of uniqueness and uniqueness
with an explicit isometry follow here, once for all cases: a packing in a
smaller disk would also pack the optimal one, so it would have the normal form
of a layout that reaches the larger circle.
-/
noncomputable section
namespace SquaresInCircles

/-- The optimum for `n` unit squares: the least radius of a disk that holds
them, and the layouts of the packings that attain it, as centres in the frame
of the disk centre. -/
structure Optimum (n : ℕ) where
  radius : ℝ
  layouts : Set (Fin n → Point)
  layouts_nonempty : layouts.Nonempty
  layout_packing : ∀ c ∈ layouts, Packing (fun i => axisSquare (c i)) (0,0) radius
  layout_reaches : ∀ c ∈ layouts, ∃ i x y, closedAxisSquare (c i) x y ∧ radius^2 ≤ x^2+y^2
  uniqueness : ∀ (S : Fin n → UnitSquare) (o : Point), Packing S o radius →
    ∃ c ∈ layouts, HasNormalForm S o c

namespace Optimum

variable {n : ℕ} (P : Optimum n)

/-- The optimum with a single layout: the optimal packing is unique. -/
def ofUnique {R : ℝ} (c : Fin n → Point)
    (packing : Packing (fun i => axisSquare (c i)) (0,0) R)
    (reaches : ∃ i x y, closedAxisSquare (c i) x y ∧ R^2 ≤ x^2+y^2)
    (uniqueness : ∀ (S : Fin n → UnitSquare) (o : Point), Packing S o R → HasNormalForm S o c) :
    Optimum n where
  radius := R
  layouts := {c}
  layouts_nonempty := ⟨c,rfl⟩
  layout_packing _ h := h ▸ packing
  layout_reaches _ h := h ▸ reaches
  uniqueness S o hp := ⟨c,rfl,uniqueness S o hp⟩

/-- The lower bound: no packing fits in a disk smaller than the optimal one. -/
theorem optimality (S : Fin n → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) :
    P.radius ≤ R := by
  by_contra hlt
  push Not at hlt
  have hsq : R^2 < P.radius^2 := by nlinarith [hp.1]
  obtain ⟨c,hc,φ,σ,hφ⟩ := P.uniqueness S o
    ⟨hp.1.trans hlt.le,fun j p hj => (hp.2.1 j p hj).trans hsq.le,hp.2.2⟩
  obtain ⟨i,x,y,hxy,hR⟩ := P.layout_reaches c hc
  have hin := hp.2.1 (σ i) _ ((hφ i x y).2.mpr hxy)
  rw [inDisk,pointInDirection_norm] at hin
  linarith

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
