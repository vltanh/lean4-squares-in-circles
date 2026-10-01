import SquaresInCircles.Six.NormalizeFrame

/-!
# Composing congruences

Congruence about the origin is reflexive, and a congruence about `o` followed
by one about the origin is a congruence about `o`: the rotations add and the
relabellings compose. A relabelling of the five exterior squares extends to the
six squares by fixing the central square, and two configurations with the same
open and closed squares after a relabelling are congruent.
-/

noncomputable section
namespace SquaresInCircles.Six

lemma pointInDirection_comp (o : Point) (φ ψ : Direction) (p : Point) :
    pointInDirection o φ (pointInDirection (0,0) ψ p.1 p.2).1
      (pointInDirection (0,0) ψ p.1 p.2).2 =
      pointInDirection o (φ+ψ) p.1 p.2 := by
  apply Prod.ext <;> simp only [pointInDirection,Real.Angle.cos_add,Real.Angle.sin_add,
    zero_add] <;> ring

lemma congruent_trans {n : ℕ} {S M N : Fin n → UnitSquare} {o : Point}
    (hS : Congruent S o M) (hM : Congruent M (0,0) N) : Congruent S o N := by
  obtain ⟨φ,σ,hφ⟩ := hS
  obtain ⟨ψ,τ,hψ⟩ := hM
  refine ⟨φ+ψ,τ.trans σ,?_⟩
  intro i p
  have h1 := hφ (τ i) (pointInDirection (0,0) ψ p.1 p.2)
  have h2 := hψ i p
  rw [pointInDirection_comp] at h1
  exact ⟨h1.1.trans h2.1,h1.2.trans h2.2⟩

lemma congruent_refl {n : ℕ} (M : Fin n → UnitSquare) : Congruent M (0,0) M := by
  refine ⟨0,Equiv.refl _,?_⟩
  intro i p
  simp [pointInDirection]

/-- A relabelling of the five exterior squares, extended by fixing the central
square `0`. -/
def extendExteriorPerm (σ : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 6) where
  toFun := Fin.cases 0 (fun i => (σ i).succ)
  invFun := Fin.cases 0 (fun i => (σ.symm i).succ)
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] lemma extendExteriorPerm_zero (σ : Equiv.Perm (Fin 5)) :
    extendExteriorPerm σ 0 = 0 := rfl

lemma congruent_of_origin_sets {n : ℕ} {S M : Fin n → UnitSquare}
    (σ : Equiv.Perm (Fin n))
    (ho : ∀ i p, openSquare (S (σ i)) p ↔ openSquare (M i) p)
    (hc : ∀ i p, closedSquare (S (σ i)) p ↔ closedSquare (M i) p) :
    Congruent S (0,0) M := by
  refine ⟨0,σ,?_⟩
  intro i p
  simpa [pointInDirection] using And.intro (ho i p) (hc i p)

end SquaresInCircles.Six
