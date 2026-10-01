import SquaresInCircles.Common.Basic
import Mathlib.Tactic

/-!
# Pin labels

If each of five squares with pairwise disjoint interiors holds one of five
pins in its open square, the squares and the pins correspond one to one: no
pin lies in two squares, so the squares hold distinct pins, and all five pins
are used.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- If each of five interior-disjoint squares holds a pin, a permutation `σ`
labels them: the square `σ j` holds the pin `j`, no other square holds the
pin `j`, and the square `σ j` holds no other pin. -/
theorem pin_labels_of_covering (S : Fin 5 → UnitSquare) (pins : Fin 5 → Point)
    (hd : InteriorDisjoint S)
    (hcover : ∀ i, ∃ j, openSquare (S i) (pins j)) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ j,
      openSquare (S (σ j)) (pins j) ∧
      (∀ i, openSquare (S i) (pins j) → i = σ j) ∧
      (∀ k, openSquare (S (σ j)) (pins k) → k = j) := by
  classical
  choose f hf using hcover
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hj : openSquare (S j) (pins (f i)) := by rw [hij]; exact hf j
    exact hd i j hne (pins (f i)) ⟨hf i, hj⟩
  let e : Equiv.Perm (Fin 5) := Equiv.ofBijective f hinj.bijective_of_finite
  have hmem (j : Fin 5) : openSquare (S (e.symm j)) (pins j) := by
    simpa only [show f (e.symm j) = j from e.apply_symm_apply j] using hf (e.symm j)
  refine ⟨e.symm, ?_⟩
  intro j
  refine ⟨hmem j, ?_, ?_⟩
  · intro i hi
    by_contra hne
    exact hd i (e.symm j) hne (pins j) ⟨hi, hmem j⟩
  · intro k hk
    have he : e.symm j = e.symm k := by
      by_contra hne
      exact hd (e.symm j) (e.symm k) hne (pins k) ⟨hk, hmem k⟩
    exact (e.symm.injective he).symm

end SquaresInCircles.Six.Normalization
