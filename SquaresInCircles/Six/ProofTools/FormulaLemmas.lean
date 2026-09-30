module
public import SquaresInCircles.Six.ProofTools.Certificate

@[expose] public section

namespace SquaresInCircles.Six.ProofTools.Formula

variable {n : ℕ} (x : Fin n → ℝ)

lemma holds_all_iff (fs : List (Formula n)) :
    Holds (all fs) x ↔ ∀ f ∈ fs, Holds f x := by
  induction fs with
  | nil => simp [all,Holds]
  | cons f fs ih => simpa [all,Holds] using and_congr Iff.rfl ih

lemma holds_any_iff (fs : List (Formula n)) :
    Holds (any fs) x ↔ ∃ f ∈ fs, Holds f x := by
  induction fs with
  | nil => simp [any,Holds]
  | cons f fs ih => simpa [any,Holds] using or_congr Iff.rfl ih

lemma holds_all_map {α : Type*} (xs : List α) (f : α → Formula n) :
    Holds (all (xs.map f)) x ↔ ∀ a ∈ xs, Holds (f a) x := by
  rw [holds_all_iff]
  constructor
  · intro h a ha
    exact h (f a) (List.mem_map.mpr ⟨a,ha,rfl⟩)
  · intro h q hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    exact h a ha

lemma holds_any_map {α : Type*} (xs : List α) (f : α → Formula n) :
    Holds (any (xs.map f)) x ↔ ∃ a ∈ xs, Holds (f a) x := by
  rw [holds_any_iff]
  constructor
  · rintro ⟨q,hq,h⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    exact ⟨a,ha,h⟩
  · rintro ⟨a,ha,h⟩
    exact ⟨f a,List.mem_map.mpr ⟨a,ha,rfl⟩,h⟩

lemma holds_all_append (fs gs : List (Formula n)) :
    Holds (all (fs++gs)) x ↔ Holds (all fs) x ∧ Holds (all gs) x := by
  simp only [holds_all_iff,List.mem_append]
  constructor
  · intro h
    exact ⟨fun f hf => h f (Or.inl hf),fun g hg => h g (Or.inr hg)⟩
  · rintro ⟨hf,hg⟩ q (h | h)
    · exact hf q h
    · exact hg q h

end SquaresInCircles.Six.ProofTools.Formula
