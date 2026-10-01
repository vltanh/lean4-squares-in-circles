import SquaresInCircles.Seven.Contacts
import SquaresInCircles.Common.SeparatingAxes

/-!
# The canonical pair

Two squares in the frame of the first one, the second turned by the relative
phase. If their open squares are disjoint, the separating-axis theorem gives a
nonpositive support sum on one of the four axes, of the pair or of the pair
seen from the second square.
-/
noncomputable section
namespace SquaresInCircles.Seven

lemma reverse_reflected_phase (a u A v g : ℝ) (s t : TransverseSign) :
    relativePhase A v a u g t.flip s.flip=relativePhase a u A v g s t := by
  dsimp [relativePhase]
  rw [TransverseSign.coe_flip,TransverseSign.coe_flip]
  ring

/-- The open squares of the canonical pair are disjoint: `Q(a, su)`, and the
square at `(A, tv)` in the frame turned by the relative phase. -/
def CanonicalDisjoint (a u A v g : ℝ) (s t : TransverseSign) : Prop :=
  ∀ p, ¬ (openSquare (orientedSquare 0 a (s.coe*u)) p ∧
    openSquare (orientedSquare (relativePhase a u A v g s t) A (t.coe*v)) p)

/-- A disjoint canonical pair has a nonpositive support sum in one of its
frames: along the axes of the first square these are the support sums of the
pair, and along the axes of the second square those of the reversed pair. -/
lemma canonical_has_separator {a u A v g : ℝ} (s t : TransverseSign)
    (hd : CanonicalDisjoint a u A v g s t) :
    (∃ k, pairSupport a u A v s t k g ≤ 0) ∨
    (∃ k, pairSupport A v a u t.flip s.flip k g ≤ 0) := by
  obtain ⟨e0,e1,e2,e3⟩ := pair_support_axis_values a u A v g s t
  obtain ⟨f0,f1,f2,f3⟩ := pair_support_axis_values A v a u g t.flip s.flip
  simp only [centerDX,centerDY] at e0 e1 e2 e3
  simp only [reverse_reflected_phase,centerDX,centerDY,TransverseSign.coe_flip] at f0 f1 f2 f3
  have h := oriented_separating_axes hd
  rw [sub_zero] at h
  rcases h with h | h | h | h <;> rcases le_abs'.mp h with h | h
  · exact Or.inl ⟨2,by linarith⟩
  · exact Or.inl ⟨0,by linarith⟩
  · exact Or.inl ⟨3,by linarith⟩
  · exact Or.inl ⟨1,by linarith⟩
  · exact Or.inr ⟨0,by linarith⟩
  · exact Or.inr ⟨2,by linarith⟩
  · exact Or.inr ⟨3,by linarith⟩
  · exact Or.inr ⟨1,by linarith⟩

end SquaresInCircles.Seven
