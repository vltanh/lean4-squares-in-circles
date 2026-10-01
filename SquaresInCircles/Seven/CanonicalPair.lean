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

private lemma first_axes_of_support {a u A v g : ℝ} (s t : TransverseSign)
    (h : ∀ k, 0 < pairSupport a u A v s t k g) :
    |centerDX a u A v g s t| < pairWidth (relativePhase a u A v g s t) ∧
    |centerDY a u A v g s t| < pairWidth (relativePhase a u A v g s t) := by
  have he := pair_support_axis_values a u A v g s t
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  rw [he.1] at h0
  rw [he.2.1] at h1
  rw [he.2.2.1] at h2
  rw [he.2.2.2] at h3
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,
    abs_lt.mpr ⟨by linarith,by linarith⟩⟩

lemma reverse_center_coordinates (a u A v g : ℝ) (s t : TransverseSign) :
    Real.cos (relativePhase a u A v g s t)*centerDX a u A v g s t+
      Real.sin (relativePhase a u A v g s t)*centerDY a u A v g s t =
        -centerDX A v a u g t.flip s.flip ∧
    -Real.sin (relativePhase a u A v g s t)*centerDX a u A v g s t+
      Real.cos (relativePhase a u A v g s t)*centerDY a u A v g s t =
        centerDY A v a u g t.flip s.flip := by
  let d := relativePhase a u A v g s t
  have hu := Real.sin_sq_add_cos_sq d
  constructor <;> dsimp [centerDX,centerDY] <;>
    rw [reverse_reflected_phase] <;> simp only [TransverseSign.coe_flip]
  · change Real.cos d*(A*Real.cos d-t.coe*v*Real.sin d-a)+
      Real.sin d*(A*Real.sin d+t.coe*v*Real.cos d-s.coe*u) = _
    linear_combination A*hu
  · change -Real.sin d*(A*Real.cos d-t.coe*v*Real.sin d-a)+
      Real.cos d*(A*Real.sin d+t.coe*v*Real.cos d-s.coe*u) = _
    linear_combination t.coe*v*hu

/-- A disjoint canonical pair has a nonpositive support in one of its frames. -/
lemma canonical_has_separator {a u A v g : ℝ} (s t : TransverseSign)
    (hd : CanonicalDisjoint a u A v g s t) :
    (∃ k, pairSupport a u A v s t k g ≤ 0) ∨
    (∃ k, pairSupport A v a u t.flip s.flip k g ≤ 0) := by
  by_contra hn
  have hf : ∀ k, 0 < pairSupport a u A v s t k g := by
    intro k
    by_contra hk
    exact hn (Or.inl ⟨k,le_of_not_gt hk⟩)
  have hr : ∀ k, 0 < pairSupport A v a u t.flip s.flip k g := by
    intro k
    by_contra hk
    exact hn (Or.inr ⟨k,le_of_not_gt hk⟩)
  have hfirst := first_axes_of_support s t hf
  have hsecond := first_axes_of_support t.flip s.flip hr
  rw [reverse_reflected_phase] at hsecond
  let d := relativePhase a u A v g s t
  let S := orientedSquare 0 a (s.coe*u)
  let T := orientedSquare d A (t.coe*v)
  have hc : relativeC S T = Real.cos d := by
    norm_num [S,T,orientedSquare,relativeC]
  have hs : relativeS S T = Real.sin d := by
    norm_num [S,T,orientedSquare,relativeS]
  have hw : SAT.threshold S T = pairWidth d := by rw [SAT.threshold,hc,hs]; rfl
  have hx : frameX S (sub T.center S.center) = centerDX a u A v g s t := by
    norm_num [S,T,orientedSquare,frameX,sub,centerDX,d]
  have hy : frameY S (sub T.center S.center) = centerDY a u A v g s t := by
    norm_num [S,T,orientedSquare,frameY,sub,centerDY,d]
  have hT := relative_normal S T (sub T.center S.center)
  rw [hc,hs,hx,hy] at hT
  have he := reverse_center_coordinates a u A v g s t
  have hsep := SAT.separating_axes S T hd
  rw [hw,hx,hy,hT.1,hT.2,he.1,he.2,abs_neg] at hsep
  rcases hsep with hsep | hsep | hsep | hsep
  · exact (not_le_of_gt hfirst.1) hsep
  · exact (not_le_of_gt hfirst.2) hsep
  · exact (not_le_of_gt hsecond.1) hsep
  · exact (not_le_of_gt hsecond.2) hsep

end SquaresInCircles.Seven
