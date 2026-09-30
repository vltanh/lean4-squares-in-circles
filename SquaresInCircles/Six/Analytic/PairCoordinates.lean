import SquaresInCircles.Six.Normalization.CentralSAT
import SquaresInCircles.Seven.SeparatingAxes

/-!
# Exact coordinates of the four pair axes

This module contains only identities and the actual geometric separating-axis
alternative. It imports neither a normalized packing nor a scalar certificate.
The names are retained in Normalization for compatibility with the stress code.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

lemma oriented_relativeC (t a b T A B : ℝ) :
    relativeC (orientedSquare t a b) (orientedSquare T A B) = Real.cos (T-t) := by
  simp only [relativeC,orientedSquare,Real.cos_sub]
  ring

lemma oriented_relativeS (t a b T A B : ℝ) :
    relativeS (orientedSquare t a b) (orientedSquare T A B) = Real.sin (T-t) := by
  simp only [relativeS,orientedSquare,Real.sin_sub]
  ring

lemma oriented_pair_threshold (t a b T A B : ℝ) :
    Seven.SAT.threshold (orientedSquare t a b) (orientedSquare T A B) =
      1/2+angularWidth (T-t) := by
  rw [Seven.SAT.threshold,oriented_relativeC,oriented_relativeS]
  dsimp [angularWidth]
  ring

lemma pair_frameX_left (t a b T A B : ℝ) :
    frameX (orientedSquare t a b)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center) =
      A*Real.cos (T-t)-B*Real.sin (T-t)-a := by
  dsimp [frameX,orientedSquare,sub]
  rw [Real.cos_sub,Real.sin_sub]
  linear_combination -a*(Real.sin_sq_add_cos_sq t)

lemma pair_frameY_left (t a b T A B : ℝ) :
    frameY (orientedSquare t a b)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center) =
      A*Real.sin (T-t)+B*Real.cos (T-t)-b := by
  dsimp [frameY,orientedSquare,sub]
  rw [Real.cos_sub,Real.sin_sub]
  linear_combination -b*(Real.sin_sq_add_cos_sq t)

lemma pair_frameX_right (t a b T A B : ℝ) :
    frameX (orientedSquare T A B)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center) =
      A-a*Real.cos (T-t)-b*Real.sin (T-t) := by
  dsimp [frameX,orientedSquare,sub]
  rw [Real.cos_sub,Real.sin_sub]
  linear_combination A*(Real.sin_sq_add_cos_sq T)

lemma pair_frameY_right (t a b T A B : ℝ) :
    frameY (orientedSquare T A B)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center) =
      B+a*Real.sin (T-t)-b*Real.cos (T-t) := by
  dsimp [frameY,orientedSquare,sub]
  rw [Real.cos_sub,Real.sin_sub]
  linear_combination B*(Real.sin_sq_add_cos_sq T)

def pairMargin (i : Fin 4) (t a b T A B : ℝ) : ℝ :=
  let d := T-t
  let h := 1/2+angularWidth d
  ![|A*Real.cos d-B*Real.sin d-a|-h,
    |A*Real.sin d+B*Real.cos d-b|-h,
    |A-a*Real.cos d-b*Real.sin d|-h,
    |B+a*Real.sin d-b*Real.cos d|-h] i

lemma pair_separators_complete {t a b T A B : ℝ}
    (hd : ∀ p, ¬ (openSquare (orientedSquare t a b) p ∧
      openSquare (orientedSquare T A B) p)) :
    ∃ i : Fin 4, 0 ≤ pairMargin i t a b T A B := by
  have h := Seven.SAT.separating_axes (orientedSquare t a b) (orientedSquare T A B) hd
  rw [oriented_pair_threshold,pair_frameX_left,pair_frameY_left,
    pair_frameX_right,pair_frameY_right] at h
  rcases h with h | h | h | h
  · exact ⟨0,by dsimp [pairMargin]; linarith⟩
  · exact ⟨1,by dsimp [pairMargin]; linarith⟩
  · exact ⟨2,by dsimp [pairMargin]; linarith⟩
  · exact ⟨3,by dsimp [pairMargin]; linarith⟩

end SquaresInCircles.Six.Normalization
