import SquaresInCircles.Six.Normalization.CentralSAT
import SquaresInCircles.Seven.SeparatingAxes

/-!
# Coordinates of a pair of turned squares

For the squares `orientedSquare t a b` and `orientedSquare T A B`, with the
relative turn `q = T - t`, the separating threshold is `1/2 + angularWidth q`.
The difference of the centres has the coordinates
`(A cos q - B sin q - a, A sin q + B cos q - b)` in the frame of the first
square and `(A - a cos q - b sin q, B + a sin q - b cos q)` in the frame of the
second.
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

end SquaresInCircles.Six.Normalization
