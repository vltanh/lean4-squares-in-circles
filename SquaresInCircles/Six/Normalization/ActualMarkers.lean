import SquaresInCircles.Six.Normalization.PinPacking

/-!
# The radial coordinate of an oriented square

In its own frame, the centre of `orientedSquare t a b` has first coordinate `a`.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

lemma oriented_frame_centerX (t a b : ℝ) :
    frameX (orientedSquare t a b) (sub (orientedSquare t a b).center (0,0)) = a := by
  dsimp [frameX,orientedSquare,sub]
  linear_combination a*(Real.sin_sq_add_cos_sq t)

end SquaresInCircles.Six.Normalization
