import SquaresInCircles.Six.Stress.ExactSupport

/-!
# The support with `max` and `min`

`scalarSupport R x y`, written with `max |x| |y|` and `min |x| |y|` in place of
the sorting of `|x|` and `|y|`: the cap value `rhoAt R * max |x| |y|` when
`2 R min |x| |y| ≤ sqrt (x^2 + y^2)`, and the far-vertex value
`R sqrt (x^2 + y^2) - (|x| + |y|)/2` otherwise.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress

lemma scalarSupport_max_min (R x y : ℝ) :
    scalarSupport R x y =
      if 2 * R * min |x| |y| ≤ Real.sqrt (x ^ 2 + y ^ 2) then
        rhoAt R * max |x| |y|
      else R * Real.sqrt (x ^ 2 + y ^ 2) - (|x| + |y|) / 2 := by
  unfold scalarSupport orderedSupport
  by_cases h : |y| ≤ |x|
  · simp only [ite_eq_left h, min_eq_right h, max_eq_left h, sq_abs]
  · have h' : |x| ≤ |y| := (lt_of_not_ge h).le
    simp only [ite_eq_right h, min_eq_left h', max_eq_right h', sq_abs]
    rw [show y ^ 2 + x ^ 2 = x ^ 2 + y ^ 2 by ring]
    split_ifs <;> ring

end SquaresInCircles.Six.Stress
