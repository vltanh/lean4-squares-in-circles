module
public import SquaresInCircles.Six.Stress.ExactSupport

@[expose] public section

/-!
# The scalar support formula as ordinary real algebra

Sorting the two absolute force coordinates gives the exact cap/vertex formula.
This file is independent of expression syntax, interval evaluation, and all
normalization certificates. Reification for exploratory computations is kept
separately in SupportExpression.
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
  · simp only [if_pos h, min_eq_right h, max_eq_left h, sq_abs]
  · have h' : |x| ≤ |y| := (lt_of_not_ge h).le
    simp only [if_neg h, min_eq_left h', max_eq_right h', sq_abs]
    rw [show y ^ 2 + x ^ 2 = x ^ 2 + y ^ 2 by ring]
    split_ifs <;> ring

end SquaresInCircles.Six.Stress
