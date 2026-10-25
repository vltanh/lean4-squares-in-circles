module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetDiagonalReferences

/-!
# The J diagonal is concave on the written extended angle interval

Uncompiled source draft.  This is the second-derivative estimate in
§8.2 of the original mixed-zero proof, with its two named endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.JDiagonal
open CommonQuarter CorePairGeometry Arithmetic

lemma second_negative {x : ℝ} (hx : x∈angles) : H₂ 0 x<0 := by
  have hb := Shape.diagonal_band hx
  have h1 := Shape.J_first_bounds hb
  have h2 := Shape.J_second_upper hb
  have hw := speed_bounds hx
  have hv : 1/2-diagonal x≤(59/1000:ℝ) := by linarith [(diagonal_bounds hx).1]
  have hp := mul_le_mul_of_nonneg_right h2.le (sq_nonneg (speed x))
  have hq := mul_le_mul_of_nonneg_left hv (show 0≤JLabel.d1 (diagonal x) by linarith [h1.1])
  norm_num [H₂,F]
  nlinarith [hw.2.2.1,h1.2]

lemma lower {x : ℝ} (hx : x∈angles) : (17953/20000:ℝ)<H 0 x := by
  have hc : ConcaveOn ℝ angles (H 0) :=
    concave_of_deriv2 (fun t ht => H_hasDerivAt 0 ht)
      (fun t ht => H₁_hasDerivAt 0 ht) (fun t ht => (second_negative ht).le)
  exact concave_gt_of_endpoints hc hx
    (by linarith [LabelReferences.initial.2.2.2.2])
    (by linarith [DiagonalReferences.J_cap])

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.JDiagonal
