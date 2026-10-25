module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoAligned

/-!
# Eight squares: the original upper target-secondary owner by finite coordinate comparison

Its original weak separator permits at most `.4*x` of target-coordinate loss from alignment. The
target slope costs less than `1.069` per unit of that coordinate, while the original angle
contributes the full `x`. The aligned bound therefore applies to the original squares themselves
(`original_upper_target_secondary`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma upper_target_displacement {a b x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10)) :
    1-a-upperTarget a b x≤(2/5)*x := by
  have ht := positive_trig hx
  have hc := mul_nonneg
    (show 0≤a-1/2 by linarith [(primary_mem hs).1,fine_outer_endpoint_bounds.2])
    (sub_nonneg.mpr ht.2.1)
  have hsine := mul_le_mul_of_nonneg_right
    (show b-1/2≤(2/5:ℝ) by linarith [(source_mem hs).2,outer_endpoint_bounds.2.2.2])
    ht.2.2.1
  have hxsin := mul_le_mul_of_nonneg_left ht.2.2.2.2.1 (by norm_num : (0:ℝ)≤2/5)
  dsimp [upperTarget]
  nlinarith

theorem original_upper_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2+x)) :
    (8977827/10000000:ℝ)<value b B (Real.pi/2+x) := by
  have hcut := upper_target_cut hx hm
  have hdisp : 1-a-B≤(2/5)*x := by
    linarith [upper_target_displacement hs hx]
  by_cases ha : 1≤a
  · have hbase := original_aligned hs ht (by linarith [ht.1])
    dsimp [value] at *
    linarith [hx.1]
  · have hdom := aligned_domain ⟨(primary_mem hs).1,by linarith⟩
    have hs0 := ShortOuterOne.SameContact.arc_state hdom.2.1
    have hbase := original_aligned hs hs0 (show 1≤a+(1-a) by linarith)
    by_cases hB : 1-a≤B
    · have hT := T_monotone hdom.2.1 (source_mem ht) hB
      dsimp [value] at *
      linarith [hx.1]
    · have hT := T_increment_upper (source_mem ht) hdom.2.1 (by linarith)
      dsimp [value] at *
      nlinarith [hx.1]

end SquaresInCircles.Eight.SecondWord.NegativeTwo
