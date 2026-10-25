module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeData

/-!
# Eight squares: original positive outer owner order below the quarter turn

Subtracting the two physical circle equations compares the two cross coordinate gaps; their
ratio is greater than one half (`cross_gap_half`). The whole lower angle window satisfies
`1-sin φ ≤ cos φ/2` (`lower_half_angle`), so its original target-primary projection is no larger
than its source-secondary projection (`lower_second_implies_first`). Weak equality cases are
included.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic

lemma cross_gap_half {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    (A-b)/2≤a-B := by
  have ha := NegativeTwo.primary_mem hs
  have hb := NegativeTwo.source_mem hs
  have hA := NegativeTwo.primary_mem ht
  have hB := NegativeTwo.source_mem ht
  have hx : 0≤a-B := by linarith [ha.1,hB.2]
  have hy : 0≤A-b := by linarith [hA.1,hb.2]
  have he : (a-B)*(a+B+1)=(A-b)*(A+b+1) := by
    nlinarith [hs.2.2,ht.2.2]
  have hu : a+B+1≤(17/5:ℝ) := by
    linarith [ha.2,hB.2,outer_endpoint_bounds.2.1,outer_endpoint_bounds.2.2.2]
  have hl : (9/5:ℝ)≤A+b+1 := by
    linarith [hA.1,hb.1,fine_outer_endpoint_bounds.2]
  have hp := mul_nonneg hx (sub_nonneg.mpr hu)
  have hq := mul_nonneg hy (sub_nonneg.mpr hl)
  nlinarith

lemma lower_half_angle {φ : ℝ} (hφ : Lower φ) :
    1-Real.sin φ≤Real.cos φ/2 := by
  have hx := lower_deviation hφ
  have ht := positive_taylor_reserves hx
  have hsq := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  simp only [Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,sub_zero] at ht
  nlinarith [hx.1]

lemma lower_second_le_first {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ) :
    Eight.forwardMargin 1 a b A B 1 1 φ≤Eight.forwardMargin 0 a b A B 1 1 φ := by
  have hg := cross_gap_half hs ht
  have ha := lower_half_angle hφ
  have hc := (lower_trig hφ).2.2.1
  have hy : 0≤A-b := by
    linarith [(NegativeTwo.primary_mem ht).1,(NegativeTwo.source_mem hs).2]
  have hp := mul_nonneg hy (sub_nonneg.mpr ha)
  have hq := mul_nonneg (sub_nonneg.mpr hg) hc
  norm_num [Eight.forwardMargin]
  nlinarith

theorem lower_second_implies_first {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 1 a b A B 1 1 φ) :
    0≤Eight.forwardMargin 0 a b A B 1 1 φ :=
  hm.trans (lower_second_le_first hs ht hφ)

end SquaresInCircles.Eight.SecondWord.PositiveThree
