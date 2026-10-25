module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoData
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoLabels

/-!
# Eight squares: the first two original weak axes on the whole negative-quarter window

The target circle supplies an affine primary-coordinate decrease.  It
combines with the target label's slope to pay its full original transverse
coordinate.  The remaining angle inequality follows from a whole-interval
quadratic Taylor support.  The second lower axis implies the axial first
axis; its upper half uses the original angle and a direct small-source cut.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma target_primary_decrease {A B : ℝ} (ht : OuterState A B) :
    A+(261/1000)*B≤outerAxial := by
  have hA := primary_mem ht
  have hD : 0≤outerAxial-A := sub_nonneg.mpr hA.2
  have hz := (ShortOuterOne.SameContact.arc_state outer_zero_mem).2.2
  rw [ShortOuterOne.SameContact.arc_zero] at hz
  have he : (outerAxial-A)*(outerAxial+A+1)=B^2+B := by
    linear_combination hz-ht.2.2
  have hupper : outerAxial+A+1≤383/100 := by
    linarith [hA.2,outer_endpoint_bounds.2.1]
  have hm := mul_le_mul_of_nonneg_left hupper hD
  nlinarith [sq_nonneg B,ht.1]

def firstBase (x : ℝ) : ℝ :=
  Real.pi/2-x-1239/50000+167/10000+853/2000+
    (853/2000)*Real.sin x-(853/1000)*(outerAxial-1/2)*Real.cos x

lemma first_base_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (19/20:ℝ)<firstBase x := by
  have ht := positive_trig hx
  have hs := positive_taylor_reserves hx
  have hc0 : 0≤Real.cos x := by linarith [ht.1]
  have hrad : (outerAxial-1/2)*Real.cos x≤(183/200)*Real.cos x := by
    apply mul_le_mul_of_nonneg_right _ hc0
    linarith [outer_endpoint_bounds.2.1]
  have hfactor : 0≤(12323/20000:ℝ)-(183/500)*(x+7/10) := by
    linarith [hx.2]
  have hpoly := mul_nonneg (show 0≤(7/10:ℝ)-x by linarith [hx.2]) hfactor
  dsimp [firstBase]
  nlinarith [pi_hand_enclosure.1,sq_nonneg x]

theorem original_lower_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2-x)) :
    (19/20:ℝ)<value b B (Real.pi/2-x) := by
  have hw := lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  have hc := positive_trig hx
  have hP := P_chord (source_mem hs)
  have hT := T_increment_lower outer_zero_mem (source_mem ht) ht.1
  rw [T_zero] at hT
  have hA := mul_le_mul_of_nonneg_right (target_primary_decrease ht)
    (show 0≤Real.cos x by linarith [hc.1])
  have hpay : 0≤(609/1000:ℝ)+(853/1000)*(261/1000)*Real.cos x-
      (853/1000)*Real.sin x := by
    linarith [hc.1,hc.2.2.2.1]
  have hcharge := mul_nonneg ht.1 hpay
  have hbase := first_base_lower hx
  dsimp [value,firstBase] at *
  nlinarith

theorem original_upper_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2+x)) :
    (19/20:ℝ)<value b B (Real.pi/2+x) := by
  have hu := upper_width hx
  have hl := lower_width hx
  have hBS := mul_nonneg ht.1 (positive_trig hx).2.2.1
  have hminus : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2-x) := by
    norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,Real.sin_add,Real.cos_add,
      hu,hl] at hm ⊢
    nlinarith
  have hh := original_lower_source_secondary hs ht hx hminus
  dsimp [value] at *
  linarith [hx.1]

lemma lower_second_implies_axial_first {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) (-1) (Real.pi/2-x)) :
    0≤Eight.forwardMargin 0 a b outerAxial 0 (-1) (-1) (Real.pi/2-x) := by
  have hw := lower_width hx
  have hc := positive_trig hx
  have hsin0 := hc.2.2.1
  have hcos0 : 0<Real.cos x := by linarith [hc.1]
  have ha := mul_le_mul_of_nonneg_right (primary_mem hs).1 hsin0
  have hA := (primary_mem ht).2
  have hcut : b*Real.cos x≤outerAxial-outerDiagonal*Real.sin x-
      (1+Real.cos x+Real.sin x)/2 := by
    norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
    linarith
  have hprod := mul_le_mul_of_nonneg_right
    (show outerAxial-1/2≤(183/200:ℝ) by linarith [outer_endpoint_bounds.2.1]) hsin0
  have hbracket : 0≤outerDiagonal+1/2-Real.cos x/2-
      (outerAxial-1/2)*Real.sin x := by
    linarith [fine_outer_endpoint_bounds.2,hc.2.1,hc.2.2.2.1]
  have hpay := mul_nonneg hsin0 hbracket
  have hid : (outerAxial*Real.cos x-(1+Real.cos x+Real.sin x)/2)*Real.cos x-
      (outerAxial-outerDiagonal*Real.sin x-(1+Real.cos x+Real.sin x)/2)=
        Real.sin x*(outerDiagonal+1/2-Real.cos x/2-
          (outerAxial-1/2)*Real.sin x) := by
    linear_combination (outerAxial-1/2)*(Real.sin_sq_add_cos_sq x)
  have hb : b≤outerAxial*Real.cos x-(1+Real.cos x+Real.sin x)/2 := by
    nlinarith
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw]
  linarith

theorem original_lower_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) (-1) (Real.pi/2-x)) :
    (19/20:ℝ)<value b B (Real.pi/2-x) := by
  have hz : OuterState outerAxial 0 := by
    simpa only [ShortOuterOne.SameContact.arc_zero] using
      ShortOuterOne.SameContact.arc_state outer_zero_mem
  have hf := original_lower_source_secondary hs hz hx
    (lower_second_implies_axial_first hs ht hx hm)
  have hT := T_lower (source_mem ht)
  dsimp [value] at *
  rw [T_zero] at hf
  linarith

lemma upper_second_small_source {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (11/100))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) (-1) (Real.pi/2+x)) :
    b<3/5 := by
  have hcap : x∈Icc 0 (7/10) := ⟨hx.1,by linarith [hx.2]⟩
  have hw := upper_width hcap
  have htrig := positive_trig hcap
  have hsine : Real.sin x≤11/100 := htrig.2.2.2.2.1.trans hx.2
  have hcosine : (19879/20000:ℝ)≤Real.cos x := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := x)
    have hsq := pow_le_pow_left₀ hx.1 hx.2 2
    nlinarith
  have hprod := mul_le_mul (primary_mem hs).2 hsine htrig.2.2.1
    (by linarith [outer_endpoint_bounds.1] : 0≤outerAxial)
  have hA := (primary_mem ht).2
  have hbpos := hs.1
  have hcosprod := mul_le_mul_of_nonneg_left hcosine hbpos
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  nlinarith [outer_endpoint_bounds.2.1,htrig.2.2.2.2.2]

theorem original_upper_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) (-1) (Real.pi/2+x)) :
    (9/10:ℝ)<value b B (Real.pi/2+x) := by
  have hT := T_lower (source_mem ht)
  by_cases hsmall : x≤11/100
  · have hb := upper_second_small_source hs ht ⟨hx.1,hsmall⟩ hm
    have hP := P_chord (source_mem hs)
    dsimp [value]
    linarith [pi_hand_enclosure.1,hx.1]
  · have hP := P_monotone (source_mem hs) ⟨outer_zero_mem.2,le_rfl⟩ (source_mem hs).2
    have hp := P_diagonal_upper
    dsimp [value]
    linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.SecondWord.NegativeTwo
