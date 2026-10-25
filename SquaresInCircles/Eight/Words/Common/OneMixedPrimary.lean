module

public import SquaresInCircles.Eight.Words.Common.OneOuterPrimary

/-!
# Eight squares: the remaining outer-to-core primary contacts at one quarter

The original weak primary contact forces the angle and transverse cuts
needed at the tight side endpoint. The corner is controlled by a whole
quadratic consequence of a sloping circle support. Both negative tangents
use the exact aligned baseline and a single concave trigonometric change.
All cuts are derived from the original coordinates and owner inequality.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

open Arithmetic

/-- The second-order cosine lower bound, in the form the proofs below cite. -/
private theorem r4_cos_lower_two {x : ℝ} (_hx : 0≤x) : 1-x^2/2≤Real.cos x :=
  Real.one_sub_sq_div_two_le_cos

def corePrimaryChange (x : ℝ) : ℝ :=
  x+(291/250)*(oneWidth x-1)-(679/1000)*Real.sin x

def coreNegativeChange (z : ℝ) : ℝ :=
  -z+(291/500)*(Real.cos z-1)+(1261/1000)*Real.sin z

lemma core_primary_lower {A B : ℝ} (h : CorePairGeometry.CoreState A B) :
    (279/500:ℝ)<A := by
  have hh := core_diagonal_lower (X := (1:ℝ)) (Y := (0:ℝ)) h (by norm_num) (by norm_num)
  norm_num at hh
  linarith [CoreAngleEndpoint.diagonal_bounds.1]

lemma one_core_source_support {a b : ℝ} (hs : OuterState a b) :
    303/250-radius*OneEnvelope.N (291/250) 0≤ -outerLabel a b-(291/250)*a := by
  have hh := outer_circle_lower (X := -(1229/1000:ℝ)) (Y := -(203/200:ℝ)) hs
  have he : Real.sqrt ((-(1229/1000:ℝ))^2+(-(203/200:ℝ))^2)=
      OneEnvelope.N (291/250) 0 := by
    dsimp [OneEnvelope.N,CircularNorm.norm]
    rw [OneEnvelope.energy_identity]
    norm_num
  rw [he] at hh
  dsimp [outerLabel]
  linarith

lemma core_primary_change_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0≤corePrimaryChange x := by
  have tr := positive_trig hx
  have hs := Real.sin_le hx.1
  have hc := r4_cos_lower_two hx.1
  have hxx := mul_le_mul_of_nonneg_right hx.2 hx.1
  dsimp [corePrimaryChange,oneWidth]
  rw [abs_of_nonneg tr.2.2.1]
  nlinarith

lemma core_primary_change_negative {z : ℝ} (hz : z∈Icc 0 (7/10)) :
    corePrimaryChange (-z)=coreNegativeChange z := by
  have ht := positive_trig hz
  dsimp [corePrimaryChange,coreNegativeChange,oneWidth]
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg ht.2.2.1]
  ring

lemma core_negative_change_nonneg {z : ℝ} (hz : z∈Icc 0 (3/5)) :
    0≤coreNegativeChange z := by
  have hs := Real.sin_ge_sub_cube hz.1
  have hc := r4_cos_lower_two hz.1
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz3 := mul_le_mul_of_nonneg_right hz2 hz.1
  have hzz := mul_le_mul_of_nonneg_right hz.2 hz.1
  dsimp [coreNegativeChange]
  nlinarith

lemma core_negative_change_lower {z : ℝ} (hz : z∈Icc (3/5) (7/10)) :
    -(1/40:ℝ)<coreNegativeChange z := by
  have hh := trig_concave_gt (α := (-1:ℝ)) (A := (1261/1000:ℝ))
    (B := (291/500:ℝ)) (m := (291/500)-(1/40)) (l := (3/5:ℝ)) (u := (7/10:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three]) hz
    (by linarith [primary_fixed_trig.2.2.2.2.1,primary_fixed_trig.2.2.2.2.2.1])
    (by linarith [cap_trig.1,cap_trig.2.2.1])
  dsimp [coreNegativeChange]
  linarith

/-- The actual large negative angle forces positive target transverse
reserve; it is not supplied as an additional leaf hypothesis. -/
lemma one_mixed_negative_large_cut {a b A B z : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B)
    (hz : z∈Icc (3/5) (7/10))
    (hm : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2-z)) :
    (11/100:ℝ)<B ∧ (87/500:ℝ)<1-Real.cos z := by
  have hz' : z∈Icc 0 (7/10) := ⟨by linarith [hz.1],hz.2⟩
  have hx : |-z|≤7/10 := by rw [abs_neg,abs_of_nonneg hz'.1]; exact hz.2
  have tr := positive_trig hz'
  have hsm := sin_mono (show (3/5:ℝ)∈Icc 0 (7/10) by norm_num) hz' hz.1
  have hcm := cos_anti (show (3/5:ℝ)∈Icc 0 (7/10) by norm_num) hz' hz.1
  have hwm := sine_cosine_mono (show (3/5:ℝ)∈Icc 0 (7/10) by norm_num) hz' hz.1
  have hsin : (141/250:ℝ)<Real.sin z := by
    linarith [primary_fixed_trig.2.2.2.2.1]
  have hcos : Real.cos z<(413/500:ℝ) := by
    linarith [primary_fixed_trig.2.2.2.2.2.2]
  have hwidth : (2389/2000:ℝ)<(1+Real.cos z+Real.sin z)/2 := by
    linarith [primary_fixed_trig.2.2.2.2.1,primary_fixed_trig.2.2.2.2.2.1]
  have hA := core_primary_lower ht
  have hAs := mul_le_mul_of_nonneg_right hA.le tr.2.2.1
  have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
  have hm' : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+(-z)) := by
    simpa [sub_eq_add_neg] using hm
  rw [one_primary_margin hx] at hm'
  dsimp [oneWidth] at hm'
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hm'
  have hBc := mul_le_mul_of_nonneg_left hcos.le (CoreAngleEndpoint.state_bounds ht).2.2.1
  constructor <;> nlinarith

lemma one_mixed_negative_lower {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x)) :
    OneEnvelope.envelope .core 0+corePrimaryChange x+
      (291/250)*B*(1-Real.cos x)≤Real.pi/2+x-outerLabel a b+coreLabel A B := by
  have hsource := one_core_source_support hs
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have hsin := signed_sin hx
  have hcoef : 0≤(73/10)+(291/250)*Real.sin x := by
    have hh := neg_le_abs (Real.sin x)
    linarith
  have htarget := mul_nonneg hcoef (show 0≤7/12-A by linarith)
  rw [one_primary_margin hx] at hm
  have hm' := mul_nonneg (show (0:ℝ)≤291/250 by norm_num) hm
  dsimp [OneEnvelope.envelope,OneEnvelope.weight,OneEnvelope.offset,corePrimaryChange,coreLabel]
  norm_num
  nlinarith

theorem one_outer_core_negative_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-outerLabel a b+coreLabel A B := by
  have hlow := one_mixed_negative_lower hs ht hx hm
  have hb := (CoreAngleEndpoint.state_bounds ht).2.2.1
  have hextra := mul_nonneg hb (sub_nonneg.mpr (Real.cos_le_one x))
  by_cases hp : 0≤x
  · have hchange := core_primary_change_positive ⟨hp,(abs_le.mp hx).2⟩
    nlinarith [OneEnvelope.core_baseline]
  · let z : ℝ := -x
    have hz : z∈Icc 0 (7/10) := ⟨by dsimp [z]; linarith,
      by dsimp [z]; linarith [(abs_le.mp hx).1]⟩
    have he : x= -z := by dsimp [z]; ring
    rw [he,core_primary_change_negative hz,Real.cos_neg] at hlow
    by_cases hsmall : z≤3/5
    · have hc := core_negative_change_nonneg ⟨hz.1,hsmall⟩
      have hpositive := mul_nonneg hb (sub_nonneg.mpr (Real.cos_le_one z))
      nlinarith [OneEnvelope.core_baseline]
    · have hz' : z∈Icc (3/5) (7/10) := ⟨by linarith,hz.2⟩
      have hcut := one_mixed_negative_large_cut hs ht hz'
        (by simpa [he,sub_eq_add_neg] using hm)
      have hprod := (mul_lt_mul_of_pos_left hcut.2
        (by norm_num : (0:ℝ)<11/100)).trans
          (mul_lt_mul_of_pos_right hcut.1
            (show 0<1-Real.cos z by linarith [hcut.2]))
      have hc := core_negative_change_lower hz'
      nlinarith [OneEnvelope.core_baseline]

lemma one_corner_positive_primary_angle {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B) (hB : 1/2≤B)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) : (3/10:ℝ)<x := by
  have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
  have hc := CoreAngleEndpoint.state_bounds ht
  have hp : 0<x := by
    by_contra! hn
    have hz : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    have tr := positive_trig hz
    have hA : 1/2≤A := hB.trans hc.2.2.2.1
    have hAs := mul_le_mul_of_nonneg_right hA tr.2.2.1
    have hBc := mul_le_mul_of_nonneg_right hB (by linarith [tr.1] : 0≤Real.cos (-x))
    have hw := oneWidth_ge_one hx
    rw [one_primary_margin hx] at hm
    simp only [Real.cos_neg,Real.sin_neg] at hAs hBc
    have hsum := tr.2.2.2.2.2
    simp only [Real.cos_neg,Real.sin_neg] at hsum
    nlinarith
  have tr := positive_trig ⟨hp.le,(abs_le.mp hx).2⟩
  have hAs := mul_le_mul_of_nonneg_right hc.2.1 tr.2.2.1
  have hBc := mul_le_mul_of_nonneg_right hB (by linarith [tr.1] : 0≤Real.cos x)
  rw [one_primary_margin hx] at hm
  dsimp [oneWidth] at hm
  rw [abs_of_nonneg tr.2.2.1] at hm
  by_contra! hsmall
  have hcos := r4_cos_lower_two hp.le
  have hsin := Real.sin_le hp.le
  have hx2 := pow_le_pow_left₀ hp.le hsmall 2
  nlinarith

lemma one_outer_core_corner_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B) (hB : 1/2≤B)
    (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-outerLabel a b-coreLabel A B := by
  have hangle := one_corner_positive_primary_angle hs ht hB hx hm
  have hp : 0≤x := by linarith
  have tr := positive_trig ⟨hp,(abs_le.mp hx).2⟩
  have hc := CoreAngleEndpoint.state_bounds ht
  have hAs := mul_le_mul_of_nonneg_right hc.2.1 tr.2.2.1
  have hBc := mul_le_mul_of_nonneg_right hB (by linarith [tr.1] : 0≤Real.cos x)
  have hsloping := outer_sloping_upper hs
  rw [one_primary_margin hx] at hm
  dsimp [oneWidth] at hm
  rw [abs_of_nonneg tr.2.2.1] at hm
  have hb : b<(533/350)-(10/7)*Real.cos x+(5/42)*Real.sin x := by nlinarith
  have hsL := (outer_label_error hs).2
  have htL := (core_label_bounds ht).2
  have hcos := r4_cos_lower_two hp
  have hsin := Real.sin_le hp
  have hproduct := mul_nonneg (show 0≤x-3/10 by linarith)
    (show 0≤7/10-x by linarith [(abs_le.mp hx).2])
  have hpoly : (1/5:ℝ)≤(37/42)*x-(5/7)*x^2 := by nlinarith
  nlinarith [pi_hand_enclosure.1]

lemma one_mixed_side_lower {a b B x : ℝ} (hs : OuterState a b) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2+x)) :
    OneEnvelope.envelope .core 0+corePrimaryChange x-(291/250)*B*(1-Real.cos x)≤
      Real.pi/2+x-outerLabel a b-coreLabel (7/12) B := by
  have hsource := one_core_source_support hs
  rw [one_primary_margin hx] at hm
  have hm' := mul_nonneg (show (0:ℝ)≤291/250 by norm_num) hm
  dsimp [OneEnvelope.envelope,OneEnvelope.weight,OneEnvelope.offset,corePrimaryChange,coreLabel]
  norm_num
  nlinarith

lemma one_side_positive_change {x B : ℝ} (hx : x∈Icc 0 (7/10)) (hB : 0≤B ∧ B≤1/2) :
    0≤corePrimaryChange x-(291/250)*B*(1-Real.cos x) := by
  have tr := positive_trig hx
  have hBc := mul_le_mul_of_nonneg_right hB.2
    (sub_nonneg.mpr (Real.cos_le_one x))
  have hs := Real.sin_le hx.1
  have hc := r4_cos_lower_two hx.1
  have hxx := mul_le_mul_of_nonneg_right hx.2 hx.1
  dsimp [corePrimaryChange,oneWidth]
  rw [abs_of_nonneg tr.2.2.1]
  nlinarith

lemma one_side_negative_angle_cut {a b B z : ℝ} (hs : OuterState a b)
    (hB : 0≤B ∧ B≤1/2) (hz : z∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2-z)) : z<1/2 := by
  have hx : |-z|≤7/10 := by rw [abs_neg,abs_of_nonneg hz.1]; exact hz.2
  have tr := positive_trig hz
  have hBc := mul_nonneg hB.1 (by linarith [tr.1] : 0≤Real.cos z)
  have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
  have hm' : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2+(-z)) := by
    simpa [sub_eq_add_neg] using hm
  rw [one_primary_margin hx] at hm'
  dsimp [oneWidth] at hm'
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hm'
  by_contra! hlarge
  have hh := trig_concave_gt (α := 0) (A := (13/12:ℝ)) (B := (1/2:ℝ))
    (m := (183/200:ℝ)) (l := (1/2:ℝ)) (u := (7/10:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
    (show z∈Icc (1/2) (7/10) from ⟨hlarge,hz.2⟩)
    (by linarith [primary_fixed_trig.2.2.1,primary_fixed_trig.2.2.2.1])
    (by linarith [cap_trig.1,cap_trig.2.2.1])
  nlinarith

lemma one_side_negative_transverse_cut {a b B z : ℝ} (hs : OuterState a b)
    (hB : 0≤B ∧ B≤1/2) (hz : z∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2-z)) : B<83/200 := by
  have hx : |-z|≤7/10 := by rw [abs_neg,abs_of_nonneg hz.1]; exact hz.2
  have tr := positive_trig hz
  have hfirst := mul_nonneg (show 0≤7/12-B by linarith [hB.2]) tr.2.2.1
  have hsecond := mul_nonneg (show 0≤B+1/2 by linarith [hB.1])
    (show 0≤Real.sin z+Real.cos z-1 by linarith [tr.2.2.2.2.2])
  have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
  have hm' : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2+(-z)) := by
    simpa [sub_eq_add_neg] using hm
  rw [one_primary_margin hx] at hm'
  dsimp [oneWidth] at hm'
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hm'
  nlinarith

lemma one_side_negative_small_change {B z : ℝ} (hz : z∈Icc 0 (2/5))
    (hB : 0≤B ∧ B≤83/200) :
    0≤coreNegativeChange z-(291/250)*B*(1-Real.cos z) := by
  have hs := Real.sin_ge_sub_cube hz.1
  have hc := r4_cos_lower_two hz.1
  have hBc := mul_le_mul_of_nonneg_right hB.2 (sub_nonneg.mpr (Real.cos_le_one z))
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hz3 := mul_le_mul_of_nonneg_right hz2 hz.1
  have hzz := mul_le_mul_of_nonneg_right hz.2 hz.1
  dsimp [coreNegativeChange]
  nlinarith

lemma one_side_negative_middle_cut {a b B z : ℝ} (hs : OuterState a b)
    (hB : 0≤B ∧ B≤1/2) (hz : z∈Icc (2/5) (1/2))
    (hm : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2-z)) : B<1/25 := by
  have hz' : z∈Icc 0 (7/10) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hx : |-z|≤7/10 := by rw [abs_neg,abs_of_nonneg hz'.1]; exact hz'.2
  have tr := positive_trig hz'
  have hcm := cos_anti hz' (show (1/2:ℝ)∈Icc 0 (7/10) by norm_num) hz.2
  have hc : (7/8:ℝ)≤Real.cos z := by linarith [primary_fixed_trig.2.2.2.1]
  have hBc := mul_le_mul_of_nonneg_left hc hB.1
  have hh := trig_concave_gt (α := 0) (A := (13/12:ℝ)) (B := (1/2:ℝ))
    (m := (22/25:ℝ)) (l := (2/5:ℝ)) (u := (1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three]) hz
    (by linarith [primary_fixed_trig.1,primary_fixed_trig.2.1])
    (by linarith [primary_fixed_trig.2.2.1,primary_fixed_trig.2.2.2.1])
  have ha := (outer_bounds hs).2.1.trans_lt outer_endpoint_bounds.2.1
  have hm' : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2+(-z)) := by
    simpa [sub_eq_add_neg] using hm
  rw [one_primary_margin hx] at hm'
  dsimp [oneWidth] at hm'
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1] at hm'
  nlinarith

lemma one_outer_core_side_primary {a b B x : ℝ} (hs : OuterState a b)
    (hB : 0≤B ∧ B≤1/2) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-outerLabel a b-coreLabel (7/12) B := by
  have hlow := one_mixed_side_lower hs hx hm
  by_cases hp : 0≤x
  · have hchange := one_side_positive_change ⟨hp,(abs_le.mp hx).2⟩ hB
    linarith [OneEnvelope.core_baseline]
  · let z : ℝ := -x
    have hz : z∈Icc 0 (7/10) := ⟨by dsimp [z]; linarith,
      by dsimp [z]; linarith [(abs_le.mp hx).1]⟩
    have he : x= -z := by dsimp [z]; ring
    have hm' : 0≤forwardMargin 3 a b (7/12) B (-1) 1 (Real.pi/2-z) := by
      simpa [he,sub_eq_add_neg] using hm
    have hangle := one_side_negative_angle_cut hs hB hz hm'
    rw [he,core_primary_change_negative hz,Real.cos_neg] at hlow
    by_cases hsmall : z≤2/5
    · have hcut := one_side_negative_transverse_cut hs hB hz hm'
      have hchange := one_side_negative_small_change ⟨hz.1,hsmall⟩ ⟨hB.1,hcut.le⟩
      linarith [OneEnvelope.core_baseline]
    · have hcut := one_side_negative_middle_cut hs hB
        ⟨by linarith,hangle.le⟩ hm'
      have hchange := core_negative_change_nonneg ⟨hz.1,by linarith⟩
      have hBc := mul_le_mul_of_nonneg_right hcut.le
        (sub_nonneg.mpr (Real.cos_le_one z))
      have hc := r4_cos_lower_two hz.1
      have hz2 := pow_le_pow_left₀ hz.1 hangle.le 2
      have hextra : (291/250)*B*(1-Real.cos z)≤291/50000 := by nlinarith
      nlinarith [OneEnvelope.core_baseline]

theorem one_outer_core_positive_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B) (hx : |x|≤7/10)
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (157/200:ℝ)<Real.pi/2+x-outerLabel a b-coreLabel A B := by
  rcases ht with ⟨rfl,hB0,hB1⟩ | ⟨hB0,hBA,hcircle⟩
  · exact one_outer_core_side_primary hs ⟨hB0,hB1⟩ hx hm
  · exact one_outer_core_corner_primary hs (Or.inr ⟨hB0,hBA,hcircle⟩) hB0 hx hm

end SquaresInCircles.Eight.CommonQuarter
