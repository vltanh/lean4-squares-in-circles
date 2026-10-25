module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoLowerSourceSecondary
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoLowerStripScalars

/-!
# Eight squares: source concentration on the actual short lower contact

For fixed physical angle at most .01, the original target-secondary
contact has positive second derivative in the source coordinate.
Its derivative at the actual zero-target endpoint is negative.
Thus the full feasible source interval decreases to that endpoint.
All contact and derivative formulas use the original outer circle.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerStrip

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def contact (x b : ℝ) : ℝ := lowerCut (arc b) b x
def sourceSpeed (x b : ℝ) : ℝ := ratio b*Real.cos x+Real.sin x
def contactValue (x b : ℝ) : ℝ := Real.pi/2-x-P b-V (contact x b)
def contactFirst (x b : ℝ) : ℝ :=
  -PLabel.d1 b+VLabel.d1 (contact x b)*sourceSpeed x b
def contactSecond (x b : ℝ) : ℝ :=
  -PLabel.d2 b-VLabel.d2 (contact x b)*(sourceSpeed x b)^2+
    VLabel.d1 (contact x b)*ratioD b*Real.cos x

lemma angle_mem {x : ℝ} (hx : x∈Icc 0 (1/100)) : x∈Icc 0 (7/10) :=
  ⟨hx.1,by linarith [hx.2]⟩

lemma short_cos_lower {x : ℝ} (hx : x∈Icc 0 (1/100)) :
    (19999/20000:ℝ)≤Real.cos x := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hs := pow_le_pow_left₀ hx.1 hx.2 2
  linarith

lemma arc_derivative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt arc (-ratio b) b := by
  exact ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)

lemma ratio_derivative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt ratio (ratioD b) b := by
  exact ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)

lemma contact_derivative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (contact x) (-sourceSpeed x b) b := by
  exact (((((arc_derivative hb).sub_const (1/2)).mul_const (Real.cos x)).sub
    (((hasDerivAt_id b).add_const (1/2)).mul_const (Real.sin x))).sub_const (1/2)).congr_deriv
    (by dsimp only [sourceSpeed]; ring)

lemma speed_derivative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (sourceSpeed x) (ratioD b*Real.cos x) b := by
  exact ((ratio_derivative hb).mul_const (Real.cos x)).add_const (Real.sin x)

lemma speed_positive {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<sourceSpeed x b := by
  have hr : 0<ratio b := by linarith [(outer_ratio_bounds hb).1]
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hm := mul_pos hr hc
  dsimp [sourceSpeed]
  linarith [(positive_trig hx).2.2.1]

lemma contact_antitone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    AntitoneOn (contact x) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (contact_derivative hb x).continuousAt.continuousWithinAt)
    (fun b hb => contact_derivative (Ioo_subset_Icc_self hb) x)
    (fun b hb => by linarith [speed_positive (Ioo_subset_Icc_self hb) hx])

lemma contact_upper {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : contact x b≤arc b-1 := by
  exact LowerSecondary.cut_upper (ShortOuterOne.SameContact.arc_state hb) hx

lemma contact_early {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : 0≤contact x b) :
    contact x b∈earlyTarget :=
  LowerSecondary.cut_mem (ShortOuterOne.SameContact.arc_state hb) hx hc

lemma contact_bOne {x : ℝ} (hx : x∈Icc 0 (7/10)) : contact x bOne≤0 := by
  have hh := contact_upper bOne_mem hx
  rw [bOne_arc] at hh
  linarith

lemma contactValue_hasDerivAt {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hc : contact x b∈earlyTarget) :
    HasDerivAt (contactValue x) (contactFirst x b) b := by
  have hV := (VLabel.outer_hasDerivAt (outer_domain (early_mem hc))).comp b
    (contact_derivative hb x)
  exact (((PLabel.outer_hasDerivAt (outer_domain hb)).const_sub (Real.pi/2-x)).sub hV).congr_deriv
    (by dsimp only [contactFirst]; ring)

lemma contactFirst_hasDerivAt {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hc : contact x b∈earlyTarget) :
    HasDerivAt (contactFirst x) (contactSecond x b) b := by
  have hV := (VLabel.d1_hasDerivAt (outer_domain (early_mem hc))).comp b
    (contact_derivative hb x)
  exact ((PLabel.d1_hasDerivAt (outer_domain hb)).neg.add
    (hV.mul (speed_derivative hb x))).congr_deriv (by dsimp only [contactSecond,Function.comp_apply]; ring)

lemma contactSecond_lower {b x : ℝ} (hb : b∈Icc 0 bOne)
    (hx : x∈Icc 0 (1/100)) (hc : contact x b∈earlyTarget) :
    (1/10:ℝ)<contactSecond x b := by
  have hB : b∈Icc 0 outerDiagonal := ⟨hb.1,hb.2.trans bOne_mem.2⟩
  have hP := source_second_upper hb
  have hV := target_first_lower hc
  have hD := source_ratioD_lower hB
  have hcos := short_cos_lower hx
  have hbad := mul_nonneg
    (show 0≤ -VLabel.d2 (contact x b) by linarith [V_second_upper (early_mem hc)])
    (sq_nonneg (sourceSpeed x b))
  have hprod := mul_le_mul hV.le hD.le (by norm_num : (0:ℝ)≤557/1000)
    (by linarith : 0≤VLabel.d1 (contact x b))
  have hprod0 : 0≤VLabel.d1 (contact x b)*ratioD b :=
    mul_nonneg (by linarith) (by linarith)
  have hprod' := mul_le_mul hprod hcos (by norm_num : (0:ℝ)≤19999/20000) hprod0
  dsimp [contactSecond]
  nlinarith

lemma short_speed_upper {b x : ℝ} (hb : b∈Icc 0 bOne)
    (hx : x∈Icc 0 (1/100)) : sourceSpeed x b<871/1000 := by
  have hB : b∈Icc 0 outerDiagonal := ⟨hb.1,hb.2.trans bOne_mem.2⟩
  have hp := positive_trig (angle_mem hx)
  have hr := source_ratio_upper hb
  have hr0 : 0≤ratio b := by linarith [(outer_ratio_bounds hB).1]
  have hm := mul_le_mul_of_nonneg_left hp.2.1 hr0
  dsimp [sourceSpeed]
  nlinarith [hp.2.2.2.2.1,hx.2]

lemma first_zero_negative {b x : ℝ} (hb : b∈sourceBand)
    (hx : x∈Icc 0 (1/100)) (hzero : contact x b=0) :
    contactFirst x b<0 := by
  have hB : b∈Icc 0 bOne := ⟨by linarith [hb.1],hb.2⟩
  have hp := speed_positive (band_mem hb) (angle_mem hx)
  have hs := short_speed_upper hB hx
  have hV := V_first_upper outer_zero_mem
  have hm := mul_le_mul hV.le hs.le hp.le (by norm_num : (0:ℝ)≤1061/1000)
  dsimp [contactFirst]
  rw [hzero]
  linarith [source_first_lower hb]

lemma reference_contact_positive {x : ℝ} (hx : x∈Icc 0 (1/100)) :
    0<contact x (31/40) := by
  have hu := source_reference_radical.1
  have hc := short_cos_lower hx
  have hs : Real.sin x≤1/100 :=
    (positive_trig (angle_mem hx)).2.2.2.2.1.trans hx.2
  have hmul := mul_le_mul
    (show (25663/50000:ℝ)≤U (31/40)-1 by linarith)
    hc (by norm_num : (0:ℝ)≤19999/20000)
    (by linarith : 0≤U (31/40)-1)
  have hsin := mul_le_mul_of_nonneg_left hs
    (by norm_num : (0:ℝ)≤51/40)
  have he : contact x (31/40)=(U (31/40)-1)*Real.cos x-(51/40)*Real.sin x-1/2 := by
    simp only [contact,lowerCut,U]
    ring
  rw [he]
  linarith

lemma zero_endpoint_band {x β : ℝ} (hx : x∈Icc 0 (1/100))
    (hβ : β∈Icc 0 bOne) (hz : contact x β=0) : β∈sourceBand := by
  refine ⟨?_,hβ.2⟩
  by_contra h
  have horder : β≤31/40 := by linarith
  have hm := contact_antitone (angle_mem hx)
    ⟨hβ.1,hβ.2.trans bOne_mem.2⟩ source_reference_mem horder
  rw [hz] at hm
  linarith [reference_contact_positive hx]

lemma zero_contact_value {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hz : contact x b=0) :
    contactValue x b=axisValue b := by
  have hzero : NegativeTwo.TargetContact.B b x=0 := by
    change 1/2-(arc b-1/2)*Real.cos x+(b+1/2)*Real.sin x=0
    dsimp [contact,lowerCut] at hz
    linarith
  have hd : NegativeTwo.TargetContact.Domain b x :=
    ⟨hb,hx,by rw [hzero]; exact outer_zero_mem⟩
  have he := NegativeTwo.ContactInverse.original_angle hd
  rw [hzero] at he
  norm_num at he
  unfold contactValue axisValue
  rw [hz,he]

end SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerStrip

