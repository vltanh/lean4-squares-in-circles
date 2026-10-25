module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoAxialCalculus

/-!
# A single exact reference and the full opposite-quarter axial bound

The reference is the rational transverse coordinate .56615.  Its
inverse angle is bounded by a zero of the original contact equation,
using alternating Taylor bounds at .150171.  Actual circle squares
give its value and derivative.  Uniform curvature then covers the
whole circle.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.Axial

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def reference : ℝ := 11323/20000
def referenceAngle : ℝ := 150171/1000000

lemma reference_mem : reference∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num [reference])

lemma reference_late : reference∈Icc (1/5) outerDiagonal :=
  ⟨by norm_num [reference],reference_mem.2⟩

lemma reference_radical :
    (16670105511/10000000000:ℝ)<U reference ∧
      U reference<2083763189/1250000000 :=
  Asymmetric.shifted_reference reference_mem
    (by norm_num) (by norm_num) (by norm_num [reference,W,Q0])
    (by norm_num [reference,W,Q0])

lemma reference_q :
    (988486811/625000000:ℝ)<Inverse.q (U reference) ∧
      Inverse.q (U reference)<7907894489/5000000000 := by
  have hh := reference_radical
  norm_num [Inverse.q,NegativeTwo.Inverse.q,Q0]
  constructor <;> linarith

lemma reference_ratio :
    (1279116079/2000000000:ℝ)<ratio reference ∧
      ratio reference<7994475495/12500000000 := by
  have hh := reference_radical
  have hp := U_positive (outer_domain reference_mem)
  have hw : W reference=21323/20000 := by norm_num [W,reference]
  change (1279116079/2000000000:ℝ)<W reference/U reference ∧
    W reference/U reference<7994475495/12500000000
  rw [hw]
  constructor
  · apply (lt_div_iff₀ hp).2
    linarith [hh.2]
  · apply (div_lt_iff₀ hp).2
    linarith [hh.1]

lemma reference_speed :
    (11539405953/10000000000:ℝ)<speed (-(1/2)) reference ∧
      speed (-(1/2)) reference<2307881191/2000000000 := by
  have hd := NegativeTwo.ContactInverse.data reference_mem
    (show (-(1/2:ℝ))∈Icc (-(1/2)) (2/5) by norm_num)
  have hq := reference_q
  constructor <;> nlinarith [hd.2.2.2.2.1,hd.2.2.2.2.2]

lemma reference_factor :
    (8528663/10000000:ℝ)<Inverse.factor (U reference) ∧
      Inverse.factor (U reference)<10660829/12500000 := by
  have hu := reference_radical
  have hq := reference_q
  have hp : 0<U reference*Inverse.q (U reference) :=
    mul_pos (by linarith [hu.1]) (by linarith [hq.1])
  have hl := mul_le_mul hu.1.le hq.1.le (by norm_num)
    (by linarith [hu.1] : 0≤U reference)
  have hh := mul_le_mul hu.2.le hq.2.le
    (by linarith [hq.1] : 0≤Inverse.q (U reference)) (by norm_num)
  change (8528663/10000000:ℝ)<(Q0-U reference)/(U reference*Inverse.q (U reference)) ∧
    (Q0-U reference)/(U reference*Inverse.q (U reference))<10660829/12500000
  constructor
  · apply (lt_div_iff₀ hp).2
    norm_num [Q0]
    linarith
  · apply (div_lt_iff₀ hp).2
    norm_num [Q0]
    linarith

lemma reference_correction :
    (700867/4000000:ℝ)<ratio reference/
      (2*Inverse.q (U reference)*speed (-(1/2)) reference) ∧
    ratio reference/(2*Inverse.q (U reference)*speed (-(1/2)) reference)<8760839/50000000 := by
  have hq := reference_q
  have hv := reference_speed
  have hr := reference_ratio
  have hp : 0<2*Inverse.q (U reference)*speed (-(1/2)) reference :=
    mul_pos (by linarith [hq.1]) (by linarith [hv.1])
  have hl := mul_le_mul hq.1.le hv.1.le (by norm_num)
    (by linarith [hq.1] : 0≤Inverse.q (U reference))
  have hh := mul_le_mul hq.2.le hv.2.le
    (by linarith [hv.1] : 0 ≤ speed (-(1/2)) reference) (by norm_num)
  constructor
  · apply (lt_div_iff₀ hp).2
    linarith
  · apply (div_lt_iff₀ hp).2
    linarith

lemma reference_label_first :
    (67764657/100000000:ℝ)<VLabel.d1 reference ∧
      VLabel.d1 reference<67764659/100000000 := by
  have hu := reference_radical
  have hr := reference_ratio
  have he : VLabel.d1 reference=16031/100000+(63457/100000)*(U reference-1/2)-
      (-(41/4000)+(63457/100000)*reference)*ratio reference := by
    simp only [RoleLabel.d1,VLabel,U]
    ring
  have hc : (-(41/4000)+(63457/100000)*reference:ℝ)=
      698023611/2000000000 := by
    norm_num [reference]
  rw [he,hc]
  constructor <;> linarith

lemma reference_first : |first reference|<1/100000 := by
  rw [first_formula,abs_lt]
  have hf := reference_factor
  have hc := reference_correction
  have hv := reference_label_first
  constructor <;> linarith

lemma reference_trig :
    (7480360507/50000000000:ℝ)<Real.sin referenceAngle ∧
      Real.cos referenceAngle<24718637739/25000000000 := by
  have hs := sin_lower_seven (show 0≤referenceAngle by norm_num [referenceAngle])
  have hc := cos_le_cos8 (show 0≤referenceAngle by norm_num [referenceAngle])
  unfold referenceAngle at hs hc ⊢
  norm_num [cos8] at hs hc
  exact ⟨by linarith,by linarith⟩

lemma reference_contact_positive :
    0<NegativeTwo.TargetContact.B reference referenceAngle := by
  have hu := reference_radical
  have ht := reference_trig
  have hp := positive_trig (show referenceAngle∈Icc 0 (7/10) by norm_num [referenceAngle])
  have hprod := mul_le_mul
    (show U reference-1≤(833763189/1250000000:ℝ) by linarith [hu.2])
    ht.2.le (by linarith [hp.1] : 0≤Real.cos referenceAngle)
    (by norm_num : (0:ℝ)≤833763189/1250000000)
  have hsin := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤reference+1/2 by norm_num [reference])
  have he : NegativeTwo.TargetContact.B reference referenceAngle=
      1/2-(U reference-1)*Real.cos referenceAngle+
        (reference+1/2)*Real.sin referenceAngle := by
    simp only [NegativeTwo.TargetContact.B,U]
    ring
  have hr : reference+1/2=(21323/20000:ℝ) := by norm_num [reference]
  rw [he,hr]
  rw [hr] at hsin
  linarith

lemma reference_angle_upper : angle reference≤referenceAngle := by
  have hzero : NegativeTwo.TargetContact.B reference 0<0 := by
    rw [NegativeTwo.TargetContact.B_zero]
    have hh := reference_radical.1
    dsimp [U] at hh
    linarith
  have hc : Continuous (NegativeTwo.TargetContact.B reference) :=
    continuous_iff_continuousAt.2 fun x =>
      (NegativeTwo.TargetContact.B_angle_hasDerivAt reference x).continuousAt
  obtain ⟨x,hx,hcontact⟩ := intermediate_value_Icc
    (show (0:ℝ)≤referenceAngle by norm_num [referenceAngle]) hc.continuousOn
      (show (0:ℝ)∈Icc (NegativeTwo.TargetContact.B reference 0)
        (NegativeTwo.TargetContact.B reference referenceAngle) from
        ⟨hzero.le,reference_contact_positive.le⟩)
  have hD : NegativeTwo.TargetContact.Domain reference x :=
    ⟨reference_mem,⟨hx.1,by linarith [hx.2,show referenceAngle≤(7/10:ℝ) by norm_num [referenceAngle]]⟩,
      by rw [hcontact]; exact outer_zero_mem⟩
  have he := NegativeTwo.ContactInverse.original_angle hD
  rw [hcontact,show (0:ℝ)-1/2=-(1/2) by norm_num] at he
  exact he.trans_le hx.2

lemma reference_label_value : V reference<24903/50000 := by
  have hu := reference_radical.2
  have he : V reference=-(41/4000)*(U reference-1/2)+(16031/100000)*(11323/20000)+
      (63457/100000)*(U reference-1/2)*(11323/20000) := by
    simp only [V,RoleLabel.outer,RoleLabel.eval,VLabel,U,reference]
    ring
  rw [he]
  linarith

lemma reference_value : (112223/125000:ℝ)<value reference := by
  have hpi : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  have ha := reference_angle_upper
  have hv := reference_label_value
  norm_num [referenceAngle,value,P,RoleLabel.outer,RoleLabel.eval,PLabel] at *
  linarith

lemma late_value {b : ℝ} (hb : b∈Icc (1/5) outerDiagonal) :
    (44889/50000:ℝ)<value b := by
  have ht := curvature_tangent (f := value) (d := first) (dd := second) (κ := (11/100:ℝ))
    hb reference_late
    (fun y hy => value_hasDerivAt ⟨by linarith [hy.1],hy.2⟩)
    (fun y hy => first_hasDerivAt ⟨by linarith [hy.1],hy.2⟩)
    (fun y hy => (second_late_lower hy).le)
  have hsmall := abs_lt.mp reference_first
  have hsquare : (first reference)^2<(1/100000:ℝ)^2 := by nlinarith
  have hcomplete := sq_nonneg ((11/100)*(b-reference)+first reference)
  nlinarith [reference_value]

theorem value_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (44889/50000:ℝ)<value b := by
  by_cases hlate : (1/5:ℝ)≤b
  · exact late_value ⟨hlate,hb.2⟩
  · have hm : value (1/5)≤value b := early_antitone ⟨hb.1,by linarith⟩
      (show (1/5:ℝ)∈Icc 0 (1/5) by norm_num) (by linarith)
    exact (late_value ⟨le_rfl,NegativeTwo.TargetContact.Cap.two_mem.2⟩).trans_le hm

/-- Every original zero contact uses the same exact inverse angle. -/
theorem original {a b x : ℝ} (hs : OuterState a b) (hx : x∈Icc 0 (7/10))
    (hcontact : lowerCut a b x=0) :
    (44889/50000:ℝ)<Real.pi/2-x-P 0-V b := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2⟩
  have hz : NegativeTwo.TargetContact.B b x=0 := by
    dsimp [NegativeTwo.TargetContact.B,lowerCut] at *
    rw [(ShortOuterOne.SameContact.actual_arc hs).1]
    linarith
  have hd : NegativeTwo.TargetContact.Domain b x :=
    ⟨hb,hx,by rw [hz]; exact outer_zero_mem⟩
  have he := NegativeTwo.ContactInverse.original_angle hd
  rw [hz,show (0:ℝ)-1/2=-(1/2) by norm_num] at he
  have ha : angle b=x := he
  have hv := value_lower hb
  dsimp only [value] at hv
  rw [ha] at hv
  exact hv

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.Axial
