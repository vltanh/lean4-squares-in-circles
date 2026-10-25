module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.ReferenceTrig

/-!
# Eight squares: the complete lower target-secondary owner for positive edge three

One concave derivative bound moves the original source to the axial
end of the circle.  The resulting angle function has curvature greater
than `.44`; its single reference at `1.04` gives a strict global reserve.
No angle or coordinate subdivision is used.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def projectedSlope (b : ℝ) : ℝ :=
  VLabel.d1 b+(147/125)*(19121/25000)*ratio b-(147/125)*(16106/25000)
def projectedSlopeFirst (b : ℝ) : ℝ :=
  VLabel.d2 b+(147/125)*(19121/25000)*ratioD b
def projectedSlopeSecond (b : ℝ) : ℝ :=
  VLabel.d3 b+(147/125)*(19121/25000)*ratioDD b

lemma projectedSlope_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt projectedSlope (projectedSlopeFirst b) b := by
  convert ((VLabel.d1_hasDerivAt (outer_domain hb)).add
    ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul
      ((147/125)*(19121/25000)))).sub_const ((147/125)*(16106/25000)) using 1
  · funext t
    simp only [projectedSlope,Pi.add_apply]
  · rfl

lemma projectedSlopeFirst_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt projectedSlopeFirst (projectedSlopeSecond b) b := by
  convert (VLabel.d2_hasDerivAt (outer_domain hb)).add
    ((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hb)).const_mul
      ((147/125)*(19121/25000))) using 1
  · funext t
    simp only [projectedSlopeFirst,Pi.add_apply]
  · rfl

lemma projectedSlopeSecond_negative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    projectedSlopeSecond b<0 := by
  have he := VLabel.third_numerator (outer_domain hb)
  have hp := pow_pos (U_positive (outer_domain hb)) 5
  have hDD : ratioDD b*(U b)^5=3*Q0*W b := by
    show 3*Q0*W b/(U b)^5*(U b)^5=3*Q0*W b
    exact div_mul_cancel₀ _ hp.ne'
  have hh := (UW_bounds hb).2.2
  have hnum : projectedSlopeSecond b*(U b)^5=
      3*Q0*(-(63457/100000)*Q0+
        ((65507/200000)+(147/125)*(19121/25000))*W b) := by
    dsimp only [projectedSlopeSecond]
    rw [show VLabel.s=63457/100000 from rfl,show VLabel.p=-1025/100000 from rfl] at he
    linear_combination he+((147/125)*(19121/25000))*hDD
  have hneg : 3*Q0*(-(63457/100000)*Q0+
      ((65507/200000)+(147/125)*(19121/25000))*W b)<0 := by
    norm_num [Q0]
    linarith [hh.2]
  by_contra hc
  have hm := mul_nonneg (le_of_not_gt hc) hp.le
  linarith

lemma projectedSlope_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (31/100:ℝ)<projectedSlope b := by
  have hc : ConcaveOn ℝ (Icc 0 outerDiagonal) projectedSlope :=
    concave_of_deriv2
      (fun t ht => projectedSlope_hasDerivAt ht)
      (fun t ht => projectedSlopeFirst_hasDerivAt ht)
      (fun t ht => (projectedSlopeSecond_negative ht).le)
  have hz : (31/100:ℝ)<projectedSlope 0 := by
    dsimp [projectedSlope]
    linarith [V_zero_first_lower,(outer_ratio_bounds outer_zero_mem).1]
  have hd : (31/100:ℝ)<projectedSlope outerDiagonal := by
    rw [projectedSlope,V_first_diagonal,ratio_diagonal]
    norm_num
  have hh := hc.min_le_of_mem_Icc outer_zero_mem
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩) hb
  exact (lt_min hz hd).trans_le hh

lemma actual_projectedSlope {b φ : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hφ : Lower φ) :
    0<VLabel.d1 b+(147/125)*ratio b*Real.sin φ-(147/125)*Real.cos φ := by
  have ht := lower_trig hφ
  have hr := (ShortOuterOne.SameContact.ratio_pos (outer_domain hb)).le
  have hh := mul_nonneg hr (sub_nonneg.mpr ht.1.le)
  have he := projectedSlope_lower hb
  dsimp [projectedSlope] at he
  nlinarith

lemma source_projection_minimum {b φ : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hφ : Lower φ) :
    V 0-(147/125)*outerAxial*Real.sin φ≤
      V b-(147/125)*arc b*Real.sin φ-(147/125)*b*Real.cos φ := by
  have hd {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
      HasDerivAt (fun y => V y-(147/125)*arc y*Real.sin φ-(147/125)*y*Real.cos φ)
        (VLabel.d1 t+(147/125)*ratio t*Real.sin φ-(147/125)*Real.cos φ) t := by
    convert ((VLabel.outer_hasDerivAt (outer_domain ht)).sub
      (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain ht)).const_mul
        (147/125)).mul_const (Real.sin φ))).sub
      (((hasDerivAt_id' t).const_mul (147/125)).mul_const (Real.cos φ)) using 1
    · funext y
      simp only [V,Pi.sub_apply]
    · ring
  have hm : MonotoneOn
      (fun y => V y-(147/125)*arc y*Real.sin φ-(147/125)*y*Real.cos φ)
      (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun _ ht => (hd ht).continuousAt.continuousWithinAt)
      (fun _ ht => hd (Ioo_subset_Icc_self ht))
      (fun _ ht => (actual_projectedSlope (Ioo_subset_Icc_self ht) hφ).le)
  have hh := hm outer_zero_mem hb hb.1
  simpa only [ShortOuterOne.SameContact.arc_zero,mul_zero,zero_mul,sub_zero] using hh

def projectionScalar (φ : ℝ) : ℝ :=
  φ+V 0-793/20000+147/250+(147/250)*Real.cos φ-
    (147/125)*(outerAxial-1/2)*Real.sin φ
def projectionFirst (φ : ℝ) : ℝ :=
  1-(147/250)*Real.sin φ-(147/125)*(outerAxial-1/2)*Real.cos φ
def projectionSecond (φ : ℝ) : ℝ :=
  -(147/250)*Real.cos φ+(147/125)*(outerAxial-1/2)*Real.sin φ

lemma projectionScalar_hasDerivAt (φ : ℝ) :
    HasDerivAt projectionScalar (projectionFirst φ) φ := by
  convert (((((hasDerivAt_id' φ).add_const (V 0)).sub_const (793/20000)).add_const
    (147/250)).add ((Real.hasDerivAt_cos φ).const_mul (147/250))).sub
    ((Real.hasDerivAt_sin φ).const_mul ((147/125)*(outerAxial-1/2))) using 1
  · funext t
    simp only [projectionScalar,Pi.add_apply,Pi.sub_apply]
  · dsimp only [projectionFirst]
    ring

lemma projectionFirst_hasDerivAt (φ : ℝ) :
    HasDerivAt projectionFirst (projectionSecond φ) φ := by
  convert (((Real.hasDerivAt_sin φ).const_mul (147/250)).const_sub 1).sub
    ((Real.hasDerivAt_cos φ).const_mul ((147/125)*(outerAxial-1/2))) using 1
  · funext t
    simp only [projectionFirst,Pi.sub_apply]
  · dsimp only [projectionSecond]
    ring

lemma projectionSecond_lower {φ : ℝ} (hφ : Lower φ) :
    (11/25:ℝ)<projectionSecond φ := by
  have ht := lower_trig hφ
  have hp := mul_le_mul
    (show (1829/2000:ℝ)≤outerAxial-1/2 by linarith [fine_outer_endpoint_bounds.1])
    ht.1.le (by norm_num : (0:ℝ)≤19121/25000)
    (by linarith [fine_outer_endpoint_bounds.1] : 0≤outerAxial-1/2)
  dsimp [projectionSecond]
  norm_num at hp
  linarith [ht.2.2.2.1]

lemma projection_reference_angle : Lower (26/25) := by
  refine ⟨?_,?_⟩
  · dsimp [lowerAngle]
    linarith [pi_hand_enclosure.2]
  · linarith [pi_hand_enclosure.1]

lemma projection_reference_trig :
    (215601/250000:ℝ)<Real.sin (26/25) ∧ Real.sin (26/25)<172481/200000 ∧
    (25311/50000:ℝ)<Real.cos (26/25) ∧ Real.cos (26/25)<506221/1000000 := by
  have hs := sin11_le_sin (show (0:ℝ)≤26/25 by norm_num)
  have hsu := sin_le_sin9 (show (0:ℝ)≤26/25 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤26/25 by norm_num)
  have hcu := cos_le_cos12 (show (0:ℝ)≤26/25 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hsu hc hcu
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma projection_references :
    (9439/10000:ℝ)<projectionScalar (26/25) ∧
      |projectionFirst (26/25)|<13/250 := by
  have ht := projection_reference_trig
  have ha : (36583/40000:ℝ)<outerAxial-1/2 ∧ outerAxial-1/2<57161/62500 := by
    constructor <;> linarith [ShortOuterZero.fine_axial_bounds.1,
      ShortOuterZero.fine_axial_bounds.2]
  have hsu := mul_le_mul ha.2.le ht.2.1.le
    (by linarith [ht.1] : 0≤Real.sin (26/25)) (by norm_num : (0:ℝ)≤57161/62500)
  have hcl := mul_le_mul ha.1.le ht.2.2.1.le
    (by norm_num : (0:ℝ)≤25311/50000) (by linarith [ha.1] : 0≤outerAxial-1/2)
  have hcu := mul_le_mul ha.2.le ht.2.2.2.le
    (by linarith [ht.2.2.1] : 0≤Real.cos (26/25))
    (by norm_num : (0:ℝ)≤57161/62500)
  dsimp [projectionScalar,projectionFirst]
  constructor
  · nlinarith [V_zero_bounds.1,ht.2.2.1]
  · rw [abs_lt]
    constructor <;> nlinarith [ht.1,ht.2.1]

theorem projectionScalar_lower {φ : ℝ} (hφ : Lower φ) :
    (588/625:ℝ)<projectionScalar φ := by
  have ht := curvature_tangent (κ := (11/25:ℝ)) hφ projection_reference_angle
    (fun t _ => projectionScalar_hasDerivAt t)
    (fun t _ => projectionFirst_hasDerivAt t)
    (fun t ht => (projectionSecond_lower ht).le)
  have hd := abs_lt.mp projection_references.2
  have hdsq : (projectionFirst (26/25))^2<(13/250:ℝ)^2 := by nlinarith
  nlinarith [projection_references.1,
    sq_nonneg ((11/25)*(φ-26/25)+projectionFirst (26/25))]

theorem original_lower_target_secondary {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 1 φ) :
    (588/625:ℝ)<value b B φ := by
  have hcut := lower_target_secondary_cut hφ hm
  have hL := L_axial_line (NegativeTwo.source_mem ht)
  have hsource := source_projection_minimum (NegativeTwo.source_mem hs) hφ
  rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hsource
  have hbase := projectionScalar_lower hφ
  dsimp [projectionScalar,value] at *
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree
