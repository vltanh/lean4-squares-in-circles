module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoData
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoLabels
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoPrimaryLabels

/-!
# Eight squares: both actual aligned opposite-quarter contacts

One aligned cost increases from its axial circle point.  The other has
uniform curvature greater than one half; a single rational coordinate
and a tangent parabola give its strict bound on the whole contact arc.
The final theorems consume the original weak aligned inequalities.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def alignedLeftCut (B : ℝ) : ℝ := arc B-1
def alignedLeft (B : ℝ) : ℝ := Real.pi/2-P (alignedLeftCut B)-V B
def alignedLeftD (B : ℝ) : ℝ :=
  PLabel.d1 (alignedLeftCut B)*ratio B-VLabel.d1 B
def alignedLeftDD (B : ℝ) : ℝ :=
  -PLabel.d2 (alignedLeftCut B)*(ratio B)^2+
    PLabel.d1 (alignedLeftCut B)*ratioD B-VLabel.d2 B

lemma aligned_left_domain {B : ℝ} (hB : B∈Icc 0 bOne) :
    B∈Icc 0 outerDiagonal ∧ alignedLeftCut B∈Icc 0 (83/200) := by
  have hb : B∈Icc 0 outerDiagonal := ⟨hB.1,hB.2.trans bOne_mem.2⟩
  have hm := ShortOuterOne.SameContact.arc_antitone (outer_domain hb)
    (outer_domain bOne_mem) hB.2
  rw [bOne_arc] at hm
  have ha := (outer_bounds (ShortOuterOne.SameContact.arc_state hb)).2.1
  refine ⟨hb,?_⟩
  dsimp [alignedLeftCut]
  constructor <;> linarith [outer_endpoint_bounds.2.1]

lemma aligned_left_source_mem {B : ℝ} (hB : B∈Icc 0 bOne) :
    alignedLeftCut B∈Icc 0 outerDiagonal := by
  have hs := (aligned_left_domain hB).2
  exact Asymmetric.rational_outer_mem ⟨hs.1,by linarith [hs.2]⟩

lemma alignedLeft_hasDerivAt {B : ℝ} (hB : B∈Icc 0 bOne) :
    HasDerivAt alignedLeft (alignedLeftD B) B := by
  have hd := (ShortOuterOne.SameContact.arc_hasDerivAt
    (outer_domain (aligned_left_domain hB).1)).sub_const 1
  have hs := (PLabel.outer_hasDerivAt
    (outer_domain (aligned_left_source_mem hB))).comp B hd
  exact ((hs.const_sub (Real.pi/2)).fun_sub
    (VLabel.outer_hasDerivAt (outer_domain (aligned_left_domain hB).1))).congr_deriv
      (by dsimp [alignedLeftD,alignedLeftCut]; ring)

lemma alignedLeftD_hasDerivAt {B : ℝ} (hB : B∈Icc 0 bOne) :
    HasDerivAt alignedLeftD (alignedLeftDD B) B := by
  have hb := (aligned_left_domain hB).1
  have hd := (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).sub_const 1
  have hs := (PLabel.d1_hasDerivAt (outer_domain (aligned_left_source_mem hB))).comp B hd
  exact ((hs.fun_mul (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb))).fun_sub
    (VLabel.d1_hasDerivAt (outer_domain hb))).congr_deriv
      (by simp only [Function.comp_apply,alignedLeftDD,alignedLeftCut]; ring)

lemma outer_ratioD_lower {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (557/1000:ℝ)<ratioD B := by
  have hu := U_positive (outer_domain hB)
  have hc := pow_le_pow_left₀ hu.le (UW_bounds hB).2.1.le 3
  change (557/1000:ℝ)<Q0/(U B)^3
  apply (lt_div_iff₀ (pow_pos hu 3)).2
  norm_num [Q0]
  nlinarith

lemma alignedLeft_curvature {B : ℝ} (hB : B∈Icc 0 bOne) :
    (1/2:ℝ)<alignedLeftDD B := by
  have hb := (aligned_left_domain hB).1
  have hs := aligned_left_source_mem hB
  have hP := P_second_small (aligned_left_domain hB).2
  have hP0 := P_second_positive hs
  have hr := outer_ratio_bounds hb
  have hr2 : (ratio B)^2≤1 := by nlinarith [hr.1,hr.2.1]
  have hnegative := mul_le_mul_of_nonneg_left hr2 hP0.le
  have hpositive := mul_lt_mul (P_first_bounds hs).1 (outer_ratioD_lower hb).le
    (by norm_num : (0:ℝ)<557/1000) (by linarith [(P_first_bounds hs).1])
  dsimp [alignedLeftDD]
  linarith [V_second_upper hb]

lemma aligned_reference_mem : (2/3:ℝ)∈Icc 0 bOne :=
  ⟨by norm_num,by linarith [bOne_bounds.1]⟩

lemma aligned_reference_target :
    (39956921/25000000:ℝ)<U (2/3) ∧ U (2/3)<31965537/20000000 :=
  Asymmetric.shifted_reference (aligned_left_domain aligned_reference_mem).1
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])

lemma aligned_reference_source :
    (18861773/10000000:ℝ)<U (alignedLeftCut (2/3)) ∧
      U (alignedLeftCut (2/3))<188617731/100000000 := by
  have ht := aligned_reference_target
  have hs := aligned_left_source_mem aligned_reference_mem
  have hc := UW_circle (outer_domain hs)
  have hp := U_positive (outer_domain hs)
  have hw : W (alignedLeftCut (2/3))=U (2/3)-1 := by
    dsimp [W,alignedLeftCut,U]
    ring
  rw [hw] at hc
  norm_num [Q0] at hc
  constructor <;> nlinarith

lemma aligned_reference_value : (9091/10000:ℝ)<alignedLeft (2/3) := by
  have ht := aligned_reference_target
  have hs := aligned_reference_source
  have hb : (9827684/100000000:ℝ)<alignedLeftCut (2/3) ∧
      alignedLeftCut (2/3)<1965537/20000000 := by
    dsimp [alignedLeftCut,U] at *
    constructor <;> linarith
  have hp := mul_le_mul
    (show 13861773/10000000≤arc (alignedLeftCut (2/3)) by dsimp [U] at hs; linarith [hs.1])
    hb.1.le (by norm_num)
    (by dsimp [U] at hs; linarith [hs.1] : 0≤arc (alignedLeftCut (2/3)))
  have hb2 := pow_le_pow_left₀ (aligned_left_source_mem aligned_reference_mem).1 hb.2.le 2
  have hpi := pi_hand_enclosure.1
  dsimp [alignedLeft,P,V,RoleLabel.outer,RoleLabel.eval,PLabel,VLabel]
  dsimp [U] at ht hs
  nlinarith

lemma aligned_reference_first : |alignedLeftD (2/3)|<1/50 := by
  have ht := aligned_reference_target
  have hs := aligned_reference_source
  have hb := aligned_left_source_mem aligned_reference_mem
  have hB := (aligned_left_domain aligned_reference_mem).1
  have hpos := U_positive (outer_domain hb)
  have hposB := U_positive (outer_domain hB)
  have hw : W (alignedLeftCut (2/3))=U (2/3)-1 := by
    dsimp [W,alignedLeftCut,U]
    ring
  have hr : (317/1000:ℝ)<ratio (alignedLeftCut (2/3)) ∧
      ratio (alignedLeftCut (2/3))<159/500 := by
    change (317/1000:ℝ)<W (alignedLeftCut (2/3))/U (alignedLeftCut (2/3)) ∧
      W (alignedLeftCut (2/3))/U (alignedLeftCut (2/3))<159/500
    rw [hw]
    constructor
    · apply (lt_div_iff₀ hpos).2
      linarith
    · apply (div_lt_iff₀ hpos).2
      linarith
  have hR : (729/1000:ℝ)<ratio (2/3) ∧ ratio (2/3)<731/1000 := by
    change (729/1000:ℝ)<W (2/3)/U (2/3) ∧ W (2/3)/U (2/3)<731/1000
    constructor
    · apply (lt_div_iff₀ hposB).2
      norm_num [W]
      linarith
    · apply (div_lt_iff₀ hposB).2
      norm_num [W]
      linarith
  have hb' : (98/1000:ℝ)<alignedLeftCut (2/3) ∧ alignedLeftCut (2/3)<99/1000 := by
    dsimp [alignedLeftCut,U] at *
    constructor <;> linarith
  have hprodlo := mul_le_mul hb'.1.le hr.1.le (by norm_num)
    (by linarith [hb'.1] : 0≤alignedLeftCut (2/3))
  have hprodhi := mul_le_mul hb'.2.le hr.2.le
    (by linarith [hr.1] : 0≤ratio (alignedLeftCut (2/3))) (by norm_num)
  have hP : (98/125:ℝ)<PLabel.d1 (alignedLeftCut (2/3)) ∧
      PLabel.d1 (alignedLeftCut (2/3))<393/500 := by
    dsimp [RoleLabel.d1,PLabel]
    dsimp [U] at hs
    constructor <;> nlinarith
  have hV : (111/200:ℝ)<VLabel.d1 (2/3) ∧ VLabel.d1 (2/3)<557/1000 := by
    dsimp [RoleLabel.d1,VLabel]
    dsimp [U] at ht
    constructor <;> nlinarith
  have hlo := mul_le_mul hP.1.le hR.1.le (by norm_num)
    (by linarith [hP.1] : 0≤PLabel.d1 (alignedLeftCut (2/3)))
  have hhi := mul_le_mul hP.2.le hR.2.le
    (by linarith [hR.1] : 0≤ratio (2/3)) (by norm_num)
  rw [abs_lt]
  dsimp [alignedLeftD]
  constructor <;> nlinarith

lemma aligned_left {B : ℝ} (hB : B∈Icc 0 bOne) :
    (227/250:ℝ)<alignedLeft B := by
  have ht := curvature_tangent (κ := (1/2:ℝ)) hB aligned_reference_mem
    (fun t ht => alignedLeft_hasDerivAt ht)
    (fun t ht => alignedLeftD_hasDerivAt ht)
    (fun t ht => (alignedLeft_curvature ht).le)
  have hf := abs_lt.mp aligned_reference_first
  have hfsq : (alignedLeftD (2/3))^2<(1/50:ℝ)^2 := by nlinarith
  have hs := sq_nonneg ((B-2/3)/2+alignedLeftD (2/3))
  nlinarith [aligned_reference_value]

lemma aligned_left_original {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (halign : 1+b≤A) : (227/250:ℝ)<value b B (Real.pi/2) := by
  have hA : 1≤A := by linarith [hs.1]
  have hmono := ShortOuterOne.SameContact.arc_antitone
    (primary_domain primary_one_mem) (primary_domain (primary_mem ht)) hA
  rw [(ShortOuterOne.SameContact.actual_arc ht).2] at hmono
  have hB : B∈Icc 0 bOne := ⟨ht.1,hmono⟩
  have hcut : b≤alignedLeftCut B := by
    dsimp [alignedLeftCut]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have hP := P_monotone (source_mem hs) (aligned_left_source_mem hB) hcut
  have hh := aligned_left hB
  dsimp [value,alignedLeft] at *
  linarith

lemma aligned_right {B : ℝ} (hB : B∈Icc 0 (outerAxial-1)) :
    (44889/50000:ℝ)<Real.pi/2+PPrimaryLabel.outer (1+B)-V B := by
  have hdom {t : ℝ} (ht : t∈Icc 0 (outerAxial-1)) :
      t∈Icc 0 outerDiagonal ∧ 1+t∈Icc 1 outerAxial := by
    refine ⟨⟨ht.1,?_⟩,⟨by linarith [ht.1],by linarith [ht.2]⟩⟩
    linarith [ht.2,outer_endpoint_bounds.2.1,fine_outer_endpoint_bounds.2]
  have hd {t : ℝ} (ht : t∈Icc 0 (outerAxial-1)) :
      HasDerivAt (fun y => Real.pi/2+PPrimaryLabel.outer (1+y)-V y)
        (PPrimaryLabel.d1 (1+t)-VLabel.d1 t) t := by
    have hs := (PPrimaryLabel.outer_hasDerivAt (primary_domain
      ⟨primary_one_mem.1.trans (hdom ht).2.1,(hdom ht).2.2⟩)).comp t
        ((hasDerivAt_id' t).const_add 1)
    exact ((hs.const_add (Real.pi/2)).fun_sub
      (VLabel.outer_hasDerivAt (outer_domain (hdom ht).1))).congr_deriv (by ring)
  have hm : MonotoneOn (fun y => Real.pi/2+PPrimaryLabel.outer (1+y)-V y)
      (Icc 0 (outerAxial-1)) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd ht).continuousAt.continuousWithinAt)
      (fun t ht => hd (Ioo_subset_Icc_self ht))
      (fun t ht => by
        have hh := hdom (Ioo_subset_Icc_self ht)
        linarith [M_first_above_one hh.2,V_first_upper hh.1])
  have hz : (0:ℝ)∈Icc 0 (outerAxial-1) :=
    ⟨le_rfl,by linarith [outer_endpoint_bounds.1]⟩
  have he : PPrimaryLabel.outer 1= -P bOne :=
    PLabel.primary_actual (primary_state primary_one_mem)
  have hh := hm hz hB hB.1
  norm_num only [add_zero,he] at hh
  linarith [aligned_axial_value]

lemma aligned_right_original {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (halign : 1+B≤a) : (44889/50000:ℝ)<value b B (Real.pi/2) := by
  have hB : B∈Icc 0 (outerAxial-1) :=
    ⟨ht.1,by linarith [(outer_bounds hs).2.1]⟩
  have hp : 1+B∈Icc outerDiagonal outerAxial :=
    ⟨by linarith [ht.1,primary_one_mem.1],halign.trans (outer_bounds hs).2.1⟩
  have hm := M_monotone hp (primary_mem hs) halign
  have he : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
  rw [he] at hm
  have hh := aligned_right hB
  dsimp [value]
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo
