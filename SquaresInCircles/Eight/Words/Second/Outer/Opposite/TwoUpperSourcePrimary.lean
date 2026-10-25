module

public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoAxialCalculus
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoTargetPrimaryLabel
public import SquaresInCircles.Eight.Words.Second.WordData

/-!
# Eight squares: the original upper source-primary owner of opposite outer edge two

The weak separator is compared with its exact inverse angle at the original source primary
height. The target ratio makes its contact cost monotone along the whole target circle. The two
possible initial points are the aligned contact and the zero-target boundary
(`original_upper_source_primary`). All original states and weak ties are kept.
-/

section
/-!
## Original-coordinate data for opposite outer edge two

The four cuts below are rearrangements of the original weak axes.  The
source and target keep their literal edge-two labels and their common
circle.  The shortened bounds lemma is local to this contact family.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma outer_bounds {a b : ℝ} (hs : OuterState a b) :
    outerDiagonal≤a ∧ a≤outerAxial ∧ b≤outerDiagonal :=
  ⟨(CommonQuarter.outer_bounds hs).1,(CommonQuarter.outer_bounds hs).2.1,
    (CommonQuarter.outer_bounds hs).2.2.2.1⟩

def value (b B φ : ℝ) : ℝ := φ-P b-V B
def lowerCut (a b x : ℝ) : ℝ :=
  (a-1/2)*Real.cos x-(b+1/2)*Real.sin x-1/2
def upperCut (a b x : ℝ) : ℝ :=
  (a-1/2)*Real.cos x+(b-1/2)*Real.sin x-1/2
def lowerPrimary (a b x : ℝ) : ℝ :=
  1/2+(a+1/2)*Real.sin x+(b+1/2)*Real.cos x
def upperPrimary (a b x : ℝ) : ℝ :=
  1/2+(b+1/2)*Real.cos x-(a-1/2)*Real.sin x
def k (b x : ℝ) : ℝ := Real.cos x+ratio b*Real.sin x
def v (b x : ℝ) : ℝ := W b*Real.sin x+(U b-1)*Real.cos x

lemma cost_identity {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    SecondWord.cost 2 .outer .outer false true a b A B φ=value b B φ := by
  unfold value
  rw [show P b=PLabel.eval a b from PLabel.outer_actual hs,
    show V B=VLabel.eval A B from VLabel.outer_actual ht]
  norm_num [SecondWord.cost,label,QuarterWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,PLabel,VLabel,RoleLabel.eval]
  ring

lemma upper_width {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    pairWidth (Real.pi/2+x)=(1+Real.cos x+Real.sin x)/2 := by
  rw [quarter_width (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩),
    abs_of_nonneg (positive_trig hx).2.2.1]

lemma lower_width {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    pairWidth (Real.pi/2-x)=(1+Real.cos x+Real.sin x)/2 := by
  have hh := quarter_width (x := -x)
    (abs_le.mpr ⟨by linarith [hx.2],by linarith [hx.1]⟩)
  simpa only [sub_eq_add_neg,Real.cos_neg,Real.sin_neg,abs_neg,
    abs_of_nonneg (positive_trig hx).2.2.1] using hh

lemma source_mem {a b : ℝ} (hs : OuterState a b) : b∈Icc 0 outerDiagonal :=
  ⟨hs.1,(outer_bounds hs).2.2⟩

lemma primary_mem {a b : ℝ} (hs : OuterState a b) : a∈Icc outerDiagonal outerAxial :=
  ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end

section
/-!
## Both actual aligned opposite-quarter contacts

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
end
end
end

section
/-!
## The strict target ratio on the complete actual outer circle

The diagonal-contact inverse speed exceeds the target label derivative
at zero, and their difference has derivative greater than .012 on the
whole circle.  The inverse-polynomial bounds retain the exact circle
and every boundary point.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.TargetRatio

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)

def z : ℝ := outerDiagonal-1/2
def speed (b : ℝ) : ℝ := NegativeTwo.ContactInverse.speed z b
def F (b : ℝ) : ℝ := -NegativeTwo.ContactInverse.first z b
def first (b : ℝ) : ℝ := PJCritical.inverseTarget (U b) (ratio b) z (speed b)
def difference (b : ℝ) : ℝ := F b-VLabel.d1 b
def differenceD (b : ℝ) : ℝ := first b-VLabel.d2 b

lemma z_bounds : (399/1000:ℝ)<z ∧ z<2/5 := by
  dsimp [z]
  constructor <;> linarith [fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]

lemma z_mem : z∈Icc (-(1/2:ℝ)) (2/5) :=
  ⟨by linarith [z_bounds.1],z_bounds.2.le⟩

lemma F_formula (b : ℝ) :
    F b=Inverse.factor (U b)+z*ratio b/(Inverse.q (U b)*speed b) := by
  dsimp [F,NegativeTwo.ContactInverse.first,speed]
  ring

lemma F_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt F (first b) b := by
  exact (NegativeTwo.ContactInverse.first_hasDerivAt hb z_mem).neg.congr_deriv
    (by dsimp only [first,speed,NegativeTwo.ContactInverse.second]; ring)

lemma difference_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt difference (differenceD b) b := by
  exact (F_hasDerivAt hb).sub (VLabel.d1_hasDerivAt (outer_domain hb))

lemma speed_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : (481/500:ℝ)<speed b := by
  have hd := NegativeTwo.ContactInverse.data hb z_mem
  have hq := Inverse.range_data
    (show U b∈Inverse.interval from ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩)
  have hz2 : z^2<(2/5:ℝ)^2 := by nlinarith [z_bounds.1,z_bounds.2]
  have hv0 : 0<speed b := hd.2.2.2.2.1
  have hn : z^2+(speed b)^2=Inverse.q (U b) := hd.2.2.2.2.2
  nlinarith [hq.2]

lemma weight_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<z/(Inverse.q (U b)*speed b) ∧ z/(Inverse.q (U b)*speed b)<48/125 := by
  have hq := (Inverse.range_data
    (show U b∈Inverse.interval from ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩)).2
  have hv := speed_lower hb
  have hp : 0<Inverse.q (U b)*speed b := by positivity
  refine ⟨div_pos (by linarith [z_bounds.1]) hp,?_⟩
  apply (div_lt_iff₀ hp).2
  have hm := mul_le_mul hq hv.le (by norm_num : (0:ℝ)≤481/500)
    (by linarith : 0≤Inverse.q (U b))
  nlinarith [z_bounds.2]

lemma brace_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    -(81/500:ℝ)<NegativeTwo.Inverse.brace (U b) (ratio b) (speed b) := by
  have hd := NegativeTwo.ContactInverse.data hb z_mem
  have hI : U b∈Inverse.interval := ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩
  have hq := (Inverse.range_data hI).2
  have hq0 : 0<Inverse.q (U b) := by linarith
  have hv : 0<speed b := by linarith [speed_lower hb]
  have hz2 : z^2≤4/25 := by nlinarith [z_bounds.1,z_bounds.2]
  have hr := outer_ratio_bounds hb
  have hr2 : (ratio b)^2≤1 := by nlinarith [hr.1,hr.2.1]
  have hv2 : (1157/1250:ℝ)≤(speed b)^2 := by
    have hn := hd.2.2.2.2.2
    change z^2+(speed b)^2=Inverse.q (U b) at hn
    linarith
  have hden := mul_le_mul hq hv2 (by norm_num : (0:ℝ)≤1157/1250) hq0.le
  have hnum := mul_le_mul hr2 hz2 (sq_nonneg z) (by norm_num : (0:ℝ)≤1)
  have hcor : (ratio b)^2*z^2/(Inverse.q (U b)*(speed b)^2)<4/25 := by
    apply (div_lt_iff₀ (mul_pos hq0 (sq_pos_of_pos hv))).2
    nlinarith
  have he := NegativeTwo.Inverse.brace_identity hd.1.ne' hq0.ne' hv.ne'
    (Axial.circle_ratio hb) hd.2.2.2.2.2
  have hK := (Inverse.K0_bounds hI).1
  dsimp [Inverse.mass] at hK
  linarith

theorem derivative_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (3/250:ℝ)<differenceD b := by
  have hh := Inverse.actual_height_derivative hb
  have hw := weight_bounds hb
  have hk := brace_lower hb
  have hfirst := mul_le_mul_of_nonneg_left hk.le hw.1.le
  have hsecond := mul_lt_mul_of_pos_right hw.2 (by norm_num : (0:ℝ)<81/500)
  have hV := V_second_upper hb
  change (3/250:ℝ)< -ratio b*PJCritical.heightFactorD (U b)+
    z/(Inverse.q (U b)*speed b)*NegativeTwo.Inverse.brace (U b) (ratio b) (speed b)-VLabel.d2 b
  nlinarith

lemma zero_q :
    (67903041/62500000:ℝ)<Inverse.q (U 0) ∧
      Inverse.q (U 0)<543224329/500000000 := by
  have hu := NegativeTwo.TargetContact.Cap.zero_source
  norm_num [Inverse.q,NegativeTwo.Inverse.q,Q0]
  constructor <;> linarith

lemma zero_ratio : (5223/20000:ℝ)<ratio 0 := by
  have hu := NegativeTwo.TargetContact.Cap.zero_source.2
  have hp := U_positive (outer_domain outer_zero_mem)
  rw [show ratio 0=(1/2)/U 0 by simp only [ratio,U,zero_add]]
  apply (lt_div_iff₀ hp).2
  linarith

lemma zero_factor : (48099/50000:ℝ)<Inverse.factor (U 0) := by
  have hu := NegativeTwo.TargetContact.Cap.zero_source
  have hq := zero_q
  have hp : 0<U 0*Inverse.q (U 0) := mul_pos (by linarith [hu.1]) (by linarith [hq.1])
  have hh := mul_le_mul hu.2.le hq.2.le
    (by linarith [hq.1] : 0≤Inverse.q (U 0)) (by norm_num)
  change (48099/50000:ℝ)<(Q0-U 0)/(U 0*Inverse.q (U 0))
  apply (lt_div_iff₀ hp).2
  norm_num [Q0]
  nlinarith

lemma zero_speed : speed 0<(963/1000:ℝ) := by
  have hd := NegativeTwo.ContactInverse.data outer_zero_mem z_mem
  have hq := zero_q.2
  have hz := z_bounds
  have hv0 : 0<speed 0 := hd.2.2.2.2.1
  have hn : z^2+(speed 0)^2=Inverse.q (U 0) := hd.2.2.2.2.2
  have hz2 : (399/1000:ℝ)^2<z^2 := by nlinarith [hz.1]
  nlinarith

lemma zero_correction :
    (9959/100000:ℝ)<z*ratio 0/(Inverse.q (U 0)*speed 0) := by
  have hq := zero_q
  have hv := zero_speed
  have hv0 : 0<speed 0 := by linarith [speed_lower outer_zero_mem]
  have hp : 0<Inverse.q (U 0)*speed 0 := mul_pos (by linarith [hq.1]) hv0
  have hden := mul_le_mul hq.2.le hv.le hv0.le (by norm_num)
  have hnum := mul_le_mul z_bounds.1.le zero_ratio.le (by norm_num)
    (by linarith [z_bounds.1] : 0≤z)
  apply (lt_div_iff₀ hp).2
  nlinarith

lemma zero_positive : (1/2000:ℝ)<difference 0 := by
  have hf := zero_factor
  have hc := zero_correction
  have hV := V_first_upper outer_zero_mem
  dsimp [difference]
  rw [F_formula]
  linarith

lemma difference_monotone : MonotoneOn difference (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hb => (difference_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun _ hb => difference_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun _ hb => by linarith [derivative_positive (Ioo_subset_Icc_self hb)])

theorem paid {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : VLabel.d1 b<F b := by
  have hm := difference_monotone outer_zero_mem hb hb.1
  have h0 := zero_positive
  dsimp [difference] at *
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo.TargetRatio
end
end
end

section
/-!
## The explicit inverse rotation for an arbitrary physical primary height

The fixed-primary shift ranges up to .915.  The actual circle keeps
its radical strictly positive throughout this whole range.  The
source derivative of the inverse angle increases with the primary
shift, so the diagonal ratio already pays every physical primary
contact.  Original weak separators give a finite comparison to this
curve.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.PrimaryInverse

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

abbrev radius := NegativeTwo.ContactInverse.radius
abbrev speed := NegativeTwo.ContactInverse.speed
abbrev baseAngle := NegativeTwo.ContactInverse.baseAngle
abbrev inverseAngle := NegativeTwo.ContactInverse.angle
def shifts : Set ℝ := Icc 0 (183/200)
def X (z b : ℝ) : ℝ := Real.pi/2-inverseAngle z b
def F (z b : ℝ) : ℝ := Inverse.factor (U b)+z*ratio b/(Inverse.q (U b)*speed z b)
def targetCost (z b : ℝ) : ℝ := X z b-V b

lemma data {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    1<radius b ∧ (radius b)^2=Inverse.q (U b) ∧
      0<speed z b ∧ z^2+(speed z b)^2=Inverse.q (U b) := by
  have hzero := NegativeTwo.ContactInverse.data hb
    (show (0:ℝ)∈Icc (-(1/2)) (2/5) by norm_num)
  have hq := (Inverse.range_data
    (show U b∈Inverse.interval from ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩)).2
  have hz2 : z^2≤(183/200:ℝ)^2 := by nlinarith [hz.1,hz.2]
  have hrad : 0<Inverse.q (U b)-z^2 := by linarith
  have hv := Real.sqrt_pos.mpr hrad
  have hv2 := Real.sq_sqrt hrad.le
  refine ⟨hzero.2.2.1,hzero.2.2.2.1,hv,?_⟩
  change z^2+(Real.sqrt (Inverse.q (U b)-z^2))^2=Inverse.q (U b)
  linarith

lemma inverse_root {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    Real.sqrt (1-(z/radius b)^2)=speed z b/radius b := by
  have hd := data hb hz
  have hn : 0<radius b := by linarith [hd.1]
  have he : 1-(z/radius b)^2=(speed z b/radius b)^2 := by
    field_simp [hn.ne']
    nlinarith [hd.2.1,hd.2.2.2]
  rw [he,Real.sqrt_sq (div_nonneg hd.2.2.1.le hn.le)]

lemma argument_bounds {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    -1<z/radius b ∧ z/radius b<1 := by
  have hd := data hb hz
  have hn : 0<radius b := by linarith [hd.1]
  constructor
  · apply (lt_div_iff₀ hn).2
    linarith [hz.1,hd.1]
  · apply (div_lt_iff₀ hn).2
    linarith [hz.2,hd.1]

lemma angle_source_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (inverseAngle z) (-F z b) b := by
  have hd := data hb hz
  have hn : 0<radius b := by linarith [hd.1]
  have hv := hd.2.2.1
  have ha := argument_bounds hb hz
  have hratio : HasDerivAt (fun y => z/radius y) (-z*ratio b/(radius b)^3) b := by
    convert (hasDerivAt_const b z).div
      (NegativeTwo.ContactInverse.radius_hasDerivAt hb) hn.ne' using 1
    field_simp [hn.ne']
    ring
  have hbeta : HasDerivAt (fun y => Real.arcsin (z/radius y))
      (-z*ratio b/(Inverse.q (U b)*speed z b)) b := by
    have hh := (Real.hasDerivAt_arcsin (by linarith : z/radius b≠-1)
      (by linarith : z/radius b≠1)).comp b hratio
    refine hh.congr_deriv ?_
    rw [inverse_root hb hz,←hd.2.1]
    field_simp [hn.ne',hv.ne']
  exact ((NegativeTwo.ContactInverse.base_hasDerivAt hb).add hbeta).congr_deriv
    (by dsimp only [F]; ring)

lemma X_source_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (X z) (F z b) b := by
  exact ((angle_source_hasDerivAt hb hz).const_sub (Real.pi/2)).congr_deriv (by ring)

lemma X_shift_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts) :
    HasDerivAt (fun t => X t b) (-(1/speed z b)) z := by
  have hd := data hb hz
  have hn : 0<radius b := by linarith [hd.1]
  have ha := argument_bounds hb hz
  have hbeta := (Real.hasDerivAt_arcsin (by linarith : z/radius b≠-1)
    (by linarith : z/radius b≠1)).comp z ((hasDerivAt_id z).div_const (radius b))
  have hangle := hbeta.const_add (baseAngle b)
  refine (hangle.const_sub (Real.pi/2)).congr_deriv ?_
  rw [inverse_root hb hz]
  field_simp [hn.ne',hd.2.2.1.ne']

lemma F_paid {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z∈shifts)
    (hdiag : TargetRatio.z≤z) : VLabel.d1 b<F z b := by
  have hd := data hb hz
  have hd0 := NegativeTwo.ContactInverse.data hb TargetRatio.z_mem
  have hq : 0<Inverse.q (U b) := by linarith [(Inverse.range_data
    (show U b∈Inverse.interval from ⟨(UW_bounds hb).1.le,(UW_bounds hb).2.1.le⟩)).2]
  have hsmall : speed z b≤TargetRatio.speed b := by
    apply Real.sqrt_le_sqrt
    nlinarith [hz.1,TargetRatio.z_bounds.1]
  have hz0 : 0≤TargetRatio.z := by linarith [TargetRatio.z_bounds.1]
  have hprod := mul_le_mul hdiag hsmall hd.2.2.1.le hz.1
  have hquot : TargetRatio.z/TargetRatio.speed b≤z/speed z b := by
    apply (div_le_div_iff₀ hd0.2.2.2.2.1 hd.2.2.1).2
    exact hprod
  have hr : 0≤ratio b/Inverse.q (U b) :=
    div_nonneg (by linarith [(outer_ratio_bounds hb).1]) hq.le
  have hm := mul_le_mul_of_nonneg_left hquot hr
  have he0 : TargetRatio.F b=Inverse.factor (U b)+
      (ratio b/Inverse.q (U b))*(TargetRatio.z/TargetRatio.speed b) := by
    rw [TargetRatio.F_formula]
    ring
  have he : F z b=Inverse.factor (U b)+
      (ratio b/Inverse.q (U b))*(z/speed z b) := by dsimp [F]; ring
  rw [he]
  have hp := TargetRatio.paid hb
  rw [he0] at hp
  linarith

lemma targetCost_monotone {z : ℝ} (hz : z∈shifts) (hdiag : TargetRatio.z≤z) :
    MonotoneOn (targetCost z) (Icc 0 outerDiagonal) := by
  have hd {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
      HasDerivAt (targetCost z) (F z b-VLabel.d1 b) b := by
    exact (X_source_hasDerivAt hb hz).sub (VLabel.outer_hasDerivAt (outer_domain hb))
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (hd hb).continuousAt.continuousWithinAt
  · exact fun b hb => hd (Ioo_subset_Icc_self hb)
  · intro b hb
    linarith [F_paid (Ioo_subset_Icc_self hb) hz hdiag]

lemma aligned {b z : ℝ} (hb : b∈Icc 0 outerDiagonal) (hz : z=W b) : X z b=0 := by
  have ha := NegativeTwo.ContactInverse.base_bounds hb
  have ht := NegativeTwo.ContactInverse.base_trig hb
  have hrange : -(Real.pi/2)≤Real.pi/2-baseAngle b ∧
      Real.pi/2-baseAngle b≤Real.pi/2 := by
    constructor <;> linarith [Real.pi_pos]
  have hs : z/radius b=Real.sin (Real.pi/2-baseAngle b) := by
    rw [Real.sin_pi_div_two_sub,ht.1,hz]
  dsimp [X,inverseAngle,NegativeTwo.ContactInverse.angle]
  rw [hs,Real.arcsin_sin hrange.1 hrange.2]
  ring

/-- A weak physical upper-primary inequality lies after its explicit
inverse contact angle, even when that angle is negative. -/
lemma weak_angle {a b z x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10)) (hz : z∈shifts)
    (hcut : upperPrimary a b x≤z+1/2) : X z b≤x := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2⟩
  have hd := data hb hz
  have hn : 0<radius b := by linarith [hd.1]
  have ha := NegativeTwo.ContactInverse.base_bounds hb
  have ht := NegativeTwo.ContactInverse.base_trig hb
  let y : ℝ := Real.pi/2-x-baseAngle b
  have hy : -(Real.pi/2)≤y ∧ y≤Real.pi/2 := by
    dsimp [y]
    constructor <;> linarith [hx.1,hx.2,ha.1,ha.2,pi_hand_enclosure.1]
  have hsine : Real.sin y=
      (W b*Real.cos x-(U b-1)*Real.sin x)/radius b := by
    rw [show y=Real.pi/2-(x+baseAngle b) by dsimp [y]; ring,
      Real.sin_pi_div_two_sub,Real.cos_add,ht.1,ht.2]
    field_simp [hn.ne']
  have hnum : W b*Real.cos x-(U b-1)*Real.sin x≤z := by
    dsimp [upperPrimary] at hcut
    rw [←(ShortOuterOne.SameContact.actual_arc hs).1] at hcut
    dsimp [U,W]
    linarith
  have hsin : Real.sin y≤z/radius b := by
    rw [hsine]
    exact div_le_div_of_nonneg_right hnum hn.le
  have hh := Real.arcsin_le_arcsin hsin
  rw [Real.arcsin_sin hy.1 hy.2] at hh
  dsimp [X,inverseAngle,NegativeTwo.ContactInverse.angle,y] at *
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo.PrimaryInverse
end
end
end

section
/-!
## The zero-target boundary of the upper source-primary contact

On source primary heights between the diagonal and one, the source
primary label has second derivative greater than .9.  Its derivative
times the actual contact speed increases toward one and remains
strictly below one there.  The complete boundary cost therefore
decreases to the already proved aligned endpoint.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.PrimaryAxis

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def interval : Set ℝ := Icc outerDiagonal 1
def speed (a : ℝ) : ℝ := NegativeTwo.ContactInverse.speed (a-1/2) 0
def product (a : ℝ) : ℝ := PPrimaryLabel.d1 a*speed a
def productD (a : ℝ) : ℝ :=
  PPrimaryLabel.d2 a*speed a-PPrimaryLabel.d1 a*(a-1/2)/speed a
def cost (a : ℝ) : ℝ :=
  Real.pi/2+PrimaryInverse.X (a-1/2) 0+PPrimaryLabel.outer a-V 0
def first (a : ℝ) : ℝ := PPrimaryLabel.d1 a-1/speed a

lemma primary_mem {a : ℝ} (ha : a∈interval) : a∈Icc outerDiagonal outerAxial :=
  ⟨ha.1,ha.2.trans primary_one_mem.2⟩

lemma shift_mem {a : ℝ} (ha : a∈interval) : a-1/2∈PrimaryInverse.shifts := by
  constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2]

lemma source_first_formula (a : ℝ) :
    PPrimaryLabel.d1 a=2363/100000+(2363/50000)*a+(2211/20000)*arc a+
      (22663/25000-(2211/20000)*a)*ratio a := by
  dsimp [RoleLabel.d1,PPrimaryLabel,RoleLabel.primary,PLabel]
  ring

lemma source_second_formula (a : ℝ) :
    PPrimaryLabel.d2 a=2363/50000-(2211/10000)*ratio a+
      (22663/25000-(2211/20000)*a)*ratioD a := by
  dsimp [RoleLabel.d2,PPrimaryLabel,RoleLabel.primary,PLabel]
  ring

lemma ratio_upper {a : ℝ} (ha : a∈interval) : ratio a<117/100 := by
  have hp : 0<arc a+1/2 := U_positive (primary_domain (primary_mem ha))
  have hm := ShortOuterOne.SameContact.arc_antitone
    (primary_domain (primary_mem ha)) (primary_domain primary_one_mem) ha.2
  change bOne≤arc a at hm
  change (a+1/2)/(arc a+1/2)<117/100
  apply (div_lt_iff₀ hp).2
  linarith [bOne_bounds.1,ha.2]

lemma ratioD_lower {a : ℝ} (ha : a∈interval) : (71/50:ℝ)<ratioD a := by
  have hp := U_positive (primary_domain (primary_mem ha))
  have hb := primary_secondary_mem (primary_mem ha)
  have hU : U a<7/5 := by dsimp [U]; linarith [hb.2,outer_endpoint_bounds.2.2.2]
  have hcube := pow_le_pow_left₀ hp.le hU.le 3
  change (71/50:ℝ)<Q0/(U a)^3
  apply (lt_div_iff₀ (pow_pos hp 3)).2
  norm_num [Q0]
  nlinarith

lemma source_first_positive {a : ℝ} (ha : a∈interval) : 0<PPrimaryLabel.d1 a := by
  have hr := primary_ratio_one (primary_mem ha)
  have hb := primary_secondary_mem (primary_mem ha)
  have hc : 0<22663/25000-(2211/20000)*a := by linarith [ha.2]
  have hm := mul_pos hc (show 0<ratio a by linarith)
  rw [source_first_formula]
  nlinarith [ha.1,fine_outer_endpoint_bounds.2,hb.1]

lemma source_second_lower {a : ℝ} (ha : a∈interval) : (9/10:ℝ)<PPrimaryLabel.d2 a := by
  have hr := ratio_upper ha
  have hD := ratioD_lower ha
  have hc : (159/200:ℝ)<22663/25000-(2211/20000)*a := by linarith [ha.2]
  have hm := mul_lt_mul hc hD.le (by norm_num : (0:ℝ)<71/50)
    (by linarith : 0≤22663/25000-(2211/20000)*a)
  rw [source_second_formula]
  nlinarith

lemma source_first_monotone : MonotoneOn PPrimaryLabel.d1 interval :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (PPrimaryLabel.d1_hasDerivAt (primary_domain (primary_mem ha))).continuousAt.continuousWithinAt)
    (fun _ ha => PPrimaryLabel.d1_hasDerivAt (primary_domain (primary_mem (Ioo_subset_Icc_self ha))))
    (fun _ ha => by linarith [source_second_lower (Ioo_subset_Icc_self ha)])

lemma source_first_one : PPrimaryLabel.d1 1<(271/250:ℝ) := by
  have hh := PPrimaryLabel.first_chart_reference (b := (1:ℝ))
    (l := (129058126439213/100000000000000:ℝ))
    (u := (64529063219607/50000000000000:ℝ))
    (dlo := (27/25:ℝ)) (dhi := (271/250:ℝ)) (primary_domain primary_one_mem)
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,W,Q0])
    (by norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,W,Q0])
  exact hh.2

lemma source_first_upper {a : ℝ} (ha : a∈interval) : PPrimaryLabel.d1 a<(271/250:ℝ) :=
  (source_first_monotone ha ⟨primary_one_mem.1,le_rfl⟩ ha.2).trans_lt source_first_one

lemma speed_data {a : ℝ} (ha : a∈interval) :
    0<speed a ∧ (a-1/2)^2+(speed a)^2=Inverse.q (U 0) := by
  have hd := PrimaryInverse.data outer_zero_mem (shift_mem ha)
  exact ⟨hd.2.2.1,hd.2.2.2⟩

lemma speed_square_lower {a : ℝ} (ha : a∈interval) : (209/250:ℝ)<(speed a)^2 := by
  have hd := speed_data ha
  have hz : 0≤a-1/2 := by linarith [ha.1,fine_outer_endpoint_bounds.2]
  have hz2 := pow_le_pow_left₀ hz (show a-1/2≤(1/2:ℝ) by linarith [ha.2]) 2
  nlinarith [TargetRatio.zero_q.1,hd.2]

lemma speed_hasDerivAt {a : ℝ} (ha : a∈interval) :
    HasDerivAt speed (-(a-1/2)/speed a) a := by
  have hd := speed_data ha
  have hrad : Inverse.q (U 0)-(a-1/2)^2≠0 := by nlinarith [sq_pos_of_pos hd.1]
  have hin : HasDerivAt (fun y => Inverse.q (U 0)-(y-1/2)^2) (-(2*(a-1/2))) a :=
    ((hasDerivAt_const a (Inverse.q (U 0))).sub
      (((hasDerivAt_id a).sub_const (1/2)).pow 2)).congr_deriv (by simp)
  have hv : speed a=Real.sqrt (Inverse.q (U 0)-(a-1/2)^2) := rfl
  refine (hin.sqrt hrad).congr_deriv ?_
  rw [← hv]
  field_simp [hd.1.ne']

lemma product_hasDerivAt {a : ℝ} (ha : a∈interval) :
    HasDerivAt product (productD a) a := by
  exact ((PPrimaryLabel.d1_hasDerivAt (primary_domain (primary_mem ha))).mul
    (speed_hasDerivAt ha)).congr_deriv (by dsimp only [productD]; ring)

lemma productD_positive {a : ℝ} (ha : a∈interval) : 0<productD a := by
  have hd := speed_data ha
  have hM := source_first_positive ha
  have hz : 0≤a-1/2 := by linarith [ha.1,fine_outer_endpoint_bounds.2]
  have hmain := mul_le_mul (source_second_lower ha).le (speed_square_lower ha).le
    (by norm_num : (0:ℝ)≤209/250) (by linarith [source_second_lower ha])
  have hlast := mul_le_mul (source_first_upper ha).le
    (show a-1/2≤(1/2:ℝ) by linarith [ha.2]) hz (by norm_num : (0:ℝ)≤271/250)
  have he : productD a*speed a=
      PPrimaryLabel.d2 a*(speed a)^2-PPrimaryLabel.d1 a*(a-1/2) := by
    dsimp [productD]
    field_simp [hd.1.ne']
  nlinarith

lemma product_monotone : MonotoneOn product interval :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (product_hasDerivAt ha).continuousAt.continuousWithinAt)
    (fun _ ha => product_hasDerivAt (Ioo_subset_Icc_self ha))
    (fun _ ha => (productD_positive (Ioo_subset_Icc_self ha)).le)

lemma speed_one : speed 1=outerAxial-1/2 := by
  have hd := speed_data ⟨primary_one_mem.1,le_rfl⟩
  have hc := UW_circle (outer_domain outer_zero_mem)
  have hu : U 0=outerAxial+1/2 := by
    simp [U,ShortOuterOne.SameContact.arc_zero]
  norm_num [W] at hc
  rw [hu] at hc hd
  dsimp [Inverse.q,NegativeTwo.Inverse.q] at hd
  have hp : 0<outerAxial-1/2 := by linarith [ShortOuterZero.fine_axial_bounds.1]
  nlinarith

lemma product_one : product 1<1 := by
  have hM := source_first_one
  have hMp := source_first_positive ⟨primary_one_mem.1,le_rfl⟩
  have hv : 0<outerAxial-1/2 := by linarith [ShortOuterZero.fine_axial_bounds.1]
  have hm := mul_lt_mul_of_pos_right hM hv
  dsimp [product]
  rw [speed_one]
  nlinarith [ShortOuterZero.fine_axial_bounds.2]

lemma product_paid {a : ℝ} (ha : a∈interval) : product a<1 :=
  (product_monotone ha ⟨primary_one_mem.1,le_rfl⟩ ha.2).trans_lt product_one

lemma cost_hasDerivAt {a : ℝ} (ha : a∈interval) : HasDerivAt cost (first a) a := by
  have hX := (PrimaryInverse.X_shift_hasDerivAt outer_zero_mem (shift_mem ha)).comp a
    ((hasDerivAt_id a).sub_const (1/2))
  exact (((hX.const_add (Real.pi/2)).add
    (PPrimaryLabel.outer_hasDerivAt (primary_domain (primary_mem ha)))).sub_const (V 0)).congr_deriv
    (by dsimp only [first,speed]; ring)

lemma first_negative {a : ℝ} (ha : a∈interval) : first a<0 := by
  have hv := (speed_data ha).1
  have hp := product_paid ha
  have he : first a*speed a=product a-1 := by
    dsimp [first,product]
    field_simp [hv.ne']
  nlinarith

lemma cost_antitone : AntitoneOn cost interval :=
  antiOn_of_hasDeriv_nonpos
    (fun _ ha => (cost_hasDerivAt ha).continuousAt.continuousWithinAt)
    (fun _ ha => cost_hasDerivAt (Ioo_subset_Icc_self ha))
    (fun _ ha => (first_negative (Ioo_subset_Icc_self ha)).le)

theorem cost_lower {a : ℝ} (ha : a∈interval) : (44889/50000:ℝ)<cost a := by
  have hm := cost_antitone ha ⟨primary_one_mem.1,le_rfl⟩ ha.2
  have hX := PrimaryInverse.aligned outer_zero_mem (show (1-1/2:ℝ)=W 0 by norm_num [W])
  have hM : PPrimaryLabel.outer 1= -P bOne :=
    PLabel.primary_actual (primary_state primary_one_mem)
  dsimp [cost] at hm ⊢
  rw [hX,hM] at hm
  linarith [aligned_axial_value]

end SquaresInCircles.Eight.SecondWord.OppositeTwo.PrimaryAxis
end
end
end

section
/-!
## The whole-circle source speed comparison

Convexity supplies one affine upper bound for the source derivative.
Two exact circle supports then pay the full angular displacement on
the original interval.  The argument has no source-coordinate cells.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma P_first_zero : PLabel.d1 0<387/500 := P_first_zero_bounds.2

lemma P_first_affine {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    PLabel.d1 b<387/500+(223/1000)*b := by
  have hh := positive_of_second_nonpos
    (f := fun t => 387/500+(223/1000)*t-PLabel.d1 t)
    (d := fun t => 223/1000-PLabel.d2 t)
    (dd := fun t => -PLabel.d3 t) hb
    (fun t ht => ((((hasDerivAt_id t).const_mul (223/1000)).const_add (387/500)).sub
        (PLabel.d1_hasDerivAt (outer_domain ht))).congr_deriv (by ring))
    (fun t ht => (PLabel.d2_hasDerivAt (outer_domain ht)).const_sub (223/1000))
    (fun t ht => neg_nonpos.mpr (P_third_positive ht).le)
    (by simpa using sub_pos.mpr P_first_zero)
    (by rw [P_first_diagonal]; linarith [fine_outer_endpoint_bounds.2])
  linarith

lemma k_positive {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<k b x := by
  have hh := mul_nonneg (by linarith [(outer_ratio_bounds hb).1] : 0≤ratio b)
    (positive_trig hx).2.2.1
  dsimp [k]
  linarith [(positive_trig hx).1]

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

theorem original_upper_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2⟩
  have hz : a-1/2∈PrimaryInverse.shifts := by
    constructor <;> linarith [(outer_bounds hs).1,(outer_bounds hs).2.1,
      fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.1]
  have hdiag : TargetRatio.z≤a-1/2 := by
    dsimp [TargetRatio.z]
    linarith [(outer_bounds hs).1]
  have hcut : upperPrimary A B x≤(a-1/2)+1/2 := by
    have hw := upper_width hx
    norm_num [forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
    dsimp [upperPrimary]
    linarith
  have hX := PrimaryInverse.weak_angle ht hx hz hcut
  have hmono := PrimaryInverse.targetCost_monotone hz hdiag
  by_cases ha : 1≤a
  · have hbase : a-1∈Icc 0 outerDiagonal := by
      refine ⟨by linarith,?_⟩
      linarith [(outer_bounds hs).2.1,outer_endpoint_bounds.2.1,fine_outer_endpoint_bounds.2]
    by_cases hBbase : B≤a-1
    · have halign := aligned_right_original hs ht (by linarith)
      dsimp [value] at *
      linarith [hx.1]
    · have hstep := hmono hbase hB (by linarith)
      have hzero := PrimaryInverse.aligned hbase
        (show a-1/2=W (a-1) by dsimp [W]; ring)
      dsimp [PrimaryInverse.targetCost] at hstep
      rw [hzero] at hstep
      have halign := aligned_right_original hs (ShortOuterOne.SameContact.arc_state hbase)
        (show 1+(a-1)≤a by linarith)
      dsimp [value] at *
      linarith
  · have hA : a∈PrimaryAxis.interval := ⟨(outer_bounds hs).1,by linarith⟩
    have hbase := PrimaryAxis.cost_lower hA
    have hstep := hmono outer_zero_mem hB hB.1
    have hsource : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
    dsimp [PrimaryAxis.cost,PrimaryInverse.targetCost,value] at *
    rw [hsource] at hbase
    linarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end
