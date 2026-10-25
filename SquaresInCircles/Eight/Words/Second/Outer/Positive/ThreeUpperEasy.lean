module

public import SquaresInCircles.Eight.Words.Second.Outer.LBounds
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.VBounds

/-!
# Eight squares: the last two original upper owners for positive edge three

The target-secondary owner caps its actual target coordinate on the
whole upper interval.  The source-primary owner has a sharper cap on
the initial strip; all later angles were closed by the original label
bounds.  Both arguments retain weak separators and actual states.
-/

section
/-!
## Original positive edge-three cost and its four actual weak axes

The role-three positive source label is `V` and its positive target
label is `L`.  Every projection below is an algebraic rearrangement of
the same original separator on the original common circle.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def value (b B φ : ℝ) : ℝ := φ+V b-L B
def lowerAngle : ℝ := Real.pi/2-7/10
def Lower (φ : ℝ) : Prop := φ∈Icc lowerAngle (Real.pi/2)

lemma cost_identity {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    SecondWord.cost 3 .outer .outer true true a b A B φ=value b B φ := by
  unfold value
  rw [show V b=VLabel.eval a b from VLabel.outer_actual hs,
    show L B=LLabel.eval A B from LLabel.outer_actual ht]
  norm_num [SecondWord.cost,label,QuarterWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,VLabel,LLabel,RoleLabel.eval]

lemma lower_deviation {φ : ℝ} (hφ : Lower φ) :
    Real.pi/2-φ∈Icc 0 (7/10) := by
  dsimp [Lower,lowerAngle] at hφ
  constructor <;> linarith [hφ.1,hφ.2]

lemma lower_trig {φ : ℝ} (hφ : Lower φ) :
    (19121/25000:ℝ)<Real.sin φ ∧ Real.sin φ≤1 ∧
      0≤Real.cos φ ∧ Real.cos φ<16106/25000 ∧
      1≤Real.sin φ+Real.cos φ := by
  have hh := positive_trig (lower_deviation hφ)
  simp only [Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,sub_zero,zero_add] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,by linarith [hh.2.2.2.2.2]⟩

lemma lower_width {φ : ℝ} (hφ : Lower φ) :
    pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
  have hh := NegativeTwo.lower_width (lower_deviation hφ)
  have he : Real.pi/2-(Real.pi/2-φ)=φ := by ring
  rw [he] at hh
  simpa only [Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,sub_zero,zero_add] using hh

lemma lower_source_secondary_cut {a b A B φ : ℝ} (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (1+Real.sin φ+Real.cos φ)/2≤b+A*Real.sin φ-B*Real.cos φ := by
  norm_num [Eight.forwardMargin,lower_width hφ] at hm
  linarith

lemma lower_target_secondary_cut {a b A B φ : ℝ} (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 1 φ) :
    B≤a*Real.sin φ+b*Real.cos φ-(1+Real.sin φ+Real.cos φ)/2 := by
  norm_num [Eight.forwardMargin,lower_width hφ] at hm
  linarith

lemma lower_source_primary_cut {a b A B φ : ℝ} (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 φ) :
    A*Real.cos φ+B*Real.sin φ≤a-(1+Real.sin φ+Real.cos φ)/2 := by
  norm_num [Eight.forwardMargin,lower_width hφ] at hm
  linarith

lemma upper_source_secondary_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 (Real.pi/2+x)) :
    1/2-(A-1/2)*Real.cos x-(B-1/2)*Real.sin x≤b := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  linarith

lemma upper_target_primary_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B 1 1 (Real.pi/2+x)) :
    1/2≤A+(a-1/2)*Real.sin x+(b-1/2)*Real.cos x := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  linarith

lemma upper_target_secondary_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 1 (Real.pi/2+x)) :
    B≤(a-1/2)*Real.cos x-(b+1/2)*Real.sin x-1/2 := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  linarith

lemma upper_source_primary_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 (Real.pi/2+x)) :
    (B+1/2)*Real.cos x≤a-1/2+(A-1/2)*Real.sin x := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  linarith

lemma late_angle {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : (419/250:ℝ)≤φ) : (8979/10000:ℝ)<value b B φ := by
  have hv := V_lower (NegativeTwo.source_mem hs)
  have hL := L_upper (NegativeTwo.source_mem ht)
  dsimp [value]
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree
end
end
end

section
/-!
## The two original aligned endpoints for positive edge three

The zero-source target has primary coordinate one.  The other endpoint
is the target diagonal with source coordinate `1-d`.  Their actual
circle radicals are enclosed by integer-square comparisons; both
endpoint costs strictly exceed the final threshold.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def zeroTarget : ℝ := arc 1
def alignedSource : ℝ := 1-outerDiagonal

lemma zeroTarget_state : OuterState 1 zeroTarget :=
  ShortOuterOne.SameContact.primary_state primary_one_mem

lemma zeroTarget_mem : zeroTarget∈Icc 0 outerDiagonal :=
  NegativeTwo.source_mem zeroTarget_state

lemma zeroTarget_arc : arc zeroTarget=1 :=
  (ShortOuterOne.SameContact.actual_arc zeroTarget_state).1

lemma zeroTarget_U : U zeroTarget=(3/2:ℝ) := by
  dsimp [U]
  rw [zeroTarget_arc]
  norm_num

lemma zeroTarget_bounds :
    (79058126439213/100000000000000:ℝ)<zeroTarget ∧
      zeroTarget<79058126439214/100000000000000 := by
  have hc := zeroTarget_state.2.2
  have hb := zeroTarget_mem.1
  norm_num [Q0] at hc
  constructor <;> nlinarith

lemma zeroTarget_labels :
    L zeroTarget<(65379/100000:ℝ) ∧ LLabel.d1 zeroTarget<89/100 ∧
      (2:ℝ)<LLabel.d2 zeroTarget := by
  have hh := LReference.target zeroTarget_mem
    ⟨zeroTarget_bounds.1.le,zeroTarget_bounds.2.le⟩
    (show U zeroTarget∈Icc (3/2) (3/2) by rw [zeroTarget_U]; exact ⟨le_rfl,le_rfl⟩)
    (by norm_num) (by norm_num)
  norm_num [LReference.valueLo,LReference.valueHi,LReference.firstLo,
    LReference.firstHi,LReference.secondLo,LReference.secondHi,Q0] at hh
  exact ⟨by linarith,by linarith,by linarith⟩

lemma zeroTarget_ratio : (43/50:ℝ)<ratio zeroTarget := by
  change (43/50:ℝ)<W zeroTarget/U zeroTarget
  rw [zeroTarget_U]
  dsimp [W]
  linarith [zeroTarget_bounds.1]

lemma zero_aligned_value : (361/400:ℝ)<value 0 zeroTarget (Real.pi/2) := by
  dsimp [value]
  linarith [pi_hand_enclosure.1,V_zero_bounds.1,zeroTarget_labels.1]

lemma alignedSource_mem : alignedSource∈Icc 0 outerDiagonal := by
  dsimp [alignedSource]
  constructor <;> linarith [fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]

lemma alignedSource_bounds :
    (10078593489059/100000000000000:ℝ)<alignedSource ∧
      alignedSource<10078593489060/100000000000000 := by
  dsimp [alignedSource]
  constructor <;> linarith [diagonal_fine.1,diagonal_fine.2]

lemma alignedSource_U_bounds :
    (188537960645532/100000000000000:ℝ)<U alignedSource ∧
      U alignedSource<188537960645533/100000000000000 := by
  have hc := UW_circle (outer_domain alignedSource_mem)
  have hp := U_positive (outer_domain alignedSource_mem)
  have hb := alignedSource_bounds
  have hslo : (60078593489059/100000000000000:ℝ)^2<(W alignedSource)^2 := by
    dsimp [W]
    nlinarith [hb.1]
  have hshi : (W alignedSource)^2<(60078593489060/100000000000000:ℝ)^2 := by
    dsimp [W]
    nlinarith [hb.1,hb.2]
  norm_num [Q0] at hc
  constructor <;> nlinarith

lemma alignedSource_value : (452799/5000000:ℝ)<V alignedSource := by
  have hb := alignedSource_bounds
  have hu := alignedSource_U_bounds
  have hp := mul_le_mul
    (show (138537960645532/100000000000000:ℝ)≤U alignedSource-1/2 by linarith)
    hb.1.le (by norm_num : (0:ℝ)≤10078593489059/100000000000000)
    (by linarith : 0≤U alignedSource-1/2)
  have he : V alignedSource= -(41/4000)*(U alignedSource-1/2)+
      (16031/100000)*alignedSource+
        (63457/100000)*(U alignedSource-1/2)*alignedSource := by
    dsimp [V,RoleLabel.outer,RoleLabel.eval,VLabel,U]
    ring
  rw [he]
  nlinarith [hb.1,hu.2]

lemma diagonal_aligned_value :
    (44889/50000:ℝ)<value alignedSource outerDiagonal (Real.pi/2) := by
  dsimp [value]
  linarith [pi_hand_enclosure.1,alignedSource_value,L_diagonal_upper]

end SquaresInCircles.Eight.SecondWord.PositiveThree
end
end
end

section
/-!
## Actual least-source contacts for the first positive edge-three axis

The source coordinate comes directly from the original weak separator.
The cost has a strictly concave first derivative on every closed
physical contact interval.  The derivative formulas below keep the
actual source and target circle coordinates throughout.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.FirstContact

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def source (B φ : ℝ) : ℝ := 1/2+(1-U B)*Real.sin φ+W B*Real.cos φ
def sourceFirst (B φ : ℝ) : ℝ := ratio B*Real.sin φ+Real.cos φ
def sourceSecond (B φ : ℝ) : ℝ := ratioD B*Real.sin φ
def sourceThird (B φ : ℝ) : ℝ := ratioDD B*Real.sin φ
def cost (B φ : ℝ) : ℝ := φ+V (source B φ)-L B
def first (B φ : ℝ) : ℝ := VLabel.d1 (source B φ)*sourceFirst B φ-LLabel.d1 B
def second (B φ : ℝ) : ℝ :=
  VLabel.d2 (source B φ)*(sourceFirst B φ)^2+
    VLabel.d1 (source B φ)*sourceSecond B φ-LLabel.d2 B
def third (B φ : ℝ) : ℝ :=
  VLabel.d3 (source B φ)*(sourceFirst B φ)^3+
    3*VLabel.d2 (source B φ)*sourceFirst B φ*sourceSecond B φ+
    VLabel.d1 (source B φ)*sourceThird B φ-LLabel.d3 B

def Domain (B φ : ℝ) : Prop :=
  B∈Icc 0 outerDiagonal ∧ source B φ∈Icc 0 outerDiagonal ∧ Lower φ

lemma source_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (φ : ℝ) :
    HasDerivAt (fun t => source t φ) (sourceFirst B φ) B := by
  have hd := (((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add_const
    (1/2)).const_sub 1).mul_const (Real.sin φ)).const_add (1/2)).add
    (((hasDerivAt_id' B).add_const (1/2)).mul_const (Real.cos φ))
  convert hd using 1
  · funext t
    simp only [source,U,W,Pi.add_apply]
  · dsimp only [sourceFirst]
    ring

lemma sourceFirst_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (φ : ℝ) :
    HasDerivAt (fun t => sourceFirst t φ) (sourceSecond B φ) B := by
  convert ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).mul_const
    (Real.sin φ)).add_const (Real.cos φ) using 1 <;>
    dsimp [sourceFirst,sourceSecond]

lemma sourceSecond_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (φ : ℝ) :
    HasDerivAt (fun t => sourceSecond t φ) (sourceThird B φ) B := by
  exact (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hB)).mul_const
    (Real.sin φ)

lemma cost_hasDerivAt {B φ : ℝ} (h : Domain B φ) :
    HasDerivAt (fun t => cost t φ) (first B φ) B := by
  have hv := (VLabel.outer_hasDerivAt (outer_domain h.2.1)).comp B
    (source_hasDerivAt h.1 φ)
  convert (hv.const_add φ).sub (LLabel.outer_hasDerivAt (outer_domain h.1)) using 1
  · funext t
    simp only [cost,V,L,Pi.sub_apply,Function.comp_apply]
  · rfl

lemma first_hasDerivAt {B φ : ℝ} (h : Domain B φ) :
    HasDerivAt (fun t => first t φ) (second B φ) B := by
  have hv := (VLabel.d1_hasDerivAt (outer_domain h.2.1)).comp B
    (source_hasDerivAt h.1 φ)
  convert (hv.mul (sourceFirst_hasDerivAt h.1 φ)).sub
    (LLabel.d1_hasDerivAt (outer_domain h.1)) using 1
  · funext t
    simp only [first,Pi.sub_apply,Pi.mul_apply,Function.comp_apply]
  · simp only [second,Function.comp_apply]
    ring

lemma second_hasDerivAt {B φ : ℝ} (h : Domain B φ) :
    HasDerivAt (fun t => second t φ) (third B φ) B := by
  have hv2 := (VLabel.d2_hasDerivAt (outer_domain h.2.1)).comp B
    (source_hasDerivAt h.1 φ)
  have hv1 := (VLabel.d1_hasDerivAt (outer_domain h.2.1)).comp B
    (source_hasDerivAt h.1 φ)
  convert ((hv2.mul ((sourceFirst_hasDerivAt h.1 φ).pow 2)).add
    (hv1.mul (sourceSecond_hasDerivAt h.1 φ))).sub
      (LLabel.d2_hasDerivAt (outer_domain h.1)) using 1
  · funext t
    simp only [second,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,
      Function.comp_apply]
  · simp only [third,Function.comp_apply,Pi.pow_apply]
    ring

lemma sourceFirst_positive {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) (hφ : Lower φ) :
    0<sourceFirst B φ := by
  have ht := lower_trig hφ
  have hp := mul_pos (ShortOuterOne.SameContact.ratio_pos (outer_domain hB))
    (show 0<Real.sin φ by linarith [ht.1])
  dsimp [sourceFirst]
  linarith [ht.2.2.1]

lemma sourceSecond_positive {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) (hφ : Lower φ) :
    0<sourceSecond B φ :=
  mul_pos (outer_ratio_bounds hB).2.2.1 (by linarith [(lower_trig hφ).1])

lemma third_negative {B φ : ℝ} (h : Domain B φ) : third B φ<0 := by
  have hv3 := V_third_negative h.2.1
  have hv2 : VLabel.d2 (source B φ)<0 := by linarith [V_second_upper h.2.1]
  have hp := sourceFirst_positive h.1 h.2.2
  have hq := sourceSecond_positive h.1 h.2.2
  have hfirst := mul_neg_of_neg_of_pos hv3 (pow_pos hp 3)
  have hsecond := mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num : (0:ℝ)<3) hv2) hp) hq
  have hs := lower_trig h.2.2
  have hd := (outer_ratio_bounds h.1).2.2.1
  have hDD := ratioDD_positive h.1
  have hDcap := outer_ratioDD_comparison h.1
  have hthird : 0≤ sourceThird B φ ∧ sourceThird B φ≤ratioDD B := by
    dsimp [sourceThird]
    exact ⟨mul_nonneg hDD.le (by linarith [hs.1]),
      by simpa using mul_le_mul_of_nonneg_left hs.2.1 hDD.le⟩
  have hv1 : 0≤VLabel.d1 (source B φ) := by
    linarith [(V_first_bounds h.2.1).1]
  have hprod := mul_le_mul (V_first_upper h.2.1).le
    (hthird.2.trans hDcap.le) hthird.1 (by norm_num : (0:ℝ)≤1061/1000)
  have hBprod := mul_nonneg h.1.1 hDD.le
  have hL : (284163/50000)*ratioD B≤LLabel.d3 B := by
    norm_num [RoleLabel.d3,LLabel]
    nlinarith
  dsimp [third]
  norm_num at hprod
  nlinarith

lemma original_cut {a b A B φ : ℝ} (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) : source B φ≤b := by
  have hh := lower_source_secondary_cut hφ hm
  dsimp [source,U,W]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  linarith

lemma source_at_quarter (B : ℝ) : source B (Real.pi/2)=1-arc B := by
  simp [source,U,W]
  ring

lemma source_monotone {φ : ℝ} (hφ : Lower φ) :
    MonotoneOn (fun B => source B φ) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hB => (source_hasDerivAt hB φ).continuousAt.continuousWithinAt)
    (fun _ hB => source_hasDerivAt (Ioo_subset_Icc_self hB) φ)
    (fun _ hB => (sourceFirst_positive (Ioo_subset_Icc_self hB) hφ).le)

end SquaresInCircles.Eight.SecondWord.PositiveThree.FirstContact
end
end
end

section
/-!
## A whole-angle proof for the fourth lower original owner

The actual weak projection forces an angle above `1.2`.  Its necessary
target cap gives a single decreasing scalar on the entire remaining
interval, whose quarter-turn value has a strict reserve above `1.02`.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig

lemma lower_cos_antitone : AntitoneOn Real.cos (Icc lowerAngle (Real.pi/2)) :=
  antiOn_of_hasDeriv_nonpos
    (fun t _ => (Real.hasDerivAt_cos t).continuousAt.continuousWithinAt)
    (fun t _ => Real.hasDerivAt_cos t)
    (fun t ht => by linarith [(lower_trig (Ioo_subset_Icc_self ht)).1])

lemma lower_sin_monotone : MonotoneOn Real.sin (Icc lowerAngle (Real.pi/2)) :=
  monoOn_of_hasDeriv_nonneg
    (fun t _ => (Real.hasDerivAt_sin t).continuousAt.continuousWithinAt)
    (fun t _ => Real.hasDerivAt_sin t)
    (fun _ ht => (lower_trig (Ioo_subset_Icc_self ht)).2.2.1)

lemma six_fifths_lower : Lower (6/5) := by
  refine ⟨?_,?_⟩
  · dsimp [lowerAngle]
    linarith [pi_hand_enclosure.2]
  · linarith [pi_hand_enclosure.1]

lemma six_fifths_trig :
    (233/250:ℝ)<Real.sin (6/5) ∧ (7247/20000:ℝ)<Real.cos (6/5) ∧
      Real.cos (6/5)<363/1000 := by
  have hs := sin11_le_sin (show (0:ℝ)≤6/5 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤6/5 by norm_num)
  have hcu := cos_le_cos12 (show (0:ℝ)≤6/5 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hc hcu
  exact ⟨by linarith,by linarith,by linarith⟩

def fourthNecessary (φ : ℝ) : ℝ :=
  outerAxial-1/2-(1/2)*Real.sin φ-(outerDiagonal+1/2)*Real.cos φ

lemma fourthNecessary_hasDerivAt (φ : ℝ) :
    HasDerivAt fourthNecessary
      ((outerDiagonal+1/2)*Real.sin φ-(1/2)*Real.cos φ) φ := by
  convert (((Real.hasDerivAt_sin φ).const_mul (1/2)).const_sub
    (outerAxial-1/2)).sub ((Real.hasDerivAt_cos φ).const_mul (outerDiagonal+1/2))
    using 1
  · funext t
    simp only [fourthNecessary,Pi.sub_apply]
  · ring

lemma fourthNecessary_monotone : MonotoneOn fourthNecessary
    (Icc lowerAngle (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun t _ => (fourthNecessary_hasDerivAt t).continuousAt.continuousWithinAt)
    (fun t _ => fourthNecessary_hasDerivAt t)
  intro t ht
  have hh := lower_trig (Ioo_subset_Icc_self ht)
  have hp := mul_le_mul
    (show (1399/1000:ℝ)≤outerDiagonal+1/2 by linarith [fine_outer_endpoint_bounds.2])
    hh.1.le (by norm_num : (0:ℝ)≤19121/25000)
    (by linarith [fine_outer_endpoint_bounds.2] : 0≤outerDiagonal+1/2)
  norm_num at hp
  linarith [hh.2.2.2.1]

lemma fourthNecessary_negative : fourthNecessary (6/5)<0 := by
  have ht := six_fifths_trig
  have hp := mul_le_mul
    (show (1399/1000:ℝ)≤outerDiagonal+1/2 by linarith [fine_outer_endpoint_bounds.2])
    ht.2.1.le (by norm_num : (0:ℝ)≤7247/20000)
    (by linarith [fine_outer_endpoint_bounds.2] : 0≤outerDiagonal+1/2)
  dsimp [fourthNecessary]
  nlinarith [ht.1,ShortOuterZero.fine_axial_bounds.2]

lemma fourth_angle_lower {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 φ) : (6/5:ℝ)<φ := by
  have hcut := lower_source_primary_cut hφ hm
  have htr := lower_trig hφ
  have hA := mul_le_mul_of_nonneg_right (NegativeTwo.primary_mem ht).1 htr.2.2.1
  have hB := mul_nonneg ht.1 (by linarith [htr.1] : 0≤Real.sin φ)
  have hn : 0≤fourthNecessary φ := by
    dsimp [fourthNecessary]
    linarith [(NegativeTwo.primary_mem hs).2]
  by_contra hh
  have hle : φ≤6/5 := by linarith
  have hd := fourthNecessary_monotone hφ six_fifths_lower hle
  linarith [fourthNecessary_negative]

def fourthCap (φ : ℝ) : ℝ :=
  ((outerAxial-1/2)-(outerDiagonal+1/2)*Real.cos φ)/Real.sin φ-1/2
def fourthCapFirst (φ : ℝ) : ℝ :=
  ((outerDiagonal+1/2)-(outerAxial-1/2)*Real.cos φ)/(Real.sin φ)^2
def fourthScalar (φ : ℝ) : ℝ := φ+V 0-793/20000-(147/125)*fourthCap φ

lemma fourthCap_hasDerivAt {φ : ℝ} (hφ : Lower φ) :
    HasDerivAt fourthCap (fourthCapFirst φ) φ := by
  have hp : Real.sin φ≠0 := by linarith [(lower_trig hφ).1]
  have hd := ((((Real.hasDerivAt_cos φ).const_mul (outerDiagonal+1/2)).const_sub
    (outerAxial-1/2)).div (Real.hasDerivAt_sin φ) hp).sub_const (1/2)
  convert hd using 1
  · rfl
  · dsimp only [fourthCapFirst]
    congr 1
    linear_combination -(outerDiagonal+1/2)*(Real.sin_sq_add_cos_sq φ)

lemma fourth_target_cap {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 φ) : B≤fourthCap φ := by
  have hcut := lower_source_primary_cut hφ hm
  have htr := lower_trig hφ
  have hp : 0<Real.sin φ := by linarith [htr.1]
  have hA := mul_le_mul_of_nonneg_right (NegativeTwo.primary_mem ht).1 htr.2.2.1
  have hline : (B+1/2)*Real.sin φ≤
      (outerAxial-1/2)-(outerDiagonal+1/2)*Real.cos φ := by
    linarith [(NegativeTwo.primary_mem hs).2]
  have hh := (le_div_iff₀ hp).2 hline
  dsimp [fourthCap]
  linarith

lemma fourth_late_lower {φ : ℝ} (hφ : φ∈Icc (6/5) (Real.pi/2)) : Lower φ :=
  ⟨six_fifths_lower.1.trans hφ.1,hφ.2⟩

lemma fourthCapFirst_lower {φ : ℝ} (hφ : φ∈Icc (6/5) (Real.pi/2)) :
    1<fourthCapFirst φ := by
  have hlo := fourth_late_lower hφ
  have ht := lower_trig hlo
  have hc := (lower_cos_antitone six_fifths_lower hlo hφ.1).trans_lt six_fifths_trig.2.2
  have ha : outerAxial-1/2<(183/200:ℝ) := by linarith [outer_endpoint_bounds.2.1]
  have hprod := mul_le_mul ha.le hc.le ht.2.2.1 (by norm_num : (0:ℝ)≤183/200)
  have hs : 0<Real.sin φ := by linarith [ht.1]
  have hsq : (Real.sin φ)^2≤1 := by nlinarith [ht.2.1]
  dsimp [fourthCapFirst]
  apply (lt_div_iff₀ (sq_pos_of_pos hs)).2
  nlinarith [fine_outer_endpoint_bounds.2]

lemma fourthScalar_antitone : AntitoneOn fourthScalar (Icc (6/5) (Real.pi/2)) := by
  have hd {φ : ℝ} (hφ : φ∈Icc (6/5) (Real.pi/2)) :
      HasDerivAt fourthScalar (1-(147/125)*fourthCapFirst φ) φ := by
    convert (((hasDerivAt_id' φ).add_const (V 0)).sub_const (793/20000)).sub
      ((fourthCap_hasDerivAt (fourth_late_lower hφ)).const_mul (147/125)) using 1
    funext t
    simp only [fourthScalar,Pi.sub_apply]
  exact antiOn_of_hasDeriv_nonpos
    (fun _ ht => (hd ht).continuousAt.continuousWithinAt)
    (fun _ ht => hd (Ioo_subset_Icc_self ht))
    (fun _ ht => by linarith [fourthCapFirst_lower (Ioo_subset_Icc_self ht)])

lemma fourthScalar_quarter : (51/50:ℝ)<fourthScalar (Real.pi/2) := by
  simp only [fourthScalar,fourthCap,Real.cos_pi_div_two,Real.sin_pi_div_two,
    mul_zero,sub_zero,div_one]
  linarith [pi_hand_enclosure.1,V_zero_bounds.1,outer_endpoint_bounds.2.1]

theorem original_lower_source_primary {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 φ) :
    (51/50:ℝ)<value b B φ := by
  have hangle := fourth_angle_lower hs ht hφ hm
  have hcap := fourth_target_cap hs ht hφ hm
  have hL := L_axial_line (NegativeTwo.source_mem ht)
  have hV := V_monotone outer_zero_mem (NegativeTwo.source_mem hs) hs.1
  have hstep := fourthScalar_antitone ⟨hangle.le,hφ.2⟩
    (show Real.pi/2∈Icc (6/5) (Real.pi/2) from ⟨six_fifths_lower.2,le_rfl⟩) hφ.2
  have hbase := fourthScalar_quarter.trans_le hstep
  dsimp [fourthScalar,value] at *
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree
end
end
end

section
/-!
## Original positive outer owner order below the quarter turn

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
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic

theorem original_upper_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 1 (Real.pi/2+x)) :
    (51/50:ℝ)<value b B (Real.pi/2+x) := by
  have hcut := upper_target_secondary_cut hx hm
  have htr := positive_trig hx
  have ha := NegativeTwo.primary_mem hs
  have hprod := mul_le_mul_of_nonneg_left htr.2.1
    (show 0≤a-1/2 by linarith [ha.1,fine_outer_endpoint_bounds.2])
  have hneg := mul_nonneg (show 0≤b+1/2 by linarith [hs.1]) htr.2.2.1
  have hB : B<(83/200:ℝ) := by linarith [ha.2,outer_endpoint_bounds.2.1]
  have hL := L_axial_line (NegativeTwo.source_mem ht)
  have hV := V_lower (NegativeTwo.source_mem hs)
  dsimp [value]
  linarith [pi_hand_enclosure.1,hx.1]

lemma upper_primary_small_target {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (11/100))
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 (Real.pi/2+x)) :
    B<(523/1000:ℝ) := by
  have hcap : x∈Icc 0 (7/10) := ⟨hx.1,by linarith [hx.2]⟩
  have hcut := upper_source_primary_cut hcap hm
  have htr := positive_trig hcap
  have ha := NegativeTwo.primary_mem hs
  have hA := NegativeTwo.primary_mem ht
  have hh : a-1/2<(57161/62500:ℝ) ∧ A-1/2<57161/62500 := by
    constructor <;> linarith [ha.2,hA.2,ShortOuterZero.fine_axial_bounds.2]
  have hc : (19879/20000:ℝ)≤Real.cos x := by
    have hbase := Real.one_sub_sq_div_two_le_cos (x := x)
    have hsq := pow_le_pow_left₀ hx.1 hx.2 2
    linarith
  have hprod := mul_le_mul hh.2.le
    (show Real.sin x≤11/100 from htr.2.2.2.2.1.trans hx.2)
    htr.2.2.1 (by norm_num : (0:ℝ)≤57161/62500)
  have hlow := mul_le_mul_of_nonneg_left hc
    (show 0≤B+1/2 by linarith [ht.1])
  linarith [hh.1]

theorem original_upper_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases he : x≤11/100
  · have hB := upper_primary_small_target hs ht ⟨hx.1,he⟩ hm
    have hL := L_axial_line (NegativeTwo.source_mem ht)
    have hV := V_lower (NegativeTwo.source_mem hs)
    dsimp [value]
    linarith [pi_hand_enclosure.1,hx.1]
  · have hh := late_angle hs ht
      (show (419/250:ℝ)≤Real.pi/2+x by linarith [pi_hand_enclosure.1])
    linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree
end
end
end
