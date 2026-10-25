module

public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy

/-!
# Eight squares: whole-angle decrease of the single early-contact minorant

The fifth derivative is below six on the entire early interval.  One
quadratic Taylor bound at `1.085` makes the third derivative negative;
one square completion at `1.257` then makes the first derivative
negative everywhere.  The value at `1.3` supplies the global reserve.
-/

section
/-!
## One quadratic support for the early positive contact

The short-source chord gives one target function.  Its quadratic
minorant at the single target `27/100` has a derivative containing only
two harmonics.  This file supplies the exact identities and all five
derivatives used in the whole-angle proof.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.Early

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio ratioD ratioDD)

def g : ℝ := 49/50
def m : ℝ := 129/100
def star : ℝ := 27/100
def uStar : ℝ := U star
def rStar : ℝ := ratio star
def dStar : ℝ := LLabel.d1 star
def wStar : ℝ := 77/100

def support (B φ : ℝ) : ℝ :=
  φ-29/2000+g/2+g*Real.sin φ-L B-g*U B*Real.sin φ+g*W B*Real.cos φ
def targetFirst (B φ : ℝ) : ℝ :=
  g*(ratio B*Real.sin φ+Real.cos φ)-LLabel.d1 B
def targetSecond (B φ : ℝ) : ℝ := g*ratioD B*Real.sin φ-LLabel.d2 B
def targetThird (B φ : ℝ) : ℝ := g*ratioDD B*Real.sin φ-LLabel.d3 B

def minorant (φ : ℝ) : ℝ := support star φ-(targetFirst star φ)^2/(2*m)
def a1 : ℝ := -g*(uStar-1)+g*dStar*rStar/m
def b1 : ℝ := -g*wStar-g*dStar/m
def a2 : ℝ := g^2*(1-rStar^2)/(2*m)
def b2 : ℝ := -g^2*rStar/m
def first (φ : ℝ) : ℝ :=
  1+a1*Real.cos φ+b1*Real.sin φ+a2*Real.sin (2*φ)+b2*Real.cos (2*φ)
def second (φ : ℝ) : ℝ :=
  -a1*Real.sin φ+b1*Real.cos φ+2*a2*Real.cos (2*φ)-2*b2*Real.sin (2*φ)
def third (φ : ℝ) : ℝ :=
  -a1*Real.cos φ-b1*Real.sin φ-4*a2*Real.sin (2*φ)-4*b2*Real.cos (2*φ)
def fourth (φ : ℝ) : ℝ :=
  a1*Real.sin φ-b1*Real.cos φ-8*a2*Real.cos (2*φ)+8*b2*Real.sin (2*φ)
def fifth (φ : ℝ) : ℝ :=
  a1*Real.cos φ+b1*Real.sin φ+16*a2*Real.sin (2*φ)+16*b2*Real.cos (2*φ)

lemma star_mem : star∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num [star])

lemma early_lower {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) : Lower φ :=
  ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩

lemma support_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (φ : ℝ) :
    HasDerivAt (fun t => support t φ) (targetFirst B φ) B := by
  have hd := ((((LLabel.outer_hasDerivAt (outer_domain hB)).neg).add_const
    (φ-29/2000+g/2+g*Real.sin φ)).sub
      ((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add_const
        (1/2)).const_mul g).mul_const (Real.sin φ))).add
      ((((hasDerivAt_id' B).add_const (1/2)).const_mul g).mul_const (Real.cos φ))
  convert hd using 1
  · funext t
    simp only [support,L,U,W,Pi.add_apply,Pi.sub_apply,Pi.neg_apply]
    ring
  · dsimp only [targetFirst]
    ring

lemma targetFirst_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (φ : ℝ) :
    HasDerivAt (fun t => targetFirst t φ) (targetSecond B φ) B := by
  have hd := ((((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).mul_const
    (Real.sin φ)).add_const (Real.cos φ)).const_mul g).sub
      (LLabel.d1_hasDerivAt (outer_domain hB))
  convert hd using 1
  · funext t
    simp only [targetFirst,Pi.sub_apply]
  · dsimp only [targetSecond]
    ring

lemma targetSecond_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (φ : ℝ) :
    HasDerivAt (fun t => targetSecond t φ) (targetThird B φ) B := by
  have hd := (((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hB)).const_mul
    g).mul_const (Real.sin φ)).sub (LLabel.d2_hasDerivAt (outer_domain hB))
  convert hd using 1
  · funext t
    simp only [targetSecond,Pi.sub_apply]
  · dsimp only [targetThird]

lemma targetThird_negative {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) (hφ : Lower φ) :
    targetThird B φ<0 := by
  have ht := lower_trig hφ
  have hD := (outer_ratio_bounds hB).2.2.1
  have hDD := ratioDD_positive hB
  have hprod := mul_le_mul_of_nonneg_left ht.2.1 hDD.le
  have hcomp := outer_ratioDD_comparison hB
  have hBprod := mul_nonneg hB.1 hDD.le
  have hL : (284163/50000)*ratioD B≤LLabel.d3 B := by
    norm_num [RoleLabel.d3,LLabel]
    nlinarith
  dsimp [targetThird,g]
  nlinarith

lemma original_short_support {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ) (hb : b≤7/20)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    support B φ<value b B φ := by
  have hcut := FirstContact.original_cut ht hφ hm
  have hsource := V_chord_short (show b∈Icc (0:ℝ) (7/20) from ⟨hs.1,hb⟩)
  have hzero := V_zero_bounds.1
  dsimp [FirstContact.source,support,value,g] at *
  linarith

lemma double_cos (φ : ℝ) : Real.cos (2*φ)=(Real.cos φ)^2-(Real.sin φ)^2 := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq φ]

lemma support_angle_hasDerivAt (φ : ℝ) :
    HasDerivAt (support star)
      (1+g*(1-uStar)*Real.cos φ-g*wStar*Real.sin φ) φ := by
  have hd := ((((((hasDerivAt_id' φ).sub_const (29/2000)).add_const (g/2)).add
    ((Real.hasDerivAt_sin φ).const_mul g)).sub_const (L star)).sub
      ((Real.hasDerivAt_sin φ).const_mul (g*uStar))).add
        ((Real.hasDerivAt_cos φ).const_mul (g*wStar))
  convert hd using 1
  · funext t
    simp only [support,uStar,wStar,W,star,Pi.add_apply,Pi.sub_apply]
    ring
  · ring

lemma targetFirst_angle_hasDerivAt (φ : ℝ) :
    HasDerivAt (targetFirst star) (g*(rStar*Real.cos φ-Real.sin φ)) φ := by
  have hd := ((((Real.hasDerivAt_sin φ).const_mul rStar).add
    (Real.hasDerivAt_cos φ)).const_mul g).sub_const dStar
  convert hd using 1
  · funext t
    simp only [targetFirst,rStar,dStar,Pi.add_apply]

lemma minorant_hasDerivAt (φ : ℝ) : HasDerivAt minorant (first φ) φ := by
  have hd := (support_angle_hasDerivAt φ).sub
    (((targetFirst_angle_hasDerivAt φ).pow 2).div_const (2*m))
  convert hd using 1
  · rfl
  · dsimp [first,a1,b1,a2,b2,targetFirst,rStar,dStar]
    rw [Real.sin_two_mul,double_cos]
    field_simp [show m≠0 by norm_num [m]]
    ring

private lemma sin_two_hasDerivAt (φ : ℝ) :
    HasDerivAt (fun x => Real.sin (2*x)) (Real.cos (2*φ)*(2*1)) φ :=
  (Real.hasDerivAt_sin (2*φ)).comp φ ((hasDerivAt_id' φ).const_mul 2)

private lemma cos_two_hasDerivAt (φ : ℝ) :
    HasDerivAt (fun x => Real.cos (2*x)) (-Real.sin (2*φ)*(2*1)) φ :=
  (Real.hasDerivAt_cos (2*φ)).comp φ ((hasDerivAt_id' φ).const_mul 2)

lemma first_hasDerivAt (φ : ℝ) : HasDerivAt first (second φ) φ := by
  have hs := sin_two_hasDerivAt φ
  have hc := cos_two_hasDerivAt φ
  have hd := (((((Real.hasDerivAt_cos φ).const_mul a1).const_add 1).add
    ((Real.hasDerivAt_sin φ).const_mul b1)).add (hs.const_mul a2)).add
      (hc.const_mul b2)
  convert hd using 1
  · funext t
    simp only [first,Pi.add_apply]
  · dsimp only [second]
    ring

lemma second_hasDerivAt (φ : ℝ) : HasDerivAt second (third φ) φ := by
  have hs := sin_two_hasDerivAt φ
  have hc := cos_two_hasDerivAt φ
  have hd := (((((Real.hasDerivAt_sin φ).const_mul (-a1)).add
    ((Real.hasDerivAt_cos φ).const_mul b1)).add (hc.const_mul (2*a2))).sub
      (hs.const_mul (2*b2)))
  convert hd using 1
  · funext t
    simp only [second,Pi.add_apply,Pi.sub_apply]
  · dsimp only [third]
    ring

lemma third_hasDerivAt (φ : ℝ) : HasDerivAt third (fourth φ) φ := by
  have hs := sin_two_hasDerivAt φ
  have hc := cos_two_hasDerivAt φ
  have hd := (((((Real.hasDerivAt_cos φ).const_mul (-a1)).sub
    ((Real.hasDerivAt_sin φ).const_mul b1)).sub (hs.const_mul (4*a2))).sub
      (hc.const_mul (4*b2)))
  convert hd using 1
  · funext t
    simp only [third,Pi.sub_apply]
  · dsimp only [fourth]
    ring

lemma fourth_hasDerivAt (φ : ℝ) : HasDerivAt fourth (fifth φ) φ := by
  have hs := sin_two_hasDerivAt φ
  have hc := cos_two_hasDerivAt φ
  have hd := (((((Real.hasDerivAt_sin φ).const_mul a1).sub
    ((Real.hasDerivAt_cos φ).const_mul b1)).sub (hc.const_mul (8*a2))).add
      (hs.const_mul (8*b2)))
  convert hd using 1
  · funext t
    simp only [fourth,Pi.add_apply,Pi.sub_apply]
  · dsimp only [fifth]
    ring

end SquaresInCircles.Eight.SecondWord.PositiveThree.Early
end
end
end

section
/-!
## Exact coefficients of the single early-angle minorant

At target `27/100`, the physical radical has square `33227/10000`.
The first harmonic is affine in that radical or its reciprocal; the
second harmonic has one rational coefficient and one reciprocal
coefficient.  Thus one integer-square bracket proves every bound here.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.Early

open CommonQuarter CorePairGeometry Arithmetic

def qStar : ℝ := 33227/10000
def firstA : ℝ := 9984177/2500000
def firstC : ℝ := -737592427/125000000

lemma uStar_bounds :
    (182282747400844/100000000000000:ℝ)<uStar ∧
      uStar<182282747400845/100000000000000 := by
  exact shifted_chart_reference (outer_domain star_mem)
    (by norm_num) (by norm_num) (by norm_num [star,W,Q0]) (by norm_num [star,W,Q0])

lemma uStar_positive : 0<uStar := U_positive (outer_domain star_mem)

lemma uStar_sq : uStar^2=qStar := by
  have hh := UW_circle (outer_domain star_mem)
  norm_num [star,W,Q0] at hh
  dsimp [uStar,qStar,star]
  linarith

lemma rStar_times_u : rStar*uStar=wStar := by
  change W star/U star*U star=wStar
  rw [div_mul_cancel₀ _ (show U star≠0 from uStar_positive.ne')]
  norm_num [W,star,wStar]

lemma dStar_times_u : dStar*uStar=firstA*uStar+firstC := by
  have hh := LLabel.first_numerator (outer_domain star_mem)
  dsimp only [dStar,uStar]
  rw [hh]
  simp only [LLabel,star,W,Q0,firstA,firstC]
  ring

lemma a1_affine :
    a1=(-g+g*wStar*firstA/(m*qStar))*uStar+
      (g+g*wStar*firstC/(m*qStar)) := by
  have hq : qStar≠0 := by norm_num [qStar]
  have hp : dStar*rStar=wStar*(firstA*uStar+firstC)/qStar := by
    apply (eq_div_iff hq).2
    calc
      dStar*rStar*qStar=(dStar*uStar)*(rStar*uStar) := by rw [←uStar_sq]; ring
      _=(firstA*uStar+firstC)*wStar := by rw [dStar_times_u,rStar_times_u]
      _=wStar*(firstA*uStar+firstC) := by ring
  dsimp [a1]
  rw [show g*dStar*rStar/m=g*(dStar*rStar)/m by ring,hp]
  field_simp [hq,show m≠0 by norm_num [m]]
  ring

lemma b1_times_u : b1*uStar=(-g*wStar-g*firstA/m)*uStar-g*firstC/m := by
  dsimp [b1]
  linear_combination (-g/m)*dStar_times_u

lemma a2_rational : a2=g^2*(qStar-wStar^2)/(2*m*qStar) := by
  have hq : qStar≠0 := by norm_num [qStar]
  have hr : rStar^2=wStar^2/qStar := by
    apply (eq_div_iff hq).2
    calc
      rStar^2*qStar=(rStar*uStar)^2 := by rw [←uStar_sq]; ring
      _=wStar^2 := by rw [rStar_times_u]
  dsimp [a2]
  rw [hr]
  field_simp [hq,show m≠0 by norm_num [m]]

lemma b2_times_u : b2*uStar= -g^2*wStar/m := by
  dsimp [b2]
  linear_combination (-g^2/m)*rStar_times_u

lemma a1_bounds :
    (-563592126648/1000000000000:ℝ)<a1 ∧ a1< -563592126647/1000000000000 := by
  rw [a1_affine]
  norm_num [g,m,wStar,firstA,firstC,qStar]
  constructor <;> linarith [uStar_bounds.1,uStar_bounds.2]

lemma b1_bounds :
    (-1329332289459/1000000000000:ℝ)<b1 ∧ b1< -1329332289458/1000000000000 := by
  have he := b1_times_u
  norm_num [g,m,wStar,firstA,firstC] at he
  have hl : (-1329332289459/1000000000000:ℝ)*uStar<b1*uStar := by
    nlinarith [uStar_bounds.1,uStar_bounds.2]
  have hh : b1*uStar<(-1329332289458/1000000000000:ℝ)*uStar := by
    nlinarith [uStar_bounds.1,uStar_bounds.2]
  constructor
  · by_contra h
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt h) uStar_positive.le
    linarith
  · by_contra h
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt h) uStar_positive.le
    linarith

lemma a2_bounds :
    (305824407767/1000000000000:ℝ)<a2 ∧ a2<305824407768/1000000000000 := by
  rw [a2_rational]
  norm_num [g,m,qStar,wStar]

lemma b2_bounds :
    (-314490550356/1000000000000:ℝ)<b2 ∧ b2< -314490550355/1000000000000 := by
  have he := b2_times_u
  norm_num [g,m,wStar] at he
  have hl : (-314490550356/1000000000000:ℝ)*uStar<b2*uStar := by
    nlinarith [uStar_bounds.1,uStar_bounds.2]
  have hh : b2*uStar<(-314490550355/1000000000000:ℝ)*uStar := by
    nlinarith [uStar_bounds.1,uStar_bounds.2]
  constructor
  · by_contra h
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt h) uStar_positive.le
    linarith
  · by_contra h
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt h) uStar_positive.le
    linarith

lemma rStar_bounds :
    (422420668428/1000000000000:ℝ)<rStar ∧ rStar<422420668429/1000000000000 := by
  have he := rStar_times_u
  norm_num [wStar] at he
  have hl : (422420668428/1000000000000:ℝ)*uStar<rStar*uStar := by
    nlinarith [uStar_bounds.1,uStar_bounds.2]
  have hh : rStar*uStar<(422420668429/1000000000000:ℝ)*uStar := by
    nlinarith [uStar_bounds.1,uStar_bounds.2]
  constructor
  · by_contra h
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt h) uStar_positive.le
    linarith
  · by_contra h
    have hp := mul_le_mul_of_nonneg_right (le_of_not_gt h) uStar_positive.le
    linarith

lemma star_labels :
    (294743185706/1000000000000:ℝ)<L star ∧ L star<294743185707/1000000000000 ∧
    (756535360613/1000000000000:ℝ)<dStar ∧ dStar<756535360614/1000000000000 := by
  have hh := LReference.target star_mem
    (show star∈Icc (27/100) (27/100) by norm_num [star])
    ⟨uStar_bounds.1.le,uStar_bounds.2.le⟩ (by norm_num) (by norm_num)
  norm_num [LReference.valueLo,LReference.valueHi,LReference.firstLo,
    LReference.firstHi,LReference.secondLo,LReference.secondHi,Q0] at hh
  dsimp [dStar]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

end SquaresInCircles.Eight.SecondWord.PositiveThree.Early
end
end
end

section
/-!
## Three fixed references for the early-angle support

Only the angles `1.085`, `1.257` and `1.3` occur.  The first two control
the curvature and slope of one analytic minorant; the last is its
endpoint value.  The slightly weakened reserves leave ample room for
the uniform curvature argument.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.Early

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig

lemma coefficient_boxes :
    a1∈Icc (-563592126648/1000000000000) (-563592126647/1000000000000) ∧
    b1∈Icc (-1329332289459/1000000000000) (-1329332289458/1000000000000) ∧
    a2∈Icc (305824407767/1000000000000) (305824407768/1000000000000) ∧
    b2∈Icc (-314490550356/1000000000000) (-314490550355/1000000000000) :=
  ⟨⟨a1_bounds.1.le,a1_bounds.2.le⟩,⟨b1_bounds.1.le,b1_bounds.2.le⟩,
    ⟨a2_bounds.1.le,a2_bounds.2.le⟩,⟨b2_bounds.1.le,b2_bounds.2.le⟩⟩

lemma third_reference : third (217/200)<(-7/25:ℝ) ∧
    |fourth (217/200)|<29/50 := by
  have h := coefficient_boxes
  have ht := PointProducts.trig (show (0:ℝ)≤217/200 by norm_num)
  have htwo := PointProducts.trig (show (0:ℝ)≤217/100 by norm_num)
  have p1 := PointProducts.product h.1 ht.2
  have p2 := PointProducts.product h.2.1 ht.1
  have p3 := PointProducts.product h.2.2.1 htwo.1
  have p4 := PointProducts.product h.2.2.2 htwo.2
  have q1 := PointProducts.product h.1 ht.1
  have q2 := PointProducts.product h.2.1 ht.2
  have q3 := PointProducts.product h.2.2.1 htwo.2
  have q4 := PointProducts.product h.2.2.2 htwo.1
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at p1 p2 p3 p4 q1 q2 q3 q4
  dsimp [third,fourth]
  rw [show (2:ℝ)*(217/200)=217/100 by norm_num]
  constructor
  · linarith [p1.1,p1.2,p2.1,p2.2,p3.1,p3.2,p4.1,p4.2]
  · rw [abs_lt]
    constructor <;> linarith [q1.1,q1.2,q2.1,q2.2,q3.1,q3.2,q4.1,q4.2]

lemma first_reference : first (1257/1000)<(-39/10000:ℝ) ∧
    |second (1257/1000)|<1/1000 := by
  have h := coefficient_boxes
  have ht := PointProducts.trig (show (0:ℝ)≤1257/1000 by norm_num)
  have htwo := PointProducts.trig (show (0:ℝ)≤1257/500 by norm_num)
  have p1 := PointProducts.product h.1 ht.2
  have p2 := PointProducts.product h.2.1 ht.1
  have p3 := PointProducts.product h.2.2.1 htwo.1
  have p4 := PointProducts.product h.2.2.2 htwo.2
  have q1 := PointProducts.product h.1 ht.1
  have q2 := PointProducts.product h.2.1 ht.2
  have q3 := PointProducts.product h.2.2.1 htwo.2
  have q4 := PointProducts.product h.2.2.2 htwo.1
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at p1 p2 p3 p4 q1 q2 q3 q4
  dsimp [first,second]
  rw [show (2:ℝ)*(1257/1000)=1257/500 by norm_num]
  constructor
  · linarith [p1.1,p1.2,p2.1,p2.2,p3.1,p3.2,p4.1,p4.2]
  · rw [abs_lt]
    constructor <;> linarith [q1.1,q1.2,q2.1,q2.2,q3.1,q3.2,q4.1,q4.2]

lemma end_support : (566/625:ℝ)<support star (13/10) ∧
    |targetFirst star (13/10)|<12/125 := by
  have ht := PointProducts.trig (show (0:ℝ)≤13/10 by norm_num)
  have hu := PointProducts.product ⟨uStar_bounds.1.le,uStar_bounds.2.le⟩ ht.1
  have hr := PointProducts.product ⟨rStar_bounds.1.le,rStar_bounds.2.le⟩ ht.1
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at ht hu hr
  have he : support star (13/10)=13/10-29/2000+g/2+g*Real.sin (13/10)-
      L star-g*uStar*Real.sin (13/10)+g*wStar*Real.cos (13/10) := by
    dsimp [support,uStar,wStar,W,star]
    ring
  have hd : targetFirst star (13/10)=
      g*(rStar*Real.sin (13/10)+Real.cos (13/10))-dStar := rfl
  rw [he,hd]
  norm_num [g,wStar]
  constructor
  · linarith [ht.1.1,ht.1.2,ht.2.1,ht.2.2,hu.1,hu.2,star_labels.1,star_labels.2.1]
  · rw [abs_lt]
    constructor <;> linarith [ht.2.1,ht.2.2,hr.1,hr.2,star_labels.2.2.1,star_labels.2.2.2]

lemma minorant_end : (451/500:ℝ)< minorant (13/10) := by
  have hb := abs_lt.mp end_support.2
  have hs : (targetFirst star (13/10))^2<(12/125:ℝ)^2 := by nlinarith
  have hq : (targetFirst star (13/10))^2/(2*m)<(12/125:ℝ)^2/(2*m) :=
    div_lt_div_of_pos_right hs (by norm_num [m])
  dsimp only [minorant]
  norm_num [m] at hq ⊢
  linarith [end_support.1]

lemma end_cos_lower : (267/1000:ℝ)<Real.cos (13/10) := by
  have hh := cos10_le_cos (show (0:ℝ)≤13/10 by norm_num)
  norm_num [cos10,cos8] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.Early
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.Early

open CommonQuarter CorePairGeometry Arithmetic

lemma end_mem : (13/10:ℝ)∈Icc lowerAngle (13/10) := by
  constructor
  · dsimp [lowerAngle]
    linarith [pi_hand_enclosure.2]
  · rfl

lemma first_harmonic_upper {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) :
    a1*Real.cos φ+b1*Real.sin φ<(-11/10:ℝ) := by
  have ht := lower_trig (early_lower hφ)
  have hc := end_cos_lower.trans_le
    (lower_cos_antitone (early_lower hφ) (early_lower end_mem) hφ.2)
  have ha := mul_nonneg
    (show 0≤-(11/20:ℝ)-a1 by linarith [a1_bounds.2]) ht.2.2.1
  have hb := mul_nonneg
    (show 0≤-(33/25:ℝ)-b1 by linarith [b1_bounds.2])
    (show 0≤Real.sin φ by linarith [ht.1])
  nlinarith [ht.1]

lemma harmonic_norm : a2^2+b2^2<(11/25:ℝ)^2 := by
  have ha : 0<a2 ∧ a2<153/500 := by
    constructor <;> linarith [a2_bounds.1,a2_bounds.2]
  have hb : (-63/200:ℝ)<b2 ∧ b2<0 := by
    constructor <;> linarith [b2_bounds.1,b2_bounds.2]
  have hsa := mul_pos (show 0<(153/500:ℝ)-a2 by linarith)
    (show 0<(153/500:ℝ)+a2 by linarith)
  have hsb := mul_pos (show 0<(63/200:ℝ)-b2 by linarith)
    (show 0<(63/200:ℝ)+b2 by linarith)
  nlinarith

lemma second_harmonic_upper (φ : ℝ) :
    a2*Real.sin (2*φ)+b2*Real.cos (2*φ)<(11/25:ℝ) := by
  have he : (a2*Real.sin (2*φ)+b2*Real.cos (2*φ))^2+
      (a2*Real.cos (2*φ)-b2*Real.sin (2*φ))^2=a2^2+b2^2 := by
    linear_combination (a2^2+b2^2)*(Real.sin_sq_add_cos_sq (2*φ))
  by_contra hh
  have hlo : (11/25:ℝ)≤a2*Real.sin (2*φ)+b2*Real.cos (2*φ) := by linarith
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤11/25) hlo 2
  nlinarith [harmonic_norm,sq_nonneg (a2*Real.cos (2*φ)-b2*Real.sin (2*φ))]

lemma fifth_upper {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) : fifth φ<6 := by
  have h1 := first_harmonic_upper hφ
  have h2 := second_harmonic_upper φ
  dsimp [fifth]
  linarith

lemma third_reference_mem : (217/200:ℝ)∈Icc lowerAngle (13/10) := by
  constructor
  · dsimp [lowerAngle]
    linarith [pi_hand_enclosure.2]
  · norm_num

lemma first_reference_mem : (1257/1000:ℝ)∈Icc lowerAngle (13/10) := by
  constructor
  · dsimp [lowerAngle]
    linarith [pi_hand_enclosure.2]
  · norm_num

lemma third_upper {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) :
    third φ<(-2/125:ℝ) := by
  have hh := curvature_tangent (f := fun t => -third t)
    (d := fun t => -fourth t) (dd := fun t => -fifth t) (κ := (-6:ℝ))
    hφ third_reference_mem
    (fun t _ => (third_hasDerivAt t).neg)
    (fun t _ => (fourth_hasDerivAt t).neg)
    (fun t ht => by linarith [fifth_upper ht])
  have hdist : |φ-217/200|≤(43/200:ℝ) := by
    rw [abs_le]
    dsimp [lowerAngle] at hφ
    constructor <;> linarith [hφ.1,hφ.2,pi_hand_enclosure.1]
  have hproduct : fourth (217/200)*(φ-217/200)≤(29/50:ℝ)*(43/200) := by
    calc
      _≤|fourth (217/200)*(φ-217/200)| := le_abs_self _
      _=|fourth (217/200)| *|φ-217/200| := abs_mul _ _
      _≤(29/50:ℝ)*(43/200) := mul_le_mul third_reference.2.le hdist
        (abs_nonneg _) (by norm_num)
  have hd := abs_le.mp hdist
  have hs := mul_nonneg (show 0≤43/200-(φ-217/200) by linarith [hd.2])
    (show 0≤43/200+(φ-217/200) by linarith [hd.1])
  nlinarith [third_reference.1]

lemma first_negative {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) : first φ<0 := by
  have hh := curvature_tangent (f := fun t => -first t)
    (d := fun t => -second t) (dd := fun t => -third t) (κ := (2/125:ℝ))
    hφ first_reference_mem
    (fun t _ => (first_hasDerivAt t).neg)
    (fun t _ => (second_hasDerivAt t).neg)
    (fun t ht => by linarith [third_upper ht])
  have hd := abs_lt.mp first_reference.2
  have hs : (second (1257/1000))^2<(1/1000:ℝ)^2 := by nlinarith
  nlinarith [first_reference.1,
    sq_nonneg ((2/125)*(φ-1257/1000)-second (1257/1000))]

lemma minorant_antitone : AntitoneOn minorant (Icc lowerAngle (13/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun t _ => (minorant_hasDerivAt t).continuousAt.continuousWithinAt)
    (fun t _ => minorant_hasDerivAt t)
    (fun _ ht => (first_negative (Ioo_subset_Icc_self ht)).le)

theorem minorant_lower {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) :
    (451/500:ℝ)< minorant φ :=
  minorant_end.trans_le (minorant_antitone hφ end_mem hφ.2)

end SquaresInCircles.Eight.SecondWord.PositiveThree.Early
end
end
end
