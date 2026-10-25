module

public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeFirstContact
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeLowerFourth

/-!
# One quadratic support for the early positive contact

The short-source chord gives one target function.  Its quadratic
minorant at the single target `27/100` has a derivative containing only
two harmonics.  This file supplies the exact identities and all five
derivatives used in the whole-angle proof.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.Early

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

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.Early
