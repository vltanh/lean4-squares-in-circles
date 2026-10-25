module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import SquaresInCircles.Eight.Words.Common.OneSecondary
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData

/-!
# Eight squares: the actual diagonal boundary for the lower source-primary owner

The target circle is rotated against a diagonal source.  The resulting
target coordinate increases, with strictly decreasing positive speed.
All identities below use the original circle at `Q0`.
-/

section
/-!
## The explicit inverse of the original circle contact

The inverse is an arctangent followed by an arcsine on a strictly
positive physical radical.  Its original-angle identity includes weak
contact endpoints.  Both derivatives are proved from this formula,
without an implicit minimizer or a chosen contact branch as a premise.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.ContactInverse

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def radius (b : ℝ) : ℝ := Real.sqrt (Inverse.q (U b))
def speed (z b : ℝ) : ℝ := Real.sqrt (Inverse.q (U b)-z^2)
def baseAngle (b : ℝ) : ℝ := Real.arctan ((U b-1)/W b)
def angle (z b : ℝ) : ℝ := baseAngle b+Real.arcsin (z/radius b)
def first (z b : ℝ) : ℝ :=
  -Inverse.factor (U b)-z*ratio b/(Inverse.q (U b)*speed z b)
def second (z b : ℝ) : ℝ :=
  -PJCritical.inverseTarget (U b) (ratio b) z (speed z b)

lemma data {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    0<U b ∧ 0<W b ∧ 1<radius b ∧ (radius b)^2=Inverse.q (U b) ∧
      0<speed z b ∧ z^2+(speed z b)^2=Inverse.q (U b) := by
  have hq := Inverse.actual_q_positive hb
  have hq0 : 0<Inverse.q (U b) := by linarith
  have hzsq : z^2≤(1/4:ℝ) := by nlinarith [hz.1,hz.2]
  have hrad : 0<Inverse.q (U b)-z^2 := by linarith
  have hr := Real.sqrt_nonneg (Inverse.q (U b))
  have hr2 := Real.sq_sqrt hq0.le
  have hv := Real.sqrt_pos.mpr hrad
  have hv2 := Real.sq_sqrt hrad.le
  refine ⟨U_positive (outer_domain hb),by dsimp [W]; linarith [hb.1],
    ?_,hr2,hv,?_⟩
  · dsimp [radius]
    nlinarith
  · dsimp [speed]
    linarith

lemma radius_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt radius (ratio b/radius b) b := by
  have hq0 := Inverse.actual_q_positive hb
  have hq : Inverse.q (U b)≠0 := by linarith
  have hr : 0<Real.sqrt (Inverse.q (U b)) := Real.sqrt_pos.2 (by linarith)
  have hU : HasDerivAt U (-ratio b) b :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hd := ((Inverse.q_hasDerivAt (U b)).comp b hU).sqrt hq
  refine hd.congr_deriv ?_
  simp only [Function.comp_apply,radius]
  rw [div_eq_div_iff (mul_pos two_pos hr).ne' hr.ne']
  ring

lemma speed_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    HasDerivAt (speed z) (ratio b/speed z b) b := by
  have hd := data hb hz
  have hrad : Inverse.q (U b)-z^2≠0 := by
    nlinarith [sq_pos_of_pos hd.2.2.2.2.1,hd.2.2.2.2.2]
  have hv : 0<Real.sqrt (Inverse.q (U b)-z^2) := hd.2.2.2.2.1
  have hU : HasDerivAt U (-ratio b) b :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hder := (((Inverse.q_hasDerivAt (U b)).comp b hU).sub_const (z^2)).sqrt hrad
  refine hder.congr_deriv ?_
  simp only [Function.comp_apply,speed]
  rw [div_eq_div_iff (mul_pos two_pos hv).ne' hv.ne']
  ring

lemma base_circle {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (U b-1)^2+(W b)^2=Inverse.q (U b) := by
  have hh := UW_circle (outer_domain hb)
  dsimp [Inverse.q]
  nlinarith

lemma base_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0≤baseAngle b ∧ baseAngle b<Real.pi/2 := by
  have hu := UW_bounds hb
  refine ⟨?_,Real.arctan_lt_pi_div_two _⟩
  exact (Real.arctan_pos.mpr (div_pos (by linarith [hu.1])
    (by linarith [hu.2.2.1]))).le

lemma base_trig {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    Real.cos (baseAngle b)=W b/radius b ∧
      Real.sin (baseAngle b)=(U b-1)/radius b := by
  have hu := UW_bounds hb
  have hh := arctan_polar_coordinates
    (a := W b) (b := U b-1) (σ := (1:ℝ))
    (by linarith [hu.2.2.1]) (Or.inr rfl)
  have he : (W b)^2+(U b-1)^2=Inverse.q (U b) := by
    linarith [base_circle hb]
  simpa only [one_mul,he,radius,baseAngle] using hh

lemma base_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt baseAngle (-Inverse.factor (U b)) b := by
  have hu := U_positive (outer_domain hb)
  have hw : 0<W b := by dsimp [W]; linarith [hb.1]
  have hq : Inverse.q (U b)≠0 := by linarith [Inverse.actual_q_positive hb]
  have hc := UW_circle (outer_domain hb)
  have hbc := base_circle hb
  have hU : HasDerivAt U (-ratio b) b :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hW : HasDerivAt W 1 b := (hasDerivAt_id' b).add_const (1/2)
  have hinner := (hU.sub_const 1).div hW hw.ne'
  have hd := (Real.hasDerivAt_arctan ((U b-1)/W b)).comp b hinner
  refine hd.congr_deriv ?_
  have hratio : ratio b=W b/U b := rfl
  have hden : 1+((U b-1)/W b)^2=Inverse.q (U b)/(W b)^2 := by
    rw [← hbc]
    field_simp
    ring
  rw [hden,hratio]
  simp only [Inverse.factor]
  rw [← hc]
  field_simp
  ring

lemma argument_bounds {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    -1<z/radius b ∧ z/radius b<1 := by
  have hr := (data hb hz).2.2.1
  have hp : 0<radius b := by linarith
  constructor
  · apply (lt_div_iff₀ hp).2
    linarith [hz.1]
  · apply (div_lt_iff₀ hp).2
    linarith [hz.2]

lemma inverse_root {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    Real.sqrt (1-(z/radius b)^2)=speed z b/radius b := by
  have hd := data hb hz
  have hr : 0<radius b := by linarith [hd.2.2.1]
  have he : 1-(z/radius b)^2=(speed z b/radius b)^2 := by
    field_simp [hr.ne']
    nlinarith [hd.2.2.2.1,hd.2.2.2.2.2]
  rw [he,Real.sqrt_sq (div_nonneg hd.2.2.2.2.1.le hr.le)]

lemma angle_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    HasDerivAt (angle z) (first z b) b := by
  have hd := data hb hz
  have hr : 0<radius b := by linarith [hd.2.2.1]
  have hv := hd.2.2.2.2.1
  have ha := argument_bounds hb hz
  have hinner : HasDerivAt (fun y => z/radius y) (-(z*(ratio b/radius b))/(radius b)^2) b :=
    ((hasDerivAt_const b z).div (radius_hasDerivAt hb) hr.ne').congr_deriv (by ring)
  have hasin := (Real.hasDerivAt_arcsin
    (by linarith : z/radius b≠-1) (by linarith : z/radius b≠1)).comp b hinner
  have hder : HasDerivAt (fun y => Real.arcsin (z/radius y))
      (-z*ratio b/(Inverse.q (U b)*speed z b)) b := by
    refine hasin.congr_deriv ?_
    rw [inverse_root hb hz,←hd.2.2.2.1]
    field_simp
  exact ((base_hasDerivAt hb).add hder).congr_deriv (by simp only [first]; ring)

lemma first_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    HasDerivAt (first z) (second z b) b := by
  have hd := data hb hz
  have hu := hd.1
  have hv := hd.2.2.2.2.1
  have hq : Inverse.q (U b)≠0 := by linarith [Inverse.actual_q_positive hb]
  have huD : HasDerivAt U (-ratio b) b :=
    (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hf := (Inverse.factor_hasDerivAt hu.ne' hq).comp b huD
  have hden := ((Inverse.q_hasDerivAt (U b)).comp b huD).mul (speed_hasDerivAt hb hz)
  have hnum := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul z
  have hder := hf.neg.sub (hnum.div hden (mul_ne_zero hq hv.ne'))
  refine hder.congr_deriv ?_
  have hrD : ratioD b=Q0/(U b)^3 := rfl
  simp only [second,PJCritical.inverseTarget,PJCritical.heightFactorD,Inverse.brace,
    Function.comp_apply,Pi.mul_apply]
  rw [hrD]
  field_simp
  ring

lemma contact {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    TargetContact.B b (angle z b)=z+1/2 ∧
      TargetContact.v b (angle z b)=speed z b := by
  have hd := data hb hz
  have hr : 0<radius b := by linarith [hd.2.2.1]
  have ha := argument_bounds hb hz
  have ht := base_trig hb
  have hs := Real.sin_arcsin ha.1.le ha.2.le
  have hc := Real.cos_arcsin (z/radius b)
  rw [inverse_root hb hz] at hc
  have hn : (U b-1)^2+(W b)^2=(radius b)^2 := by
    rw [hd.2.2.2.1]
    exact base_circle hb
  have hn0 : (U b-1)^2+(W b)^2≠0 := by rw [hn]; positivity
  have hcos : Real.cos (angle z b)=(W b*speed z b-(U b-1)*z)/(radius b)^2 := by
    rw [angle,Real.cos_add,ht.1,ht.2,hs,hc]
    field_simp
  have hsin : Real.sin (angle z b)=((U b-1)*speed z b+W b*z)/(radius b)^2 := by
    rw [angle,Real.sin_add,ht.1,ht.2,hs,hc]
    field_simp
  rw [← hn] at hcos hsin
  have hB : TargetContact.B b (angle z b)=
      1/2-(U b-1)*Real.cos (angle z b)+W b*Real.sin (angle z b) := by
    simp only [TargetContact.B,U,W]
    ring
  have hV : TargetContact.v b (angle z b)=
      (U b-1)*Real.sin (angle z b)+W b*Real.cos (angle z b) := by
    simp only [TargetContact.v,U,W]
    ring
  rw [hB,hV,hcos,hsin]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- The inverse formula recovers the actual physical angle, including
contacts with zero or diagonal target transverse coordinate. -/
lemma original_angle {b x : ℝ} (hd : TargetContact.Domain b x) :
    angle (TargetContact.B b x-1/2) b=x := by
  have hb := hd.1
  have hx := hd.2.1
  have hzero := data hb (show (0:ℝ)∈Icc (-(1/2)) (2/5) by norm_num)
  have hr : 0<radius b := by linarith [hzero.2.2.1]
  have ht := base_trig hb
  have ha := base_bounds hb
  have hy : -(Real.pi/2)≤x-baseAngle b ∧ x-baseAngle b≤Real.pi/2 := by
    constructor <;> linarith [hx.1,hx.2,ha.1,ha.2,Real.pi_gt_three]
  have he : (TargetContact.B b x-1/2)/radius b=
      Real.sin (x-baseAngle b) := by
    rw [Real.sin_sub,ht.1,ht.2]
    dsimp [TargetContact.B,U,W]
    field_simp [hr.ne']
    ring
  dsimp [angle]
  rw [he,Real.arcsin_sin hy.1 hy.2]
  ring

end SquaresInCircles.Eight.SecondWord.NegativeTwo.ContactInverse
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.PrimaryDiagonal

open CommonQuarter CorePairGeometry Arithmetic

def offset : ℝ := 1/2-outerDiagonal
def Z (x : ℝ) : ℝ := Real.cos x+offset
def Y (x : ℝ) : ℝ := Real.sqrt (Q0-(Z x)^2)
def horizontal (x : ℝ) : ℝ := Y x*Real.cos x-Z x*Real.sin x
def vertical (x : ℝ) : ℝ := Y x*Real.sin x+Z x*Real.cos x
def height (x : ℝ) : ℝ := vertical x-1/2
def factor (x : ℝ) : ℝ := 1-Real.sin x/Y x
def factorD (x : ℝ) : ℝ :=
  (Z x*(Real.sin x)^2-Real.cos x*(Y x)^2)/(Y x)^3
def speed (x : ℝ) : ℝ := horizontal x*factor x
def acceleration (x : ℝ) : ℝ :=
  -vertical x*(factor x)^2+horizontal x*factorD x
def Domain (x : ℝ) : Prop := x∈Icc 0 (7/10) ∧ height x≤outerDiagonal

lemma offset_bounds : (-2/5:ℝ)<offset ∧ offset< -399/1000 := by
  dsimp [offset]
  constructor <;> linarith [fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]

lemma radical_data {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<Z x ∧ Z x<61/100 ∧ (47/25:ℝ)<Y x ∧ Y x<2 ∧
      (Y x)^2+(Z x)^2=Q0 := by
  have ht := positive_trig hx
  have hz : 0<Z x ∧ Z x<61/100 := by
    dsimp [Z]
    constructor <;> linarith [offset_bounds.1,offset_bounds.2,ht.1,ht.2.1]
  have hrad : 0<Q0-(Z x)^2 := by
    norm_num [Q0]
    nlinarith [sq_nonneg (Z x)]
  have hy : 0<Y x := Real.sqrt_pos.2 hrad
  have he : (Y x)^2=Q0-(Z x)^2 := Real.sq_sqrt hrad.le
  refine ⟨hz.1,hz.2,?_,?_,by linarith⟩
  · norm_num [Q0] at he
    nlinarith
  · norm_num [Q0] at he
    nlinarith [sq_nonneg (Z x)]

lemma factor_bounds {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (13/20:ℝ)<factor x ∧ factor x≤1 := by
  have hy := radical_data hx
  have ht := positive_trig hx
  have hyp : 0<Y x := by linarith [hy.2.2.1]
  have hlo : Real.sin x/Y x<(7/20:ℝ) := by
    apply (div_lt_iff₀ hyp).2
    nlinarith [hy.2.2.1,ht.2.2.2.1]
  have hhi : 0≤Real.sin x/Y x := div_nonneg ht.2.2.1 hyp.le
  dsimp [factor]
  exact ⟨by linarith,by linarith⟩

lemma coordinates_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    1<horizontal x ∧ 0<vertical x := by
  have hy := radical_data hx
  have ht := positive_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  have hyp : 0<Y x := by linarith [hy.2.2.1]
  have hmain := mul_lt_mul hy.2.2.1 ht.1.le (by norm_num : (0:ℝ)<19121/25000) hyp.le
  have hsub := mul_le_mul hy.2.1.le ht.2.2.2.1.le ht.2.2.1
    (by norm_num : (0:ℝ)≤61/100)
  have hv1 := mul_nonneg hyp.le ht.2.2.1
  have hv2 := mul_pos hy.1 hc
  dsimp [horizontal,vertical]
  constructor <;> linarith

lemma circle {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (horizontal x)^2+(vertical x)^2=Q0 := by
  have hc := (radical_data hx).2.2.2.2
  dsimp [horizontal,vertical]
  linear_combination hc+((Y x)^2+(Z x)^2)*(Real.sin_sq_add_cos_sq x)

lemma height_zero : height 0=1-outerDiagonal := by
  norm_num [height,vertical,Z,offset]
  ring

lemma Z_hasDerivAt (x : ℝ) : HasDerivAt Z (-Real.sin x) x :=
  (Real.hasDerivAt_cos x).add_const offset

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt Y (Z x*Real.sin x/Y x) x := by
  have hy := radical_data hx
  have hyp : 0<Y x := by linarith [hy.2.2.1]
  have hrad : Q0-(Z x)^2≠0 := (show 0<Q0-(Z x)^2 by nlinarith [hy.2.2.2.2]).ne'
  have hd := (((Z_hasDerivAt x).fun_pow 2).const_sub Q0).sqrt hrad
  show HasDerivAt (fun y => Real.sqrt (Q0-(Z y)^2)) _ x
  refine hd.congr_deriv ?_
  have hYx : Real.sqrt (Q0-(Z x)^2)=Y x := rfl
  rw [hYx]
  field_simp
  norm_num
  ring

lemma horizontal_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt horizontal (-vertical x*factor x) x := by
  have hyp : 0<Y x := by linarith [(radical_data hx).2.2.1]
  have hd := ((Y_hasDerivAt hx).fun_mul (Real.hasDerivAt_cos x)).fun_sub
    ((Z_hasDerivAt x).fun_mul (Real.hasDerivAt_sin x))
  show HasDerivAt (fun y => Y y*Real.cos y-Z y*Real.sin y) _ x
  refine hd.congr_deriv ?_
  dsimp [vertical,factor]
  field_simp
  ring

lemma vertical_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt vertical (speed x) x := by
  have hyp : 0<Y x := by linarith [(radical_data hx).2.2.1]
  have hd := ((Y_hasDerivAt hx).fun_mul (Real.hasDerivAt_sin x)).fun_add
    ((Z_hasDerivAt x).fun_mul (Real.hasDerivAt_cos x))
  show HasDerivAt (fun y => Y y*Real.sin y+Z y*Real.cos y) _ x
  refine hd.congr_deriv ?_
  dsimp [horizontal,factor,speed]
  field_simp
  ring

lemma height_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt height (speed x) x := (vertical_hasDerivAt hx).sub_const (1/2)

lemma factor_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt factor (factorD x) x := by
  have hyp : 0<Y x := by linarith [(radical_data hx).2.2.1]
  have hd := ((Real.hasDerivAt_sin x).fun_div (Y_hasDerivAt hx) hyp.ne').const_sub 1
  show HasDerivAt (fun y => 1-Real.sin y/Y y) _ x
  refine hd.congr_deriv ?_
  dsimp [factorD]
  field_simp
  ring

lemma factorD_numerator {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    factorD x*(Y x)^3=(1-Q0+offset^2)*Real.cos x+
      offset*(1+(Real.cos x)^2) := by
  have hyp : 0<Y x := by linarith [(radical_data hx).2.2.1]
  have hy := (radical_data hx).2.2.2.2
  have he : factorD x*(Y x)^3=Z x*(Real.sin x)^2-Real.cos x*(Y x)^2 := by
    dsimp [factorD]
    field_simp [hyp.ne']
  rw [he]
  dsimp [Z] at hy ⊢
  linear_combination (Real.cos x+offset)*(Real.sin_sq_add_cos_sq x)-Real.cos x*hy

lemma factorD_negative {x : ℝ} (hx : x∈Icc 0 (7/10)) : factorD x<0 := by
  have hy := radical_data hx
  have ht := positive_trig hx
  have hk := offset_bounds
  have he := factorD_numerator hx
  have hcoef : 1-Q0+offset^2<0 := by norm_num [Q0]; nlinarith
  have hfirst := mul_neg_of_neg_of_pos hcoef (by linarith [ht.1] : 0<Real.cos x)
  have hlast := mul_neg_of_neg_of_pos (by linarith [hk.2] : offset<0)
    (by nlinarith [sq_nonneg (Real.cos x)] : 0<1+(Real.cos x)^2)
  have hp := pow_pos (show 0<Y x by linarith [hy.2.2.1]) 3
  nlinarith

lemma speed_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt speed (acceleration x) x := by
  have hd := (horizontal_hasDerivAt hx).fun_mul (factor_hasDerivAt hx)
  show HasDerivAt (fun y => horizontal y*factor y) _ x
  refine hd.congr_deriv ?_
  dsimp [acceleration]
  ring

lemma speed_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : (1/2:ℝ)<speed x := by
  have hh := mul_lt_mul (coordinates_positive hx).1 (factor_bounds hx).1.le
    (by norm_num : (0:ℝ)<13/20)
    (by linarith [(coordinates_positive hx).1] : 0≤horizontal x)
  dsimp [speed]
  linarith

lemma acceleration_negative {x : ℝ} (hx : x∈Icc 0 (7/10)) : acceleration x<0 := by
  have hp := coordinates_positive hx
  have hf := factor_bounds hx
  have hleft := mul_pos hp.2 (pow_pos (show 0<factor x by linarith [hf.1]) 2)
  have hright := mul_neg_of_pos_of_neg (by linarith [hp.1] : 0<horizontal x)
    (factorD_negative hx)
  dsimp [acceleration]
  linarith

lemma height_monotone : MonotoneOn height (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x hx => (height_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun x hx => height_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun x hx => by linarith [speed_positive (Ioo_subset_Icc_self hx)])

lemma height_half_monotone : MonotoneOn (fun x => height x-x/2) (Icc 0 (7/10)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun x hx => ((height_hasDerivAt hx).sub ((hasDerivAt_id x).div_const 2)).continuousAt.continuousWithinAt)
    (fun x hx => (height_hasDerivAt (Ioo_subset_Icc_self hx)).sub ((hasDerivAt_id x).div_const 2))
  intro x hx
  linarith [speed_positive (Ioo_subset_Icc_self hx)]

lemma horizontal_antitone : AntitoneOn horizontal (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x hx => (horizontal_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun x hx => horizontal_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun x hx => by
      have h := coordinates_positive (Ioo_subset_Icc_self hx)
      have f := factor_bounds (Ioo_subset_Icc_self hx)
      linarith [mul_nonneg h.2.le (by linarith [f.1] : 0≤factor x)])

lemma factor_antitone : AntitoneOn factor (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hx => (factor_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun _ hx => factor_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun _ hx => (factorD_negative (Ioo_subset_Icc_self hx)).le)

lemma speed_antitone : AntitoneOn speed (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hx => (speed_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun _ hx => speed_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun _ hx => (acceleration_negative (Ioo_subset_Icc_self hx)).le)

lemma target_mem {x : ℝ} (hx : Domain x) : height x∈Icc 0 outerDiagonal := by
  have hz := height_monotone (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx.1 hx.1.1
  rw [height_zero] at hz
  exact ⟨by linarith [outer_endpoint_bounds.2.2.2],hx.2⟩

end SquaresInCircles.Eight.SecondWord.NegativeTwo.PrimaryDiagonal
end
end
end
