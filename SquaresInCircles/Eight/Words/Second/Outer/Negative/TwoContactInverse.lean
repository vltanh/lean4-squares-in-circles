module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoTargetContact
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Eight squares: the explicit inverse of the original circle contact

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
