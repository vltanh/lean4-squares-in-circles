module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoTargetContact
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The explicit inverse of the original circle contact

The inverse is an arctangent followed by an arcsine on a strictly
positive physical radical.  Its original-angle identity includes weak
contact endpoints.  Both derivatives are proved from this formula,
without an implicit minimizer or a chosen contact branch as a premise.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.ContactInverse

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
  have hq : Inverse.q (U b)≠0 := by linarith [Inverse.actual_q_positive hb]
  have hd := ((Inverse.q_hasDerivAt (U b)).comp b
    ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2))).sqrt hq
  convert hd using 1 <;> dsimp [radius,U] <;> ring

lemma speed_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    HasDerivAt (speed z) (ratio b/speed z b) b := by
  have hd := data hb hz
  have hrad : Inverse.q (U b)-z^2≠0 := by
    nlinarith [sq_pos_of_pos hd.2.2.2.2.1,hd.2.2.2.2.2]
  have hder := (((Inverse.q_hasDerivAt (U b)).comp b
    ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const
      (1/2))).sub_const (z^2)).sqrt hrad
  convert hder using 1 <;> dsimp [speed,U] <;> ring

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
    (by linarith [hu.2.2.1]) (by linarith [hu.1]) (Or.inr rfl)
  have he : (W b)^2+(U b-1)^2=Inverse.q (U b) := by
    linarith [base_circle hb]
  simpa only [one_mul,he,radius,baseAngle] using hh

lemma base_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt baseAngle (-Inverse.factor (U b)) b := by
  have hu := U_positive (outer_domain hb)
  have hw : 0<W b := by dsimp [W]; linarith [hb.1]
  have hq : Inverse.q (U b)≠0 := by linarith [Inverse.actual_q_positive hb]
  have hden : 1+((U b-1)/W b)^2=Inverse.q (U b)/(W b)^2 := by
    field_simp [hw.ne']
    nlinarith [base_circle hb]
  have hinner := (((ShortOuterOne.SameContact.arc_hasDerivAt
    (outer_domain hb)).add_const (1/2)).sub_const 1).div
      ((hasDerivAt_id b).add_const (1/2)) hw.ne'
  have hd := (Real.hasDerivAt_arctan ((U b-1)/W b)).comp b hinner
  convert hd using 1
  · rfl
  · rw [hden]
    dsimp [Inverse.factor,ratio]
    change -(Q0-U b)/(U b*Inverse.q (U b))=_
    field_simp [hu.ne',hw.ne',hq]
    dsimp [Inverse.q,U,W]
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
  have hinner := (hasDerivAt_const b z).div (radius_hasDerivAt hb) hr.ne'
  have hasin := (Real.hasDerivAt_arcsin
    (by linarith : z/radius b≠-1) (by linarith : z/radius b≠1)).comp b hinner
  have hder : HasDerivAt (fun y => Real.arcsin (z/radius y))
      (-z*ratio b/(Inverse.q (U b)*speed z b)) b := by
    convert hasin using 1
    rw [inverse_root hb hz,←hd.2.2.2.1]
    field_simp [hr.ne',hv.ne']
    ring
  convert (base_hasDerivAt hb).add hder using 1 <;> dsimp [angle,first] <;> ring

lemma first_hasDerivAt {b z : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hz : z∈Icc (-(1/2)) (2/5)) :
    HasDerivAt (first z) (second z b) b := by
  have hd := data hb hz
  have hu := hd.1
  have hv := hd.2.2.2.2.1
  have hq : Inverse.q (U b)≠0 := by linarith [Inverse.actual_q_positive hb]
  have huD := (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const (1/2)
  have hf := (Inverse.factor_hasDerivAt hu.ne' hq).comp b huD
  have hden := ((Inverse.q_hasDerivAt (U b)).comp b huD).mul (speed_hasDerivAt hb hz)
  have hnum := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul z
  have hder := hf.neg.sub (hnum.div hden (mul_ne_zero hq hv.ne'))
  convert hder using 1
  · rfl
  · dsimp [second,PJCritical.inverseTarget,PJCritical.heightFactorD,Inverse.brace,
      ratioD]
    change -(-ratio b*Inverse.factorD (U b)+
      z/(Inverse.q (U b)*speed z b)*
        (Q0/(U b)^3-2*(ratio b)^2/Inverse.q (U b)-
          (ratio b)^2/(speed z b)^2))=_
    field_simp [hu.ne',hq,hv.ne']
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
  constructor <;>
    dsimp [TargetContact.B,TargetContact.v,angle] <;>
    rw [Real.cos_add,Real.sin_add,ht.1,ht.2,hs,hc] <;>
    change _=_ <;>
    dsimp [U,W] at hn ⊢ <;>
    field_simp [hr.ne'] <;> nlinarith [hn]

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

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.ContactInverse
