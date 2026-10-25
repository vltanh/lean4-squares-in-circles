module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositePositiveZeroGeometry

/-!
# The source-zero boundary curvature and endpoints

Uncompiled transcription of the second boundary in Section 3.2. The
original target coordinate has logarithmic curvature greater than .423.
The only convex target labels have relative curvature less than .361,
so the complete boundary costs are concave. Their original diagonal
entry and final-angle endpoint supply the strict reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Zero
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

open SecondWord (U W outer_domain outer_zero_mem)
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.SameZero.PJ.Reference (sinBox cosBox aBox)

def value (r : Row) (x : ℝ) : ℝ := x+c r+p r*outerAxial+(target r).outer (height x)
def heightD (x : ℝ) : ℝ := -horizontal x*factor x
def heightDD (x : ℝ) : ℝ :=
  -vertical x*(factor x)^2-horizontal x*factorD x
def first (r : Row) (x : ℝ) : ℝ := 1+h r (height x)*heightD x
def second (r : Row) (x : ℝ) : ℝ :=
  -v r*ratioD (height x)*(heightD x)^2+h r (height x)*heightDD x

lemma height_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt height (heightD x) x :=
  (ShortMixedZero.NegativeContact.V_hasDerivAt hx).sub_const (1/2)

lemma heightD_hasDerivAt {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt heightD (heightDD x) x := by
  have h : HasDerivAt (fun y => -horizontal y*factor y)
      (-(vertical x*factor x)*factor x+-horizontal x*factorD x) x :=
    (ShortMixedZero.NegativeContact.U_hasDerivAt hx).neg.mul
      (ShortMixedZero.NegativeContact.speed_hasDerivAt hx)
  exact h.congr_deriv (by dsimp only [heightDD]; ring)

lemma heightD_negative {x : ℝ} (hx : x∈Icc start (7/10)) : heightD x<0 := by
  have hc := ShortMixedZero.NegativeContact.coordinates hx
  have hs := ShortMixedZero.NegativeContact.speed_pos hx
  have hp := mul_pos (show 0<horizontal x by linarith [hc.1]) hs
  dsimp only [heightD]
  linarith

lemma height_curvature {x : ℝ} (hx : x∈Icc start (7/10)) :
    heightDD x< -(423/1000)*(heightD x)^2 := by
  have hc := ShortMixedZero.NegativeContact.coordinates hx
  have hs := ShortMixedZero.NegativeContact.speed_pos hx
  have hd := ShortMixedZero.NegativeContact.speedD_pos hx
  have hU0 : 0<horizontal x := by linarith [hc.1]
  have hU2 : (horizontal x)^2<(1629/1000:ℝ)^2 := by nlinarith [hc.1,hc.2.1]
  have hV : (423/1000)*(horizontal x)^2<vertical x := by
    nlinarith [hc.2.2.1]
  have hstrict := mul_lt_mul_of_pos_right hV (pow_pos hs 2)
  have hpositive := mul_pos hU0 hd
  dsimp only [heightD,heightDD]
  nlinarith

lemma ratioD_upper {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : ratioD B<(1431/1000:ℝ) := by
  have hU : (1399/1000:ℝ)<U B := (SecondWord.UW_bounds hB).1
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hU.le 3
  change Q0/(U B)^3<1431/1000
  apply (div_lt_iff₀ (pow_pos (by linarith : 0<U B) 3)).2
  norm_num [Q0] at hcube ⊢
  linarith

lemma target_relative_curvature (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hv : v r<0) : -v r*ratioD B<(361/1000)*h r B := by
  have hD := ratioD_upper hB
  have hR := ShortOuterOne.SameContact.ratio_pos (outer_domain hB)
  have hD0 := ShortOuterOne.SameContact.ratioD_pos (outer_domain hB)
  have hcoef : -v r≤(19335/100000:ℝ) := by fin_cases r <;> norm_num [v]
  have ht : (76744/100000:ℝ)≤t r := by fin_cases r <;> norm_num [t]
  have hprod := mul_le_mul hcoef hD.le hD0.le (by norm_num)
  have hL : t r≤h r B := by
    have hh := mul_nonpos_of_nonpos_of_nonneg hv.le hR.le
    dsimp [h]
    linarith
  nlinarith

lemma value_hasDerivAt (r : Row) {x : ℝ} (hx : Physical x) :
    HasDerivAt (value r) (first r x) x := by
  have h1 : HasDerivAt (fun y => (target r).outer (height y))
      ((target r).d1 (height x)*heightD x) x :=
    ((target r).outer_hasDerivAt (outer_domain (target_mem hx))).comp x (height_hasDerivAt hx.1)
  have h : HasDerivAt (fun y => y+c r+p r*outerAxial+(target r).outer (height y))
      (1+(target r).d1 (height x)*heightD x) x :=
    (((hasDerivAt_id' x).add_const (c r)).add_const (p r*outerAxial)).add h1
  rw [derivative_target] at h
  exact h

lemma first_hasDerivAt (r : Row) {x : ℝ} (hx : Physical x) :
    HasDerivAt (first r) (second r x) x := by
  have h1 : HasDerivAt (fun y => h r (height y)) (-v r*ratioD (height x)*heightD x) x :=
    (h_hasDerivAt r (target_mem hx)).comp x (height_hasDerivAt hx.1)
  have h : HasDerivAt (fun y => 1+h r (height y)*heightD y)
      (-v r*ratioD (height x)*heightD x*heightD x+h r (height x)*heightDD x) x :=
    (h1.mul (heightD_hasDerivAt hx.1)).const_add 1
  exact h.congr_deriv (by dsimp only [second]; ring)

lemma curvature_negative (r : Row) {x : ℝ} (hx : Physical x) : second r x<0 := by
  have htarget := (slope_bounds r (target_mem hx)).2.2
  have hD := ShortOuterOne.SameContact.ratioD_pos (outer_domain (target_mem hx))
  have hs := sq_pos_of_neg (heightD_negative hx.1)
  have hcurve := mul_lt_mul_of_pos_left (height_curvature hx.1) htarget
  by_cases hv : v r<0
  · have hlabel := mul_lt_mul_of_pos_right (target_relative_curvature r (target_mem hx) hv) hs
    have hpay := mul_pos htarget hs
    dsimp [second]
    nlinarith
  · have hlabel := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith : -v r≤0) hD.le) hs.le
    have hpay := mul_pos htarget hs
    dsimp [second]
    nlinarith

def capZ : Interval (ShortMixedZero.NegativeContact.Z (7/10)) :=
  let W := ((Interval.point (1/2)).add (sinBox (7/10) (by norm_num))).add (cosBox (7/10) (by norm_num))
  ⟨W.lo,W.hi,by
    have h : ShortMixedZero.NegativeContact.Z (7/10)=1/2+Real.sin (7/10)+Real.cos (7/10) := by
      simp only [ShortMixedZero.NegativeContact.Z,ShortMixedZero.NegativeContact.m]; ring
    rw [h]; exact W.mem⟩
def capRad : Interval (Q0-(ShortMixedZero.NegativeContact.Z (7/10))^2) := (Interval.point Q0).sub capZ.square

macro "zero_reference_arithmetic" : tactic => `(tactic|
  norm_num [capZ,capRad,rootThree,rootStep,coordinate,c,p,q,v,t,Q0,
    SecondWord.SameZero.PJ.Reference.sinBox,SecondWord.SameZero.PJ.Reference.cosBox,
    SecondWord.SameZero.PJ.Reference.aBox,Interval.point,Interval.of_bounds,
    Interval.add,Interval.sub,Interval.neg,Interval.mul,Interval.square,
    Interval.div,Interval.inv,HighOrderTaylor.S17,HighOrderTaylor.S15,
    HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,HighOrderTaylor.C16,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8])

def capY : Interval (ShortMixedZero.NegativeContact.Y (7/10)) :=
  rootThree capRad 1 (by norm_num) (by zero_reference_arithmetic)
def capU : Interval (horizontal (7/10)) :=
  (capZ.mul (sinBox (7/10) (by norm_num))).add (capY.mul (cosBox (7/10) (by norm_num)))
def capV : Interval (vertical (7/10)) :=
  (capZ.mul (cosBox (7/10) (by norm_num))).sub (capY.mul (sinBox (7/10) (by norm_num)))

lemma cap_physical : Physical (7/10) := by
  have hV : capV.hi<(9/8:ℝ) := by dsimp [capV,capY]; zero_reference_arithmetic
  refine ⟨by norm_num [start,ShortMixedZero.NegativeContact.start],?_⟩
  have hh := capV.mem.2.trans_lt hV
  dsimp [height]
  linarith [outer_endpoint_bounds.2.2.1]

lemma cap_value (r : Row) : (123/100:ℝ)<value r (7/10) := by
  let V := (((Interval.point ((7/10:ℝ)+c r)).add ((Interval.point (p r)).mul aBox)).add
    ((Interval.point (v r)).mul (capU.sub (Interval.point (1/2))))).add
      ((Interval.point (t r)).mul (capV.sub (Interval.point (1/2))))
  have hv : (123/100:ℝ)<V.lo := by
    fin_cases r <;> dsimp [V,capU,capV,capY] <;> zero_reference_arithmetic
  have hvalue : value r (7/10)=
      7/10+c r+p r*outerAxial+v r*(horizontal (7/10)-1/2)+t r*(vertical (7/10)-1/2) := by
    rw [value]
    dsimp only [target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval]
    rw [original_arc cap_physical]
    dsimp only [height]
    ring
  rw [hvalue]
  exact hv.trans_le V.mem.1

lemma value_actual (r : Row) {x : ℝ} (hx : Physical x) :
    value r x=plusCost r (height x) x := by
  have hz : plus (height x) x=0 := contact hx
  simp only [value,plusCost,hz,source,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
    ShortOuterOne.SameContact.arc_zero]
  ring

/-- The whole physical source-zero arc, with the diagonal join retained. -/
theorem lower (r : Row) {x : ℝ} (hx : Physical x) :
    (89809/100000:ℝ)<value r x := by
  obtain ⟨e,he,hentry,hdom⟩ := entry hx
  have hc : ConcaveOn ℝ (Icc e (7/10)) (value r) :=
    concave_of_deriv2 (fun y hy => value_hasDerivAt r (hdom y hy))
      (fun y hy => first_hasDerivAt r (hdom y hy))
      (fun y hy => (curvature_negative r (hdom y hy)).le)
  apply concave_gt_of_endpoints hc ⟨he.2,hx.1.2⟩
  · have hei : e∈Icc e (7/10) := ⟨le_rfl,he.2.trans hx.1.2⟩
    have hde := domain (hdom e hei)
    have hl := target_diagonal_lower r (by simpa [hentry] using hde)
    rw [value_actual r (hdom e hei),hentry]
    exact hl
  · linarith [cap_value r]

theorem original_lower (r : Row) {B x : ℝ} (hd : PlusDomain B x) (hz : plus B x=0) :
    (89809/100000:ℝ)<plusCost r B x := by
  obtain ⟨hx,hB⟩ := original_coordinates hd hz
  have hh := lower r hx
  rwa [value_actual r hx,hB] at hh

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Zero
