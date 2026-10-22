module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2OrdinarySlopes
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2CurvatureConstants
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2SecantCoordinate

/-!
# The ordinary part of the negative-DE third derivative

Uncompiled transcription of Sections 4 and 9 of the negative-DE TD2
angle companion, also used by Section 7 of its positive-BT3 companion.
The full signed curvature tangent gives the stronger negative derivative
bounds. The early and late polynomial comparisons keep each actual
ordinary pair and its original larger coefficient.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope PairNormCalculus OrdinaryCurvatureBounds
open NegativeAPositiveTD.Curvature NegativeAPositiveTD.SecantCoordinate

def Vdd (p q t : ℝ) : ℝ := curvature R p q (-t)-q*Real.cos t
def Vddd (p q t : ℝ) : ℝ := -curvatureD R p q (-t)+q*Real.sin t
def numerator (p q d x : ℝ) : ℝ :=
  -Vddd p q d-6*x*Vdd p q d+2*(1-3*x^2)*Vd R p q d
def pureThird (l c p q θ x : ℝ) : ℝ :=
  l*baseThird c x+numerator p q (θ-Real.arctan x) x/(1+x^2)^3

theorem Vdd_hasDerivAt {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) : HasDerivAt (Vdd p q) (Vddd p q t) t := by
  have hc := (curvature_hasDerivAt (R:=R) hp hq
    (by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)).comp t (hasDerivAt_neg t)
  convert hc.sub ((Real.hasDerivAt_cos t).const_mul q) using 1 <;>
    dsimp [Vdd,Vddd] <;> ring

theorem pureSecond_hasDerivAt {l c p q θ x : ℝ} (hp : 0<p) (hq : 0<q)
    (hd : θ-Real.arctan x∈Icc 0 frameCap) :
    HasDerivAt (pureSecond l c p q θ) (pureThird l c p q θ x) x := by
  have harg := (Real.hasDerivAt_arctan x).const_sub θ
  have hV := (Vd_hasDerivAt (R:=R) hp hq hd).comp x harg
  have hVV := (Vdd_hasDerivAt hp hq hd).comp x harg
  have hden : 1+x^2≠0 := by positivity
  have hn := hVV.add ((((hasDerivAt_id x).const_mul 2).mul hV))
  have hratio := hn.div ((((hasDerivAt_id x).pow 2).const_add 1).pow 2)
    (pow_ne_zero 2 hden)
  convert ((baseSecond_hasDerivAt c x).const_mul l).add hratio using 1
  · funext y
    dsimp [pureSecond,negativeSecond,Vdd]
    ring
  · dsimp [pureThird,numerator,Vdd]
    field_simp [hden]
    ring

/-- The complete quadratic negative-curvature tangent, before any
short-angle weakening. -/
theorem second_model {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) :
    Vdd p q d<q*(-3/10-d/3+d^2/2) := by
  have hq := hp.trans_le hpq
  have hconstants := universal_constants hp hpq hqp
  have ht := curvature_signed_tangent hp hpq hqp
    (t:=-d) (by rw [abs_neg,abs_of_nonneg hd.1]; exact hd.2)
  have hm := mul_le_mul_of_nonneg_right hconstants.2.1.le hd.1
  have hcos := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x:=d)) hq.le
  dsimp [Vdd]
  nlinarith

theorem third_model {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) :
    q*(1/3-d)<-Vddd p q d := by
  have hq := hp.trans_le hpq
  have hconst := (universal_constants hp hpq hqp).2.1
  have hcurv := curvatureD_antitone_signed hp hpq hqp
    (show -d∈Icc (-frameCap) frameCap by constructor <;> linarith [hd.1,hd.2])
    (show (0:ℝ)∈Icc (-frameCap) frameCap by norm_num [frameCap]) (by linarith [hd.1])
  rw [curvatureD_zero] at hcurv
  have hs := mul_le_mul_of_nonneg_left (Real.sin_le hd.1) hq.le
  dsimp [Vddd]
  linarith

theorem second_whole {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) :
    Vdd p q d<-(36/125)*q := by
  have hm := second_model hp hpq hqp hd
  have hq := hp.trans_le hpq
  have hpoly : -3/10-d/3+d^2/2≤-(36/125:ℝ) := by
    have h := mul_nonneg hd.1 (sub_nonneg.mpr hd.2)
    dsimp [frameCap] at *
    nlinarith
  exact hm.trans_le (by nlinarith [mul_le_mul_of_nonneg_left hpoly hq.le])

theorem second_short {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 (177/1000:ℝ)) :
    Vdd p q d<-(3/10)*q := by
  have hm := second_model hp hpq hqp
    ⟨hd.1,by norm_num [frameCap]; linarith [hd.2]⟩
  have hprod := mul_nonneg hd.1 (show 0≤2/3-d by linarith [hd.2])
  have hq := hp.trans_le hpq
  nlinarith [mul_nonneg hq.le hprod]

theorem third_whole {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) : Vddd p q d<(39/125)*q := by
  have hq := hp.trans_le hpq
  have hconst := (universal_constants hp hpq hqp).2.1
  have hcurv := curvatureD_antitone_signed hp hpq hqp
    (show -d∈Icc (-frameCap) frameCap by constructor <;> linarith [hd.1,hd.2])
    (show (0:ℝ)∈Icc (-frameCap) frameCap by norm_num [frameCap]) (by linarith [hd.1])
  rw [curvatureD_zero] at hcurv
  have hs := mul_lt_mul_of_pos_left (transport_trig hd).2.2.2.1 hq
  dsimp [Vddd]
  nlinarith

theorem first_upper {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) : Vd R p q d<(7/5)*q := by
  have hh := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le hp hpq hqp
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hd hd.1
  have hzero : Vd R p q 0=slopeZero p q := by
    simp [Vd,mixedNDerivative,normD1,slopeZero]
  rw [hzero] at hh
  exact hh.trans_lt (universal_constants hp hpq hqp).2.2

theorem first_upper_late {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 (3/20:ℝ)) :
    Vd R p q d<q*(7/5-(3/10)*d) := by
  have hderiv (t : ℝ) (ht : t∈Icc 0 d) :=
    (Vd_hasDerivAt (R:=R) hp (hp.trans_le hpq)
      ⟨ht.1,by norm_num [frameCap]; linarith [ht.2,hd.2]⟩).neg
  have hh := derivative_reserve (f:=fun t => -Vd R p q t)
    (df:=fun t => -Vdd p q t) (k:=(3/10)*q)
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t (Ioo_subset_Icc_self ht))
    (fun t ht => by
      have hb := second_short hp hpq hqp
        (show t∈Icc 0 (177/1000:ℝ) by exact ⟨ht.1.le,by linarith [ht.2,hd.2]⟩)
      linarith)
    (show (0:ℝ)∈Icc 0 d from ⟨le_rfl,hd.1⟩)
    (show d∈Icc 0 d from ⟨hd.1,le_rfl⟩) hd.1
  have hzero := first_upper hp hpq hqp (d:=0) (by norm_num [frameCap])
  nlinarith

theorem numerator_early_low {p q d x : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (2/3)*q≤p) (hd : d∈Icc 0 frameCap)
    (hx : 0≤x) (hx3 : 3*x^2≤1) : (137/200)*q<numerator p q d x := by
  have hq := hp.trans_le hpq
  have hqp : q≤2*p := by linarith
  have h₂ := second_whole hp hpq hqp hd
  have h₃ := third_whole hp hpq hqp hd
  have h₁ := Vd_lower hp hpq hratio hd
  have hmul₂ := mul_le_mul_of_nonpos_left h₂.le (show -6*x≤0 by linarith)
  have hmul₁ := mul_le_mul_of_nonneg_left h₁.le (show 0≤2*(1-3*x^2) by linarith)
  have hxu : x≤577351/1000000 := by nlinarith
  have hpoly : (137/200:ℝ)<4/3-39/125+(216/125)*x-4*x^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hxu)
      (show 0≤4*(x+577351/1000000)-216/125 by linarith)
    nlinarith
  have hqpoly := mul_lt_mul_of_pos_left hpoly hq
  dsimp [numerator]
  nlinarith

theorem numerator_early_middle {p q d x : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 (177/1000:ℝ))
    (hx : x∈Icc 0 (307/500:ℝ)) (hx3 : 1≤3*x^2) :
    (447/500)*q<numerator p q d x := by
  have hq := hp.trans_le hpq
  have hd' : d∈Icc 0 frameCap := ⟨hd.1,by norm_num [frameCap]; linarith [hd.2]⟩
  have h₂ := second_short hp hpq hqp hd
  have h₃ := third_model hp hpq hqp hd'
  have h₁ := first_upper hp hpq hqp hd'
  have hmul₂ := mul_le_mul_of_nonpos_left h₂.le (show -6*x≤0 by linarith [hx.1])
  have hmul₁ := mul_le_mul_of_nonpos_left h₁.le (show 2*(1-3*x^2)≤0 by linarith)
  have hpoly : (447/500:ℝ)<1/3-177/1000+(9/5)*x+(14/5)*(1-3*x^2) := by
    have hh := mul_nonneg (sub_nonneg.mpr hx.2)
      (show 0≤(42/5)*(x+307/500)-9/5 by linarith [hx.1])
    nlinarith
  have hqpoly := mul_lt_mul_of_pos_left hpoly hq
  have hqd := mul_le_mul_of_nonneg_left hd.2 hq.le
  dsimp [numerator]
  nlinarith

def latePolynomial (x : ℝ) : ℝ := 47/15+(9/5)*x-(42/5)*x^2

theorem numerator_late {p q d x : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 (3/20:ℝ))
    (hx : 613/1000≤x) : q*latePolynomial x≤numerator p q d x := by
  have hq := hp.trans_le hpq
  have hd' : d∈Icc 0 frameCap := ⟨hd.1,by norm_num [frameCap]; linarith [hd.2]⟩
  have h₂ := second_model hp hpq hqp hd'
  have h₃ := third_model hp hpq hqp hd'
  have h₁ := first_upper_late hp hpq hqp hd
  have hx0 : 0≤x := by linarith
  have hx3 : 1≤3*x^2 := by nlinarith [sq_nonneg (x-613/1000)]
  have hmul₂ := mul_le_mul_of_nonpos_left h₂.le (show -6*x≤0 by linarith)
  have hmul₁ := mul_le_mul_of_nonpos_left h₁.le (show 2*(1-3*x^2)≤0 by linarith)
  have hdd : 3*x*d^2≤(9/20)*x*d := by
    have hh := mul_nonneg hd.1 (sub_nonneg.mpr hd.2)
    nlinarith [mul_nonneg hx0 hh]
  have hfactor : 0≤-(8/5)+(31/20)*x+(9/5)*x^2 := by
    nlinarith [sq_nonneg (x-613/1000)]
  have hrem := mul_nonneg hd.1 hfactor
  have hqrem := mul_nonneg hq.le
    (show 0≤d*(-8/5+2*x+(9/5)*x^2)-3*x*d^2 by nlinarith)
  dsimp [numerator,latePolynomial]
  nlinarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape
