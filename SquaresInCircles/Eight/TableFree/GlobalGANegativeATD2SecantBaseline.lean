module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2HighSaturated
public import SquaresInCircles.Eight.TableFree.SecantNormCurvature

/-!
# The exact secant baseline and its angular derivative

Uncompiled transcription of (10)--(11) in the negative-A angle companion.
The analytic extension agrees with the original baseline throughout the
nonnegative frame interval. Its only varying norm is the affected G or
B pair; the other terms are constant in s.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.SecantBaseline
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus
open SecantNormCurvature

def affected (atG : Bool) (k c z : ℝ) : ℝ := if atG then k else PositiveTD.tilted c z
def basicRatio (atG : Bool) (k l c z : ℝ) : ℝ := affected atG k c z/l
def angularBaseline (atG : Bool) (k l c s z : ℝ) : ℝ :=
  baseline atG k l c 0 z+FlatTStress.secantCharge R l (affected atG k c z) s
def denominator (r s : ℝ) : ℝ := Real.sqrt (1+r^2*Real.cos s^2)
def angleSlope (l r s : ℝ) : ℝ :=
  l*(13/12+Real.sin s-R*Real.sin s/denominator r s)/Real.cos s^2

theorem baseline_eq_extension (atG : Bool) (k l c z : ℝ) {s : ℝ}
    (hs : s∈Icc 0 frameCap) :
    baseline atG k l c s z=angularBaseline atG k l c s z := by
  have hw := secant_width_identity (l:=l) hs
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  cases atG
  · simp only [angularBaseline,baseline,affected,lambdaG,lambdaB,↓reduceIte,
      NegativeAPositiveTD.secant,Real.cos_zero,div_one,Real.tan_zero,edgeWidth_zero,
      mul_zero,add_zero,sub_zero,fullSupport_pair,FlatTStress.secantCharge]
    dsimp [NegativeAPositiveTD.secant] at hw
    have hid : l*(1/Real.cos s-1+(13/12)*Real.tan s)=
        l/Real.cos s-l+(13/12)*l*Real.tan s := by ring
    rw [hid]
    linarith only [hw]
  · simp only [angularBaseline,baseline,affected,lambdaG,lambdaB,↓reduceIte,
      NegativeAPositiveTD.secant,Real.cos_zero,div_one,Real.tan_zero,edgeWidth_zero,
      mul_zero,add_zero,sub_zero,fullSupport_pair,FlatTStress.secantCharge]
    rw [pairNorm_symm (l/Real.cos s) k,pairNorm_symm l k]
    dsimp [NegativeAPositiveTD.secant] at hw
    have hid : l*(1/Real.cos s-1+(13/12)*Real.tan s)=
        l/Real.cos s-l+(13/12)*l*Real.tan s := by ring
    rw [hid]
    linarith only [hw]

theorem denominator_pos (r s : ℝ) : 0<denominator r s :=
  Real.sqrt_pos.mpr (by positivity)

theorem denominator_sq (r s : ℝ) : (denominator r s)^2=1+r^2*Real.cos s^2 :=
  Real.sq_sqrt (by positivity)

theorem support_norm_identity {r s : ℝ} (hc : 0<Real.cos s) :
    supportNorm r s=denominator r s/Real.cos s := by
  have hN := norm_pos (a:=r) hc
  have hN2 := norm_sq r s
  have hD := denominator_pos r s
  have hD2 := denominator_sq r s
  have he : (supportNorm r s*Real.cos s)^2=(denominator r s)^2 := by
    rw [mul_pow,hN2,hD2]
    dsimp [SecantNormCurvature.secant]
    field_simp [hc.ne']
    ring
  have he' : supportNorm r s*Real.cos s=denominator r s := by
    nlinarith [mul_pos hN hc]
  exact (eq_div_iff hc.ne').2 he'

theorem angleSlope_eq {l r s : ℝ} (hc : 0<Real.cos s) :
    l*gainFirst R r s=angleSlope l r s := by
  dsimp [gainFirst,normFirst,first,SecantNormCurvature.secant,angleSlope]
  rw [support_norm_identity hc]
  field_simp [hc.ne',(denominator_pos r s).ne']
  ring

theorem angularBaseline_hasDerivAt (atG : Bool) {k l c s z : ℝ}
    (hl : 0<l) (hc : 0<Real.cos s) :
    HasDerivAt (fun s => angularBaseline atG k l c s z)
      (angleSlope l (basicRatio atG k l c z) s) s := by
  have hh := (charge_hasDerivAt (R:=R) (a:=affected atG k c z) hl hc).const_add
    (baseline atG k l c 0 z)
  simpa only [angularBaseline,basicRatio,angleSlope_eq hc] using hh

theorem coefficient_upper {r s r₀ c₀ D : ℝ}
    (hr₀ : 0≤r₀) (hc₀ : 0≤c₀) (hD : 0<D)
    (hr : r₀≤r) (hc : c₀≤Real.cos s)
    (hsquare : qCap<D^2*(1+r₀^2*c₀^2)) :
    R/denominator r s<D := by
  have hr0 := hr₀.trans hr
  have hc0 := hc₀.trans hc
  have hrc := mul_le_mul hr hc hc₀ hr0
  have hrc2 := pow_le_pow_left₀ (mul_nonneg hr₀ hc₀) hrc 2
  have hden : 1+r₀^2*c₀^2≤(denominator r s)^2 := by
    rw [denominator_sq]
    nlinarith only [hrc2]
  have hscaled := mul_le_mul_of_nonneg_left hden (sq_nonneg D)
  apply OrdinaryCurvatureBounds.quotient_lt_of_square (denominator_pos r s) hD
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  nlinarith

theorem slope_lower {l r s D y b : ℝ}
    (hl : 0<l) (hc : 0<Real.cos s) (hs : 0≤Real.sin s)
    (hsy : Real.sin s≤y) (hD : 1≤D) (hb : 0≤b)
    (hcoeff : R/denominator r s≤D) (hreserve : b<13/12-(D-1)*y) :
    b*l<angleSlope l r s := by
  have hmul := mul_le_mul_of_nonneg_right hcoeff hs
  have hsy' := mul_le_mul_of_nonneg_left hsy (sub_nonneg.mpr hD)
  have hnum : b<13/12+Real.sin s-R*Real.sin s/denominator r s := by
    have he : R*Real.sin s/denominator r s=(R/denominator r s)*Real.sin s := by ring
    rw [he]
    linarith
  have hcos2 : Real.cos s^2≤1 := by nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.sin s)]
  have hbc := mul_le_mul_of_nonneg_left hcos2 hb
  have hbase := mul_lt_mul_of_pos_left hnum hl
  have hbase' := mul_le_mul_of_nonneg_left hbc hl.le
  unfold angleSlope
  apply (lt_div_iff₀ (sq_pos_of_pos hc)).2
  nlinarith only [hbase,hbase']

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.SecantBaseline
