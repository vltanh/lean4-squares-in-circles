module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowD
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHHComparison

/-!
# The coefficient comparison in the low-DE positive surplus

Uncompiled equation (30) of the negative-DE TD2 angle companion. The
larger coefficient is increased first. With that coefficient fixed at
1.864, the smaller coefficient is increased to 1.352. The latter step
uses the displayed decreasing trigonometric quotient, not a replacement
of the original pair in the source stress.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowPositive
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NegativeAPositiveTD.PositiveSlope

abbrev pMax : ℝ := 169/125
abbrev qMax : ℝ := 233/125

def ratioModel (r t : ℝ) : ℝ :=
  (Real.cos t-Real.sin t)*(pairNorm r 1 t)^3/
    (Real.cos t*(1+r*Real.sin t))
def ratioFirst (r t : ℝ) : ℝ :=
  pairNorm r 1 t*(r*Real.cos t^2*(Real.cos t-Real.sin t)*(2-r^2+r*Real.sin t)-
    (pairNorm r 1 t)^2*(1+r*Real.sin t))/
      (Real.cos t^2*(1+r*Real.sin t)^2)

theorem ratio_derivative {r t : ℝ} (hr : 0<r) (ht : t∈Icc 0 frameCap) :
    HasDerivAt (ratioModel r) (ratioFirst r t) t := by
  have hn := pairNorm_pos hr (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hn2 := pairNorm_sq hr (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hc := NegativeESecant.cos_pos ht
  have hv : 0<1+r*Real.sin t := by
    have hs := (transport_trig ht).2.2.1
    positivity
  have hnorm := pairNorm_hasDerivAt hr (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hd := (((Real.hasDerivAt_cos t).sub (Real.hasDerivAt_sin t)).mul
    (hnorm.pow 3)).div ((Real.hasDerivAt_cos t).mul
      (((Real.hasDerivAt_sin t).const_mul r).const_add 1)) (mul_ne_zero hc.ne' hv.ne')
  convert hd using 1
  · rfl
  · dsimp [ratioFirst,normD1,pairEnergy,pairProduct] at hn2 ⊢
    field_simp [hn.ne',hc.ne',hv.ne']
    linear_combination
      (pairNorm r 1 t)^3*(1+r*Real.sin t)*(Real.sin_sq_add_cos_sq t)

theorem ratio_antitone {r : ℝ} (hr : r∈Ioc (0:ℝ) (73/100)) :
    AntitoneOn (ratioModel r) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun t ht => (ratio_derivative hr.1 ht).continuousAt.continuousWithinAt)
    (fun t ht => ratio_derivative hr.1 (Ioo_subset_Icc_self ht))
  intro t ht
  have ht' := Ioo_subset_Icc_self ht
  have hs := transport_trig ht'
  have hn := pairNorm_pos hr.1 (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg ht'.1]; exact ht'.2)
  have hn2 := pairNorm_sq hr.1 (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg ht'.1]; exact ht'.2)
  norm_num only [pairEnergy,pairProduct,one_pow,mul_one] at hn2
  have hr2 := pow_le_pow_left₀ hr.1.le hr.2 2
  have hcos2 : Real.cos t^2≤1 := by nlinarith [Real.sin_sq_add_cos_sq t]
  have hphi : 0≤Real.cos t-Real.sin t := by linarith [hs.1,hs.2.2.2.1]
  have hphi1 : Real.cos t-Real.sin t≤1 := by linarith [Real.cos_le_one t,hs.2.2.1]
  have hfactor : Real.cos t^2*(Real.cos t-Real.sin t)≤1 := by
    have hh := mul_le_mul hcos2 hphi1 hphi (by norm_num : (0:ℝ)≤1)
    simpa using hh
  have hcoef : 0≤r*(2-r^2+r*Real.sin t) := by
    have hh := mul_nonneg hr.1.le hs.2.2.1
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hfactor hcoef
  have hrest : 0≤r*Real.sin t*(3+r^2-r) := by
    apply mul_nonneg (mul_nonneg hr.1.le hs.2.2.1)
    nlinarith
  have hpoly : r*(2-r^2+r*Real.sin t)≤(pairNorm r 1 t)^2*(1+r*Real.sin t) := by
    rw [hn2]
    nlinarith [sq_nonneg (1-r),pow_nonneg hr.1.le 3,
      mul_nonneg (sq_nonneg r) (sq_nonneg (Real.sin t))]
  have hnum : r*Real.cos t^2*(Real.cos t-Real.sin t)*(2-r^2+r*Real.sin t)-
      (pairNorm r 1 t)^2*(1+r*Real.sin t)≤0 := by nlinarith only [hscaled,hpoly]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hn.le hnum)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem ratio_below_radius {r t : ℝ} (hr : r∈Ioc (0:ℝ) (73/100))
    (ht : t∈Icc 0 frameCap) : ratioModel r t<R := by
  have hm := ratio_antitone hr (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht ht.1
  have hzero : ratioModel r 0=(Real.sqrt (1+r^2))^3 := by
    simp [ratioModel,pairNorm,pairEnergy,pairProduct,add_comm]
  rw [hzero] at hm
  have hn : 0<Real.sqrt (1+r^2) := Real.sqrt_pos.mpr (by positivity)
  have hn2 := Real.sq_sqrt (show 0≤1+r^2 by positivity)
  have hr2 := pow_le_pow_left₀ hr.1.le hr.2 2
  have hcube := pow_le_pow_left₀ (by positivity : 0≤1+r^2)
    (show 1+r^2≤1+(73/100:ℝ)^2 by linarith) 3
  have hpow : ((Real.sqrt (1+r^2))^3)^2=(1+r^2)^3 := by
    rw [←pow_mul,show (3:ℕ)*2=2*3 by norm_num,pow_mul,hn2]
  have htest : (1+(73/100:ℝ)^2)^3<qCap := by norm_num [qCap]
  have hR : 0<R := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hh : (Real.sqrt (1+r^2))^3<R := by nlinarith [radius_sq]
  exact hm.trans_lt hh

theorem larger_comparison {p q Q t : ℝ} (hp : 0<p) (hq : 0<q)
    (hqQ : q≤Q) (ht : t∈Icc 0 frameCap) : Ud p Q t≤Ud p q t := by
  have hm : AntitoneOn (fun q => Ud p q t) (Icc q Q) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro v hv
      exact (NegativeEH.HComparison.mixed_derivative hp (hq.trans_le hv.1)
        (by rw [abs_of_nonneg ht.1]; exact ht.2)).continuousAt.continuousWithinAt
    · intro v hv
      exact NegativeEH.HComparison.mixed_derivative hp (hq.trans hv.1)
        (by rw [abs_of_nonneg ht.1]; exact ht.2)
    · intro v hv
      have hcos := (NegativeESecant.cos_pos ht).le
      have hsin := (transport_trig ht).2.2.1
      have hv0 : 0≤v := (hq.trans hv.1).le
      change -NegativeEH.HComparison.mixed p v t≤0
      dsimp [NegativeEH.HComparison.mixed]
      positivity
  exact hm ⟨le_rfl,hqQ⟩ ⟨hqQ,le_rfl⟩ hqQ

def smallerFirst (p q t : ℝ) : ℝ :=
  Real.cos t-Real.sin t-R*q^2*Real.cos t*(q+p*Real.sin t)/(pairNorm p q t)^3

theorem smaller_derivative {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (fun p => Ud p q t) (smallerFirst p q t) p := by
  have hn := pairNorm_pos hp hq (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hn2 := pairNorm_sq hp hq (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hnorm : HasDerivAt (fun p => pairNorm p q t)
      ((p+q*Real.sin t)/pairNorm p q t) p := by
    simpa only [pairNorm_symm] using NegativeEH.HComparison.radial_norm_derivative hq hp
      (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hd := ((hasDerivAt_id p).const_mul (Real.cos t-Real.sin t)).sub
    (((hasDerivAt_id p).const_mul (R*q*Real.cos t)).div hnorm hn.ne')
  convert hd using 1
  · funext x
    dsimp [Ud,mixedPDerivative,normD1,pairProduct]
    simp only [sub_zero]
    ring
  · dsimp [smallerFirst,pairEnergy,pairProduct] at hn2 ⊢
    field_simp [hn.ne']
    nlinarith [congrArg (fun v : ℝ => R*q*Real.cos t*v) hn2]

theorem smallerFirst_negative {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (hr : p/q≤73/100) (ht : t∈Icc 0 frameCap) : smallerFirst p q t<0 := by
  have hratio : p/q∈Ioc (0:ℝ) (73/100) := ⟨div_pos hp hq,hr⟩
  have hh := ratio_below_radius hratio ht
  have hn := pairNorm_pos hratio.1 (by norm_num : (0:ℝ)<1)
    (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hc := NegativeESecant.cos_pos ht
  have hv : 0<1+(p/q)*Real.sin t := by
    have hsin := (transport_trig ht).2.2.1
    positivity
  have hclear := (div_lt_iff₀ (mul_pos hc hv)).1 hh
  have hhom : pairNorm p q t=q*pairNorm (p/q) 1 t := by
    simpa [hq.ne'] using pairNorm_homogeneous hq.le (p/q) 1 t
  have hid : smallerFirst p q t=Real.cos t-Real.sin t-
      R*Real.cos t*(1+(p/q)*Real.sin t)/(pairNorm (p/q) 1 t)^3 := by
    rw [smallerFirst,hhom]
    field_simp [hq.ne',hn.ne']
    ring
  rw [hid]
  have hdiv := (lt_div_iff₀ (pow_pos hn 3)).2 hclear
  linarith

theorem smaller_comparison {p t : ℝ} (hp : 0<p) (hpP : p≤pMax)
    (ht : t∈Icc 0 frameCap) : Ud pMax qMax t≤Ud p qMax t := by
  have hq : 0<qMax := by norm_num [qMax]
  have hm : AntitoneOn (fun p => Ud p qMax t) (Icc p pMax) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x hx => (smaller_derivative (hp.trans_le hx.1) hq ht).continuousAt.continuousWithinAt)
      (fun x hx => smaller_derivative (hp.trans hx.1) hq ht)
    intro x hx
    have hr : x/qMax≤73/100 := (div_le_iff₀ hq).2 (by dsimp [qMax,pMax] at *; linarith [hx.2])
    exact (smallerFirst_negative (hp.trans hx.1) hq hr ht).le
  exact hm ⟨le_rfl,hpP⟩ ⟨hpP,le_rfl⟩ hpP

/-- Equation (30), with the original two coefficients retained on the right. -/
theorem coefficient_comparison {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (hpP : p≤pMax) (hqQ : q≤qMax) (ht : t∈Icc 0 frameCap) :
    Ud pMax qMax t≤Ud p q t :=
  (smaller_comparison hp hpP ht).trans (larger_comparison hp hq hqQ ht)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowPositive
