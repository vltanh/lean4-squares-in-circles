module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2AffectedNorm

/-!
# The two affected positive-surplus curves

Uncompiled transcription of (33)--(36) in the angle companion. The
ordinary smaller-coordinate branch and the secant smaller-coordinate
branch are treated separately, retaining their common affected norm.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.AffectedPositiveCurves
open Candidate Secondary PositiveAngularEnvelope CorrelatedSameBlock SecantBaseline

def upper (r z s : ℝ) : ℝ :=
  1/Real.cos s+(13/12)*Real.tan s+r*(phi (s-z)-1)-R*AffectedNorm.norm r z (Real.tan s)
def lower (r z s : ℝ) : ℝ :=
  Real.cos z-Real.sin z+(13/12+phi z)*Real.tan s-R*AffectedNorm.norm r z (Real.tan s)
def upperFirst (r z s : ℝ) : ℝ :=
  (13/12+Real.sin s+r*Real.cos s^2*(Real.cos (s-z)-Real.sin (s-z))-
    R*AffectedNorm.first r z (Real.tan s))/Real.cos s^2
def lowerFirst (r z s : ℝ) : ℝ :=
  (13/12+phi z-R*AffectedNorm.first r z (Real.tan s))/Real.cos s^2

theorem upper_hasDerivAt {r z s : ℝ} (hv : 0<1-r*Real.sin z) (hc : 0<Real.cos s) :
    HasDerivAt (upper r z) (upperFirst r z s) s := by
  have hsec := SecantNormCurvature.secant_hasDerivAt hc.ne'
  have htan := Real.hasDerivAt_tan hc.ne'
  have hphi := (phi_hasDerivAt (s-z)).comp s ((hasDerivAt_id s).sub_const z)
  have hnorm := (AffectedNorm.norm_hasDerivAt (x:=Real.tan s) hv).comp s htan
  have hh := ((hsec.add (htan.const_mul (13/12:ℝ))).add
    ((hphi.sub_const 1).const_mul r)).sub (hnorm.const_mul R)
  convert hh using 1
  · rfl
  · dsimp [upperFirst,SecantNormCurvature.first]
    field_simp [hc.ne']
    ring

theorem lower_hasDerivAt {r z s : ℝ} (hv : 0<1-r*Real.sin z) (hc : 0<Real.cos s) :
    HasDerivAt (lower r z) (lowerFirst r z s) s := by
  have htan := Real.hasDerivAt_tan hc.ne'
  have hnorm := (AffectedNorm.norm_hasDerivAt (x:=Real.tan s) hv).comp s htan
  have hh := ((htan.const_mul (13/12+phi z)).const_add
    (Real.cos z-Real.sin z)).sub (hnorm.const_mul R)
  convert hh using 1
  · rfl
  · dsimp [lowerFirst]
    ring

theorem lower_identity {r z s : ℝ} (hc : Real.cos s≠0) :
    lower r z s=(1/Real.cos s)*phi (s-z)+(13/12)*Real.tan s-
      R*AffectedNorm.norm r z (Real.tan s) := by
  dsimp [lower,phi]
  rw [Real.cos_sub,Real.sin_sub,Real.tan_eq_sin_div_cos]
  field_simp [hc]
  ring

theorem quarter_phi_slope {t : ℝ} (ht : t∈Icc 0 (1/4:ℝ)) :
    (18/25:ℝ)<Real.cos t-Real.sin t := by
  have hh := trig_bracket (l:=0) (u:=(1/4:ℝ)) (by norm_num)
    (by linarith [Real.pi_gt_three]) ht
  norm_num at hh
  linarith [hh.2.1,hh.2.2.1]

theorem short_phi_slope {t : ℝ} (ht : t∈Icc 0 (19/50:ℝ)) :
    (557/1000:ℝ)<Real.cos t-Real.sin t := by
  have hh := trig_bracket (l:=0) (u:=(19/50:ℝ)) (by norm_num)
    (by linarith [Real.pi_gt_three]) ht
  norm_num at hh
  linarith [hh.2.1,hh.2.2.1]

theorem norm_first_upper {r s z D : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 s)
    (hD : R/denominator r s≤D) :
    R*AffectedNorm.first r z (Real.tan s)≤D*(Real.sin s+r*Real.cos s^2) := by
  have hfirst := mul_le_mul_of_nonneg_left (AffectedNorm.first_le_equal hr hs hz)
    (Real.sqrt_nonneg qCap)
  have hpos : 0≤Real.sin s+r*Real.cos s^2 :=
    add_nonneg (transport_trig hs).2.2.1 (mul_nonneg hr.1 (sq_nonneg _))
  have hh := mul_le_mul_of_nonneg_right hD hpos
  have he : R*((Real.sin s+r*Real.cos s^2)/denominator r s)=
      (R/denominator r s)*(Real.sin s+r*Real.cos s^2) := by ring
  rw [he] at hfirst
  exact hfirst.trans hh

theorem GA_upperFirst_positive {r s z : ℝ}
    (hr : r∈Icc (11/20:ℝ) (17/20:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) (hz : z∈Icc 0 s) :
    0<upperFirst r z s := by
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hrr : r∈Icc (0:ℝ) (71/50:ℝ) := ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have ht := trig_bracket (l:=0) (u:=(1/4:ℝ)) (by norm_num)
    (by linarith [Real.pi_gt_three]) hs
  have hcos : (121/125:ℝ)≤Real.cos s := by norm_num at ht; linarith [ht.2.2.1]
  have hsin : Real.sin s≤(31/125:ℝ) := by norm_num at ht; linarith [ht.2.1]
  have hc : 0<Real.cos s := by linarith
  have hcoef := coefficient_upper (r₀:=11/20) (c₀:=121/125) (D:=7/4)
    (by norm_num) (by norm_num) (by norm_num) hr.1 hcos (by norm_num [qCap])
  have hfirst := norm_first_upper hrr hsf hz hcoef.le
  have hphi := quarter_phi_slope (show s-z∈Icc 0 (1/4:ℝ) by
    exact ⟨by linarith [hz.2],by linarith [hs.2,hz.1]⟩)
  have hrc0 : 0≤r*Real.cos s^2 := mul_nonneg hrr.1 (sq_nonneg _)
  have hphim := mul_le_mul_of_nonneg_left hphi.le hrc0
  have hcos2 : Real.cos s^2≤1 := by
    nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.sin s)]
  have hrc : r*Real.cos s^2≤(17/20:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hcos2 hrr.1,hr.2]
  have hnum : 0<13/12+Real.sin s+r*Real.cos s^2*
      (Real.cos (s-z)-Real.sin (s-z))-R*AffectedNorm.first r z (Real.tan s) := by
    nlinarith
  exact div_pos hnum (sq_pos_of_pos hc)

def ABdenominator (r : ℝ) : ℝ := Real.sqrt (1+(861/1000)*r^2)
def ABcoefficient (r : ℝ) : ℝ := R/ABdenominator r

theorem ABdenominator_data (r : ℝ) :
    0<ABdenominator r ∧ (ABdenominator r)^2=1+(861/1000)*r^2 := by
  exact ⟨Real.sqrt_pos.mpr (by positivity),Real.sq_sqrt (by positivity)⟩

theorem ABcoefficient_one {r : ℝ} (hr : r∈Icc (4/5:ℝ) (27/25:ℝ)) :
    1<ABcoefficient r := by
  have hn := ABdenominator_data r
  have hr0 : 0≤r := by linarith [hr.1]
  have hr2 := pow_le_pow_left₀ hr0 hr.2 2
  have hR0 : 0≤R := Real.sqrt_nonneg qCap
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  unfold ABcoefficient
  apply (lt_div_iff₀ hn.1).2
  norm_num [qCap] at hR2
  nlinarith [hn.2]

theorem ABcoefficient_bound {r s : ℝ} (hcos : (861/1000:ℝ)≤Real.cos s^2) :
    R/denominator r s≤ABcoefficient r := by
  have hn := ABdenominator_data r
  have hd := denominator_pos r s
  have hmul := mul_le_mul_of_nonneg_left hcos (sq_nonneg r)
  have hdn : ABdenominator r≤denominator r s := by
    nlinarith [hn.2,denominator_sq r s]
  exact div_le_div₀ (Real.sqrt_nonneg qCap) le_rfl hn.1 hdn

theorem AB_positive_reserve {r : ℝ} (hr : r∈Icc (4/5:ℝ) (27/25:ℝ)) :
    0<13/12+371/1000+(557/1000)*r-ABcoefficient r*(371/1000+r) := by
  have hn := ABdenominator_data r
  have hr0 : 0≤r := by linarith [hr.1]
  have hR0 : 0≤R := Real.sqrt_nonneg qCap
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hpoly := PositivePolynomial.PA_positive hr
  have hsq : (R*(371/1000+r))^2<
      ((13/12+371/1000+(557/1000)*r)*ABdenominator r)^2 := by
    rw [mul_pow,mul_pow,hR2,hn.2]
    nlinarith only [hpoly]
  have hcross : R*(371/1000+r)<
      (13/12+371/1000+(557/1000)*r)*ABdenominator r := by
    have hleft : 0≤R*(371/1000+r) := by positivity
    have hright : 0≤(13/12+371/1000+(557/1000)*r)*ABdenominator r := by positivity
    nlinarith
  have hh := (div_lt_iff₀ hn.1).2 hcross
  have he : R*(371/1000+r)/ABdenominator r=ABcoefficient r*(371/1000+r) := by
    dsimp [ABcoefficient]
    ring
  rw [he] at hh
  linarith

theorem AB_upperFirst_positive {r s z : ℝ}
    (hr : r∈Icc (4/5:ℝ) (27/25:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) (hz : z∈Icc 0 s) :
    0<upperFirst r z s := by
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hrr : r∈Icc (0:ℝ) (71/50:ℝ) := ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have ht := trig_bracket (l:=0) (u:=(19/50:ℝ)) (by norm_num)
    (by linarith [Real.pi_gt_three]) hs
  have hcos : (116/125:ℝ)<Real.cos s := by norm_num at ht; linarith [ht.2.2.1]
  have hsin : Real.sin s≤(371/1000:ℝ) := by norm_num at ht; linarith [ht.2.1]
  have hc : 0<Real.cos s := by linarith
  have hc2 : (861/1000:ℝ)≤Real.cos s^2 := by nlinarith
  have hcoef := ABcoefficient_bound (r:=r) hc2
  have hfirst := norm_first_upper hrr hsf hz hcoef
  have hphi := short_phi_slope (show s-z∈Icc 0 (19/50:ℝ) by
    exact ⟨by linarith [hz.2],by linarith [hs.2,hz.1]⟩)
  have hrc0 : 0≤r*Real.cos s^2 := mul_nonneg hrr.1 (sq_nonneg _)
  have hphim := mul_le_mul_of_nonneg_left hphi.le hrc0
  have hcos2 : Real.cos s^2≤1 := by
    nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.sin s)]
  have hrc := mul_le_mul_of_nonneg_left hcos2 hrr.1
  have hD := ABcoefficient_one hr
  have hscharge := mul_le_mul_of_nonneg_left hsin (show 0≤ABcoefficient r-1 by linarith)
  have hrcharge := mul_le_mul_of_nonneg_left hrc
    (show 0≤ABcoefficient r-557/1000 by linarith)
  have hreserve := AB_positive_reserve hr
  have hnum : 0<13/12+Real.sin s+r*Real.cos s^2*
      (Real.cos (s-z)-Real.sin (s-z))-R*AffectedNorm.first r z (Real.tan s) := by
    nlinarith
  exact div_pos hnum (sq_pos_of_pos hc)

theorem lowerFirst_positive {r s z : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hz : z∈Icc 0 frameCap) (hc : 0<Real.cos s) :
    0<lowerFirst r z s := by
  have hfirst := mul_le_mul_of_nonneg_left
    (AffectedNorm.first_le_one (x:=Real.tan s) (AffectedNorm.second_coordinate_pos hr hz))
    (Real.sqrt_nonneg qCap)
  have hphi := one_le_phi hz
  have hR := Curvature.radius_bounds.2
  have hnum : 0<13/12+phi z-R*AffectedNorm.first r z (Real.tan s) := by linarith
  exact div_pos hnum (sq_pos_of_pos hc)

theorem GA_upper_monotone {r z : ℝ}
    (hr : r∈Icc (11/20:ℝ) (17/20:ℝ)) (hz : z∈Icc 0 (1/4:ℝ)) :
    MonotoneOn (upper r z) (Icc z (1/4:ℝ)) := by
  have hrr : r∈Icc (0:ℝ) (71/50:ℝ) := ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hzf : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hv := AffectedNorm.second_coordinate_pos hrr hzf
  have hd (s : ℝ) (hs : s∈Icc z (1/4:ℝ)) := upper_hasDerivAt hv
    (s:=s) (show 0<Real.cos s by
      have hsf : s∈Icc 0 frameCap := ⟨hz.1.trans hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
      linarith [(transport_trig hsf).1])
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  intro s hs
  exact (GA_upperFirst_positive hr ⟨by linarith [hz.1,hs.1],hs.2.le⟩ ⟨hz.1,hs.1.le⟩).le

theorem AB_upper_monotone {r z : ℝ}
    (hr : r∈Icc (4/5:ℝ) (27/25:ℝ)) (hz : z∈Icc 0 (19/50:ℝ)) :
    MonotoneOn (upper r z) (Icc z (19/50:ℝ)) := by
  have hrr : r∈Icc (0:ℝ) (71/50:ℝ) := ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hzf : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hv := AffectedNorm.second_coordinate_pos hrr hzf
  have hd (s : ℝ) (hs : s∈Icc z (19/50:ℝ)) := upper_hasDerivAt hv
    (s:=s) (show 0<Real.cos s by
      have hsf : s∈Icc 0 frameCap := ⟨hz.1.trans hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
      linarith [(transport_trig hsf).1])
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  intro s hs
  exact (AB_upperFirst_positive hr ⟨by linarith [hz.1,hs.1],hs.2.le⟩ ⟨hz.1,hs.1.le⟩).le

theorem lower_monotone {r z : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hz : z∈Icc 0 (19/50:ℝ)) :
    MonotoneOn (lower r z) (Icc z (19/50:ℝ)) := by
  have hzf : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hv := AffectedNorm.second_coordinate_pos hr hzf
  have hc (s : ℝ) (hs : s∈Icc z (19/50:ℝ)) : 0<Real.cos s := by
    have hsf : s∈Icc 0 frameCap := ⟨hz.1.trans hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
    linarith [(transport_trig hsf).1]
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (lower_hasDerivAt hv (hc s hs)).continuousAt.continuousWithinAt)
    (fun s hs => lower_hasDerivAt hv (hc s (Ioo_subset_Icc_self hs)))
  intro s hs
  exact (lowerFirst_positive hr hzf (hc s (Ioo_subset_Icc_self hs))).le

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.AffectedPositiveCurves
