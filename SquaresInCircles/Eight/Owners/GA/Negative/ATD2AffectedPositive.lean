module

public import SquaresInCircles.Eight.Owners.GA.HybridConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowNegativeComparison
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2CurvatureConstants
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2CutData
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowPositiveCoefficients
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowABSlope
public import SquaresInCircles.Eight.Owners.GA.Positive.TDStress

/-!
# Eight squares: original affected-pair positive surplus reduces to equal angles

The normalized curves are exact identities for the original
secant weights. The AB minimum keeps both possible orders of its two
coefficients, and both branches agree when those coefficients coincide.
-/

section
/-!
## The two affected positive-surplus curves

The
ordinary smaller-coordinate branch and the secant smaller-coordinate
branch are treated separately, retaining their common affected norm.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedPositiveCurves
open Candidate Secondary PositiveAngularEnvelope CorrelatedSameBlock SecantBaseline

def upper (r z s : ℝ) : ℝ :=
  1/Real.cos s+(13/12)*Real.tan s+r*(PositiveAngularEnvelope.phi (s-z)-1)-R*AffectedNorm.norm r z (Real.tan s)
def lower (r z s : ℝ) : ℝ :=
  Real.cos z-Real.sin z+(13/12+PositiveAngularEnvelope.phi z)*Real.tan s-R*AffectedNorm.norm r z (Real.tan s)
def upperFirst (r z s : ℝ) : ℝ :=
  (13/12+Real.sin s+r*Real.cos s^2*(Real.cos (s-z)-Real.sin (s-z))-
    R*AffectedNorm.first r z (Real.tan s))/Real.cos s^2
def lowerFirst (r z s : ℝ) : ℝ :=
  (13/12+PositiveAngularEnvelope.phi z-R*AffectedNorm.first r z (Real.tan s))/Real.cos s^2

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
  have hh := ((htan.const_mul (13/12+PositiveAngularEnvelope.phi z)).const_add
    (Real.cos z-Real.sin z)).sub (hnorm.const_mul R)
  convert hh using 1
  · rfl
  · dsimp [lowerFirst]
    ring

theorem lower_identity {r z s : ℝ} (hc : Real.cos s≠0) :
    lower r z s=(1/Real.cos s)*PositiveAngularEnvelope.phi (s-z)+(13/12)*Real.tan s-
      R*AffectedNorm.norm r z (Real.tan s) := by
  dsimp [lower,PositiveAngularEnvelope.phi]
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
  have hlt : ABdenominator r^2<R^2 := by
    rw [hn.2,hR2]
    norm_num [qCap]
    nlinarith
  unfold ABcoefficient
  rw [one_lt_div hn.1]
  exact lt_of_pow_lt_pow_left₀ 2 hR0 hlt

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
    have hleft : 0≤R*(371/1000+r) := mul_nonneg hR0 (by linarith)
    have hright : 0≤(13/12+371/1000+(557/1000)*r)*ABdenominator r :=
      mul_nonneg (by linarith) hn.1.le
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
  have hnum : 0<13/12+PositiveAngularEnvelope.phi z-R*AffectedNorm.first r z (Real.tan s) := by linarith
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

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedPositiveCurves
end
end
end

section
/-!
## Pure positive surplus in an unaffected pair

Both coefficient families and the linear term of D are included. The secant assignment of the
cycle is kept; only the unaffected pair stays constant as `s` decreases to `z`
(`reduces_to_equal`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.UnaffectedPositive
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate (Family)
open Explicit SecantBaseline

def affectedIndex (atG : Bool) : Fin 4 := if atG then 1 else 2
def p₀ (f : Family) (z : ℝ) : Fin 4→ℝ := ![k f z,k f z,min (l f z) (m f z),k f z]
def q₀ (f : Family) (z : ℝ) : Fin 4→ℝ := ![1,l f z,max (l f z) (m f z),1]

theorem zero_weights (f : Family) (atG : Bool) (z : ℝ) :
    Source.pWeights atG (k f z) (l f z) (m f z) 0=p₀ f z ∧
    Source.qWeights atG (k f z) (l f z) (m f z) 0=q₀ f z := by
  cases atG <;> simp [Source.pWeights,Source.qWeights,p₀,q₀,lambdaG,lambdaB,
    NegativeAPositiveTD.secant]

theorem unaffected_weights (f : Family) (atG : Bool) (s z : ℝ) (i : Fin 4)
    (hi : i≠affectedIndex atG) :
    Source.pWeights atG (k f z) (l f z) (m f z) s i=p₀ f z i ∧
    Source.qWeights atG (k f z) (l f z) (m f z) s i=q₀ f z i := by
  cases atG <;> fin_cases i <;>
    simp [affectedIndex,Source.pWeights,Source.qWeights,p₀,q₀,lambdaG,lambdaB] at hi ⊢

theorem zero_pair_domain (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4) :
    0<p₀ f z i ∧ p₀ f z i≤q₀ f z i ∧ q₀ f z i≤2*p₀ f z i := by
  have hh := ordered_pair_domain f true hz
    (show (0:ℝ)∈Icc 0 (angleCut true) by norm_num [angleCut]) i
  rw [(zero_weights f true z).1,(zero_weights f true z).2] at hh
  exact hh

theorem zero_q_bounds (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4) :
    1≤q₀ f z i ∧ q₀ f z i≤(71/50)*l f z := by
  have hb := family_basic_domain f hz
  have hllo := hb.2.2.1
  have hmhi := hb.2.2.2.2.2.2
  fin_cases i
  · show (1:ℝ)≤1 ∧ (1:ℝ)≤(71/50)*l f z
    exact ⟨le_rfl,by linarith⟩
  · show 1≤l f z ∧ l f z≤(71/50)*l f z
    exact ⟨hllo.le,by linarith⟩
  · show 1 ≤ max (l f z) (m f z) ∧ max (l f z) (m f z)≤(71/50)*l f z
    exact ⟨hllo.le.trans (le_max_left _ _),max_le (by linarith) hmhi.le⟩
  · show (1:ℝ)≤1 ∧ (1:ℝ)≤(71/50)*l f z
    exact ⟨le_rfl,by linarith⟩

theorem AB_unaffected_q_bound (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4)
    (hi : i≠affectedIndex false) : q₀ f z i≤l f z := by
  have hllo := (family_basic_domain f hz).2.2.1
  fin_cases i <;> simp [affectedIndex,q₀] at hi ⊢ <;> linarith

theorem GA_slope (f : Family) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (1/4:ℝ)) :
    (897/1000)*l f z<angleSlope (l f z) (basicRatio true (k f z) (l f z) (c f z) z) s := by
  have hb := family_basic_domain f hz
  have hl : 0<l f z := by linarith [hb.2.2.1]
  have ht := trig_bracket (l:=0) (u:=(1/4:ℝ)) (by norm_num)
    (by linarith [Real.pi_gt_three]) hs
  have hcos : (121/125:ℝ)<Real.cos s := by norm_num at ht; linarith [ht.2.2.1]
  have hsin : Real.sin s<(31/125:ℝ) := by norm_num at ht; linarith [ht.2.1]
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hratio : (11/20:ℝ)≤basicRatio true (k f z) (l f z) (c f z) z := by
    dsimp [basicRatio,affected]
    exact (le_div_iff₀ hl).2 hb.2.2.2.2.1.le
  have hc := coefficient_upper (r₀:=11/20) (c₀:=121/125) (D:=7/4)
    (by norm_num) (by norm_num) (by norm_num) hratio hcos.le
    (by norm_num [qCap])
  exact slope_lower hl (by linarith) (transport_trig hsf).2.2.1 hsin.le
    (by norm_num) (by norm_num) hc.le (by norm_num)

theorem AB_ratio_after_equal (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hzcut : z≤19/50) : (4/5)*l f z< m f z := by
  cases f
  · have hz' : z∈Icc (0:ℝ) (1/5) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split] at hz
      exact hz
    have hh := low_tilted hz'
    have hl := (low_ranges hz').2.2.1
    linarith [hh.1]
  · have hz' : z∈Icc (1/5:ℝ) (7/10) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split,
        PositiveTD.Certificate.h] at hz
      exact hz
    exact high_tilted_lower_to_AB_cut ⟨hz'.1,hzcut⟩

theorem AB_slope (f : Family) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (19/50:ℝ)) (hzs : z≤ s) :
    (43/50)*l f z<angleSlope (l f z) (basicRatio false (k f z) (l f z) (c f z) z) s := by
  have hl : 0<l f z := (family_positive f hz).2.1
  have ht := trig_bracket (l:=0) (u:=(19/50:ℝ)) (by norm_num)
    (by linarith [Real.pi_gt_three]) hs
  have hcos : (116/125:ℝ)<Real.cos s := by norm_num at ht; linarith [ht.2.2.1]
  have hsin : Real.sin s<(371/1000:ℝ) := by norm_num at ht; linarith [ht.2.1]
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hratio : (4/5:ℝ)≤basicRatio false (k f z) (l f z) (c f z) z := by
    change (4/5:ℝ)≤ m f z/l f z
    exact (le_div_iff₀ hl).2 (AB_ratio_after_equal f hz (hzs.trans hs.2)).le
  have hc := coefficient_upper (r₀:=4/5) (c₀:=116/125) (D:=8/5)
    (by norm_num) (by norm_num) (by norm_num) hratio hcos.le
    (by norm_num [qCap])
  exact slope_lower hl (by linarith) (transport_trig hsf).2.2.1 hsin.le
    (by norm_num) (by norm_num) hc.le (by norm_num)

def positiveD (f : Family) (z : ℝ) (i : Fin 4) (t : ℝ) : ℝ :=
  if i=3 then -(GlobalGA.Secondary.diagonal-1/2) else PositiveSlope.Ud (p₀ f z i) (q₀ f z i) t
def curve (f : Family) (atG : Bool) (z : ℝ) (i : Fin 4) (s : ℝ) : ℝ :=
  angularBaseline atG (k f z) (l f z) (c f z) s z+
    PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2) (p₀ f z) (q₀ f z) 3 i (s-z)

theorem positive_hasDerivAt (f : Family) {z t : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (ht : t∈Icc 0 frameCap) (i : Fin 4) :
    HasDerivAt (PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2) (p₀ f z) (q₀ f z) 3 i)
      (positiveD f z i t) t := by
  by_cases hi : i=3
  · have he : PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2) (p₀ f z) (q₀ f z) 3 i=
        fun P => -(GlobalGA.Secondary.diagonal-1/2)*P := by
      funext P; simp [PositiveTD.Hybrid.positive,hi]
    have hd : positiveD f z i t=-(GlobalGA.Secondary.diagonal-1/2) := by
      simp [positiveD,hi]
    rw [he,hd]
    simpa using (hasDerivAt_id t).const_mul (-(GlobalGA.Secondary.diagonal-1/2))
  · have hp := zero_pair_domain f hz i
    have hd : positiveD f z i t=PositiveSlope.Ud (p₀ f z i) (q₀ f z i) t := by
      simp [positiveD,hi]
    rw [hd]
    convert PositiveSlope.U_hasDerivAt hp.1 (hp.1.trans_le hp.2.1) ht using 1
    funext P; simp [PositiveTD.Hybrid.positive,hi]

theorem positiveD_lower (f : Family) {z t : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (ht : t∈Icc 0 (19/50:ℝ)) (i : Fin 4) :
    -(3/5)*q₀ f z i<positiveD f z i t := by
  by_cases hi : i=3
  · simp only [positiveD,ite_eq_left hi]
    have hq := (zero_q_bounds f hz i).1
    linarith [diagonal_bounds.2]
  · simp only [positiveD,ite_eq_right hi]
    have hp := zero_pair_domain f hz i
    exact PositiveSlope.short_bound hp.1 hp.2.1 hp.2.2 ht

theorem curve_hasDerivAt (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc z (angleCut atG)) (i : Fin 4) :
    HasDerivAt (curve f atG z i)
      (angleSlope (l f z) (basicRatio atG (k f z) (l f z) (c f z) z) s+
        positiveD f z i (s-z)) s := by
  have hzf := family_frame_domain f hz
  have hss : s∈Icc 0 (angleCut atG) := ⟨hzf.1.trans hs.1,hs.2⟩
  have hsf := (angle_domain atG hss).2
  have hdiff : s-z∈Icc 0 frameCap :=
    ⟨by linarith [hs.1],by linarith [hsf.2,hzf.1]⟩
  have hbase := angularBaseline_hasDerivAt atG (k:=k f z) (c:=c f z) (z:=z)
    (family_positive f hz).2.1
    (show 0<Real.cos s by linarith [(transport_trig hsf).1])
  have hpos := (positive_hasDerivAt f hz hdiff i).comp s ((hasDerivAt_id s).sub_const z)
  rw [mul_one] at hpos
  exact hbase.add hpos

theorem curve_monotone (f : Family) (atG : Bool) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) (i : Fin 4)
    (hi : i≠affectedIndex atG) : MonotoneOn (curve f atG z i) (Icc z (angleCut atG)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (curve_hasDerivAt f atG hz hs i).continuousAt.continuousWithinAt)
    (fun s hs => curve_hasDerivAt f atG hz (Ioo_subset_Icc_self hs) i)
  intro s hs
  have hzf := family_frame_domain f hz
  have hss : s∈Icc 0 (angleCut atG) := ⟨by linarith [hzf.1,hs.1],hs.2.le⟩
  have hshort := (angle_domain atG hss).1
  have hdiff : s-z∈Icc 0 (19/50:ℝ) :=
    ⟨by linarith [hs.1],by linarith [hshort.2,hzf.1]⟩
  have hpos := positiveD_lower f hz hdiff i
  have hl := (family_positive f hz).2.1
  cases atG
  · have hb := AB_slope f hz hss hs.1.le
    have hq := AB_unaffected_q_bound f hz i hi
    linarith
  · have hb := GA_slope f hz hss
    have hq := (zero_q_bounds f hz i).2
    linarith

theorem reduces_to_equal (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (hzs : z≤ s) (i : Fin 4)
    (hi : i≠affectedIndex atG) :
    baseline atG (k f z) (l f z) (c f z) z z≤
      baseline atG (k f z) (l f z) (c f z) s z+
        PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2)
          (Source.pWeights atG (k f z) (l f z) (m f z) s)
          (Source.qWeights atG (k f z) (l f z) (m f z) s) 3 i (s-z) := by
  have hzf := family_frame_domain f hz
  have hm := curve_monotone f atG hz i hi
    (show z∈Icc z (angleCut atG) from ⟨le_rfl,hzs.trans hs.2⟩)
    (show s∈Icc z (angleCut atG) from ⟨hzs,hs.2⟩) hzs
  obtain ⟨hp,hq⟩ := unaffected_weights f atG s z i hi
  rw [baseline_eq_extension atG _ _ _ _ hzf,
    baseline_eq_extension atG _ _ _ _ (angle_domain atG hs).2]
  dsimp [curve] at hm
  simp only [sub_self,PositiveTD.Hybrid.positive,U_zero,mul_zero,ite_self,add_zero] at hm
  simpa only [PositiveTD.Hybrid.positive,hp,hq] using hm

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.UnaffectedPositive
end
end
end

section
/-!
## The weighted stress of a negative flat A with TD2

The rotation of the negative A is collected with its secant weight in an identity
(`decomposition`). The stress uses the separators and the points of the cycle as they are
(`stress_nonpositive`, `original_stress_lower`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

def actualStress (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c s : ℝ) : ℝ :=
  demand C (weights atG k l c s (delta C.theta T))-
    ∑ i,work (force C (owners hg atG) (weights atG k l c s (delta C.theta T)) i) (C.point i)
def actualBlocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c s : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg atG k l c s 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg atG k l c s 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg atG k l c s 2) (C.point B).reflect,
    PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect]

theorem decomposition (C : SignedCycle) {hg : Fin 4} (atG : Bool) (k l c : ℝ) {s : ℝ}
    (hhg : hg=0 ∨ hg=2) (hs : s∈Icc 0 frameCap)
    (ha : aError C atG=-s) (hflat : (C.point A).a=7/12) :
    actualStress C hg atG k l c s=
      baseline atG k l c s (delta C.theta T)+
        (∑ i,actualBlocks C hg atG k l c s i)+PositiveTD.tReserve C c := by
  have hcos : Real.cos s≠0 := (show 0<Real.cos s by
    linarith [(transport_trig hs).1]).ne'
  simp only [A] at hflat
  cases atG <;> rcases hhg with rfl | rfl <;>
    simp only [aError,Bool.false_eq_true,↓reduceIte,G,A] at ha <;>
    simp [actualStress,demand,force,source,target,work,add,scale,previous,
      owners,weights,blocks,actualBlocks,PositiveTD.actualPairIncrement,
      PositiveTD.actualDIncrement,pairF,pairG,PositiveTD.tReserve,baseline,
      PositiveTD.tilted,lambdaG,lambdaB,secant,Real.tan_eq_sin_div_cos,
      Fin.sum_univ_succ,word,H,G,A,B,T,D,E,SignedPoint.reflect,ha,hflat] <;>
    field_simp [hcos] <;> ring

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (atG : Bool) {k l c s : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c)
    (hs : s∈Icc 0 frameCap) (hz : delta C.theta T∈Icc 0 frameCap)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    actualStress C hg atG k l c s≤0 := by
  have hf (i : Vertex) : C.Feasible i (owners hg atG i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation (weights_nonnegative atG hk hl hc hs hz) hf)

theorem block_family_lower {q k l c s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hsorted : ∀ i,(C.point i).Sorted) (hcontained : ∀ i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (hs : 0≤ s)
    (ha : aError C atG=-s) (hz : 0≤delta C.theta T)
    (hk : k∈Icc (1/2:ℝ) (17/20:ℝ))
    (hG : lambdaG atG l s∈Icc k (2*k)) (hB : 0<lambdaB atG l s)
    (hcoef : c∈Icc k 2)
    (hratio : lambdaB atG l s≤2*PositiveTD.tilted c (delta C.theta T) ∧
      PositiveTD.tilted c (delta C.theta T)≤2*lambdaB atG l s) (i : Fin 4) :
    PositiveTD.Hybrid.block R (GlobalGA.Secondary.diagonal-1/2)
      (pWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s)
      (qWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s) 3 i
      (blocks C hg atG k l c s i).P (blocks C hg atG k l c s i).N≤
        actualBlocks C hg atG k l c s i := by
  have hz' := (original_budgets hg atG k l c hs ha hvar hz).1
  have hc0 : 0<c := by linarith [hk.1,hcoef.1]
  have hm := PositiveTD.tilted_pos hc0 hz'
  have hcoeff := coefficient_domain hk hG hB hm hratio
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R (pWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s j)
        (qWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s j)
        (blocks C hg atG k l c s j).P (blocks C hg atG k l c s j).N≤
          PositiveTD.actualPairIncrement (blocks C hg atG k l c s j) P := by
    have hd := block_coefficients (C:=C) (hg:=hg) (atG:=atG) (c:=c)
      (show k≤1 by linarith [hk.2]) hG.1 j
    have hp : 0≤(blocks C hg atG k l c s j).p := by rw [hd.1]; exact (hcoeff j).1.le
    have hb := block_budgets hg atG k l c hs ha hvar hz j
    have hh := PositiveTD.actual_block_minorant hy hP hq hp hb.1 hb.2
    rw [hd.1,hd.2] at hh
    exact hh
  fin_cases i
  · simpa [PositiveTD.Hybrid.block,actualBlocks] using hordinary 0 hHy (hcontained H)
  · simpa [PositiveTD.Hybrid.block,actualBlocks] using hordinary 1
      (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hcontained G)
  · simpa [PositiveTD.Hybrid.block,actualBlocks] using hordinary 2
      (P:=(C.point B).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hcontained B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
    have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect)
      (by simpa using hsorted D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hcontained D) hq hk hcoef (original_error_bound hvar hn D)
    simpa [PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,pWeights,qWeights] using hh

theorem original_stress_lower {q k l c s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hsorted : ∀ i,(C.point i).Sorted) (hcontained : ∀ i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (hs : s∈Icc 0 frameCap)
    (ha : aError C atG=-s) (hflat : (C.point A).a=7/12)
    (hz : 0≤delta C.theta T) (hhg : hg=0 ∨ hg=2)
    (hk : k∈Icc (1/2:ℝ) (17/20:ℝ))
    (hG : lambdaG atG l s∈Icc k (2*k)) (hB : 0<lambdaB atG l s)
    (hcoef : c∈Icc k 2)
    (hratio : lambdaB atG l s≤2*PositiveTD.tilted c (delta C.theta T) ∧
      PositiveTD.tilted c (delta C.theta T)≤2*lambdaB atG l s) :
    baseline atG k l c s (delta C.theta T)+
      (∑ i,PositiveTD.Hybrid.block R (GlobalGA.Secondary.diagonal-1/2)
        (pWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s)
        (qWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s) 3 i
        (blocks C hg atG k l c s i).P (blocks C hg atG k l c s i).N)≤
          actualStress C hg atG k l c s := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    block_family_lower (hg:=hg) atG hsorted hcontained hq hHy hGy hBy hDy hvar hs.1 ha hz
      hk hG hB hcoef hratio i)
  have hT := PositiveTD.tReserve_nonneg (hsorted T) (hcontained T) hq
    (show 0≤c by linarith [hk.1,hcoef.1])
    (original_budgets hg atG k l c hs.1 ha hvar hz).1
  rw [decomposition C atG k l c hhg hs ha hflat]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Source
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedPositive
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeEnvelope
open SecantBaseline AffectedPositiveCurves
open Certificate (Family)

def value (atG : Bool) (k l c s z : ℝ) : ℝ :=
  baseline atG k l c s z+
    if atG then U R k (NegativeAPositiveTD.secant l s) (s-z)
    else U R (min (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z))
      (max (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z)) (s-z)

theorem rotation_unit_norm {r s z : ℝ} (hc : 0<Real.cos s) :
    pairNorm r (1/Real.cos s) (s-z)=AffectedNorm.norm r z (Real.tan s) := by
  have ht := AffectedNorm.tan_identity hc
  have hsin : (1/Real.cos s)*Real.sin (s-z)=Real.tan s*Real.cos z-Real.sin z := by
    rw [Real.sin_sub,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
  have hsin' := congrArg (fun x : ℝ => 2*r*x) hsin
  have he : r^2+(1/Real.cos s)^2+2*r*(1/Real.cos s)*Real.sin (s-z)=
      (AffectedNorm.norm r z (Real.tan s))^2 := by
    rw [AffectedNorm.norm_sq_expanded]
    nlinarith only [ht.2,hsin']
  dsimp [pairNorm]
  rw [he,Real.sqrt_sq (show 0≤AffectedNorm.norm r z (Real.tan s) from Real.sqrt_nonneg _)]

theorem rotation_norm {l s : ℝ} (hl : 0<l) (hc : 0<Real.cos s) (a z : ℝ) :
    pairNorm a (NegativeAPositiveTD.secant l s) (s-z)=
      l*AffectedNorm.norm (a/l) z (Real.tan s) := by
  have hh := pairNorm_homogeneous hl.le (a/l) (1/Real.cos s) (s-z)
  rw [show l*(a/l)=a by field_simp [hl.ne'],
    show l*(1/Real.cos s)=NegativeAPositiveTD.secant l s by
      dsimp [NegativeAPositiveTD.secant]; ring,
    rotation_unit_norm hc] at hh
  exact hh

theorem zero_norm {l : ℝ} (hl : 0<l) (a : ℝ) :
    pairNorm a l 0=l*OrdinaryCurvatureBounds.shape (a/l) := by
  have hh := FlatTStress.zero_norm_scale hl a 1
  simpa [OrdinaryCurvatureBounds.shape,add_comm] using hh

theorem GA_identity {k l c s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    value true k l c s z=baseline true k l c 0 z+
      l*(upper (k/l) z s-1+R*OrdinaryCurvatureBounds.shape (k/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [value,baseline_eq_extension true k l c z hs]
  simp only [angularBaseline,affected,↓reduceIte,FlatTStress.secantCharge,U]
  rw [rotation_norm hl hc k z,zero_norm hl k]
  dsimp [upper,NegativeAPositiveTD.secant]
  field_simp [hl.ne']
  ring

theorem branch_difference {r s z : ℝ} (hc : Real.cos s≠0) :
    upper r z s-lower r z s=(r-1/Real.cos s)*(PositiveAngularEnvelope.phi (s-z)-1) := by
  rw [lower_identity hc]
  dsimp [upper]
  ring

theorem AB_identity {k l c s z : ℝ} (hl : 0<l)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 s) :
    value false k l c s z=baseline false k l c 0 z+
      l*(min (upper (PositiveTD.tilted c z/l) z s)
        (lower (PositiveTD.tilted c z/l) z s)-1+
          R*OrdinaryCurvatureBounds.shape (PositiveTD.tilted c z/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hdiff : s-z∈Icc 0 frameCap :=
    ⟨by linarith [hz.2],by linarith [hs.2,hz.1]⟩
  have hphi : 0≤PositiveAngularEnvelope.phi (s-z)-1 := sub_nonneg.mpr (CorrelatedSameBlock.one_le_phi hdiff)
  have hbranch := branch_difference (r:=PositiveTD.tilted c z/l) (z:=z) hc.ne'
  rcases le_total (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z) with hle | hle
  · have hr : 1/Real.cos s≤PositiveTD.tilted c z/l := by
      apply (le_div_iff₀ hl).2
      dsimp [NegativeAPositiveTD.secant] at hle
      rw [show 1/Real.cos s*l=l/Real.cos s by ring]
      exact hle
    have hh := mul_nonneg (sub_nonneg.mpr hr) hphi
    have hmin : lower (PositiveTD.tilted c z/l) z s≤upper (PositiveTD.tilted c z/l) z s := by
      linarith
    rw [min_eq_right hmin,value,baseline_eq_extension false k l c z hs]
    simp only [angularBaseline,affected,Bool.false_eq_true,↓reduceIte,FlatTStress.secantCharge,
      min_eq_left hle,max_eq_right hle,U]
    simp only [pairNorm_symm (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z)]
    rw [rotation_norm hl hc (PositiveTD.tilted c z) z,zero_norm hl (PositiveTD.tilted c z),
      lower_identity hc.ne']
    dsimp [NegativeAPositiveTD.secant]
    field_simp [hl.ne']
    ring
  · have hr : PositiveTD.tilted c z/l≤1/Real.cos s := by
      apply (div_le_iff₀ hl).2
      dsimp [NegativeAPositiveTD.secant] at hle
      rw [show 1/Real.cos s*l=l/Real.cos s by ring]
      exact hle
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) hphi
    have hmin : upper (PositiveTD.tilted c z/l) z s≤lower (PositiveTD.tilted c z/l) z s := by
      linarith
    rw [min_eq_left hmin,value,baseline_eq_extension false k l c z hs]
    simp only [angularBaseline,affected,Bool.false_eq_true,↓reduceIte,FlatTStress.secantCharge,
      min_eq_right hle,max_eq_left hle,U]
    rw [rotation_norm hl hc (PositiveTD.tilted c z) z,zero_norm hl (PositiveTD.tilted c z)]
    dsimp [upper,NegativeAPositiveTD.secant]
    field_simp [hl.ne']
    ring

theorem AB_min_monotone {r z : ℝ}
    (hr : r∈Icc (4/5:ℝ) (71/50:ℝ)) (hz : z∈Icc 0 (19/50:ℝ)) :
    MonotoneOn (fun s => min (upper r z s) (lower r z s)) (Icc z (19/50:ℝ)) := by
  have hrr : r∈Icc (0:ℝ) (71/50:ℝ) := ⟨by linarith [hr.1],hr.2⟩
  have hlow := lower_monotone hrr hz
  by_cases hsmall : r≤(27/25:ℝ)
  · have hu := AB_upper_monotone ⟨hr.1,hsmall⟩ hz
    intro x hx y hy hxy
    exact min_le_min (hu hx hy hxy) (hlow hx hy hxy)
  · have he (s : ℝ) (hs : s∈Icc z (19/50:ℝ)) :
        min (upper r z s) (lower r z s)=lower r z s := by
      have hss : s∈Icc 0 (19/50:ℝ) := ⟨hz.1.trans hs.1,hs.2⟩
      have hcos := Explicit.AB_cut_cosine hss
      have hc : 0<Real.cos s := by linarith
      have hw : 1/Real.cos s≤(27/25:ℝ) := by
        apply (div_le_iff₀ hc).2
        linarith
      have hphi : 0≤PositiveAngularEnvelope.phi (s-z)-1 := by
        apply sub_nonneg.mpr
        apply CorrelatedSameBlock.one_le_phi
        exact ⟨by linarith [hs.1],by dsimp [frameCap]; linarith [hs.2,hz.1]⟩
      have hprod := mul_nonneg (show 0≤r-1/Real.cos s by linarith) hphi
      have hh := branch_difference (r:=r) (z:=z) hc.ne'
      exact min_eq_right (by linarith)
    intro x hx y hy hxy
    dsimp only
    rw [he x hx,he y hy]
    exact hlow hx hy hxy

theorem GA_reduces_to_equal (f : Family) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (1/4:ℝ)) (hzs : z≤ s) :
    baseline true (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z≤
      value true (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z := by
  have hb := Explicit.family_basic_domain f hz
  have hl : 0<Explicit.l f z := (Explicit.family_positive f hz).2.1
  have hzf := Explicit.family_frame_domain f hz
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hr : Explicit.k f z/Explicit.l f z∈Icc (11/20:ℝ) (17/20:ℝ) := by
    constructor
    · exact (le_div_iff₀ hl).2 hb.2.2.2.2.1.le
    · apply (div_le_iff₀ hl).2
      linarith [hb.1.2,hb.2.2.1]
  have hm := GA_upper_monotone hr ⟨hzf.1,hzs.trans hs.2⟩
    (show z∈Icc z (1/4:ℝ) from ⟨le_rfl,hzs.trans hs.2⟩)
    (show s∈Icc z (1/4:ℝ) from ⟨hzs,hs.2⟩) hzs
  have hez := GA_identity (k:=Explicit.k f z) (c:=Explicit.c f z) (z:=z) hl hzf
  have hes := GA_identity (k:=Explicit.k f z) (c:=Explicit.c f z) (z:=z) hl hsf
  have hmul := mul_le_mul_of_nonneg_left hm hl.le
  have hzvalue : value true (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z=
      baseline true (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z := by
    simp [value]
  rw [hzvalue] at hez
  linarith

theorem AB_reduces_to_equal (f : Family) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (19/50:ℝ)) (hzs : z≤ s) :
    baseline false (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z≤
      value false (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z := by
  have hb := Explicit.family_basic_domain f hz
  have hl : 0<Explicit.l f z := (Explicit.family_positive f hz).2.1
  have hzf := Explicit.family_frame_domain f hz
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hr : Explicit.m f z/Explicit.l f z∈Icc (4/5:ℝ) (71/50:ℝ) := by
    constructor
    · exact (le_div_iff₀ hl).2 (UnaffectedPositive.AB_ratio_after_equal f hz (hzs.trans hs.2)).le
    · exact (div_le_iff₀ hl).2 hb.2.2.2.2.2.2.le
  have hm := AB_min_monotone hr ⟨hzf.1,hzs.trans hs.2⟩
    (show z∈Icc z (19/50:ℝ) from ⟨le_rfl,hzs.trans hs.2⟩)
    (show s∈Icc z (19/50:ℝ) from ⟨hzs,hs.2⟩) hzs
  have hez := AB_identity (k:=Explicit.k f z) (c:=Explicit.c f z) (z:=z) hl hzf ⟨hzf.1,le_rfl⟩
  have hes := AB_identity (k:=Explicit.k f z) (c:=Explicit.c f z) (z:=z) hl hsf ⟨hzf.1,hzs⟩
  have hmul := mul_le_mul_of_nonneg_left hm hl.le
  have hzvalue : value false (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z=
      baseline false (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z := by
    simp [value]
  rw [hzvalue] at hez
  dsimp [Explicit.m] at hm hmul
  linarith

theorem all_positive_reduces_to_equal (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (hzs : z≤ s) (i : Fin 4) :
    baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z≤
      baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z+
        PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2)
          (Source.pWeights atG (Explicit.k f z) (Explicit.l f z) (Explicit.m f z) s)
          (Source.qWeights atG (Explicit.k f z) (Explicit.l f z) (Explicit.m f z) s) 3 i (s-z) := by
  by_cases hi : i=UnaffectedPositive.affectedIndex atG
  · subst i
    cases atG
    · simpa [value,UnaffectedPositive.affectedIndex,PositiveTD.Hybrid.positive,
        Source.pWeights,Source.qWeights,lambdaB,Explicit.m] using AB_reduces_to_equal f hz hs hzs
    · simpa [value,UnaffectedPositive.affectedIndex,PositiveTD.Hybrid.positive,
        Source.pWeights,Source.qWeights,lambdaG,Explicit.m] using GA_reduces_to_equal f hz hs hzs
  · exact UnaffectedPositive.reduces_to_equal f atG hz hs hzs i hi

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedPositive
end
end
end
