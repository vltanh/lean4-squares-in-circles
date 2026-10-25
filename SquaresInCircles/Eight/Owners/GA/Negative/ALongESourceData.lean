module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Arithmetic.CertificateRestrictions
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowNegativeComparison
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2HighAffected
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsStress
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveASupport
public import SquaresInCircles.Eight.Owners.Negative.PrimaryEntry

/-!
# Eight squares: original signed budgets after deleting one negative A primary

The original
seven angles and points are unchanged. Deletion only constructs the
four analytic ordinary blocks; no virtual argument is called a witness.
-/

section
/-!
## The widened affected-GA saturation slope

The ratio endpoint is 2/3. The exact upper
cosine Taylor value gives numerator coordinate below .766, while
the other coordinate exceeds .5704; the displayed square reserve
then bounds the normalized norm derivative by 1.6.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowAffectedSlope
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus
open NegativeAPositiveTD.SecantCoordinate NegativeAPositiveTD.AffectedNorm

def firstR (r z x : ℝ) : ℝ :=
  (1-r*Real.sin z)*(Real.cos z+x*Real.sin z)/(norm r z x)^3
def charged (r z x : ℝ) : ℝ := (13/12+Real.sin frameCap)*x-R*norm r z x
def chargedFirst (r z x : ℝ) : ℝ := 13/12+Real.sin frameCap-R*first r z x

theorem normR_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (fun r => norm r z x) ((r+x*Real.cos z-Real.sin z)/norm r z x) r := by
  have hn := norm_pos (x:=x) hv
  have hne : (x+r*Real.cos z)^2+(1-r*Real.sin z)^2≠0 := by
    nlinarith [norm_sq r z x]
  have hd := (((((hasDerivAt_id r).mul_const (Real.cos z)).const_add x).pow 2).add
    ((((hasDerivAt_id r).mul_const (Real.sin z)).const_sub 1).pow 2)).sqrt hne
  have hs : Real.sqrt ((x+r*Real.cos z)^2+(1-r*Real.sin z)^2)=norm r z x := rfl
  convert hd using 1
  · rfl
  · simp only [id,Pi.add_apply,Pi.pow_apply,hs]
    field_simp
    linear_combination (-2*r)*(Real.sin_sq_add_cos_sq z)

theorem firstR_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (fun r => first r z x) (firstR r z x) r := by
  have hn := norm_pos (x:=x) hv
  have he : Real.cos z*(norm r z x)^2-
      (x+r*Real.cos z)*(r+x*Real.cos z-Real.sin z)=
      (1-r*Real.sin z)*(Real.cos z+x*Real.sin z) := by
    rw [norm_sq]
    linear_combination r*(x+r*Real.cos z)*(Real.sin_sq_add_cos_sq z)
  have hd := (((hasDerivAt_id r).mul_const (Real.cos z)).const_add x).div
    (normR_hasDerivAt hv) hn.ne'
  convert hd using 1
  · rfl
  · dsimp [first,firstR]
    field_simp [hn.ne']
    nlinarith only [he]

theorem first_x_monotone {r z : ℝ} (hr : r∈Icc (0:ℝ) (2/3:ℝ))
    (hz : z∈Icc 0 frameCap) : MonotoneOn (first r z) (Icc (0:ℝ) (32/125)) := by
  have hv := second_coordinate_pos ⟨hr.1,by linarith [hr.2]⟩ hz
  apply monoOn_of_hasDeriv_nonneg
    (fun x _ => (first_hasDerivAt (x:=x) hv).continuousAt.continuousWithinAt)
    (fun x _ => first_hasDerivAt hv)
  intro x hx
  exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) 3)

theorem first_r_monotone {z x : ℝ} (hx : 0≤x) (hz : z∈Icc 0 frameCap) :
    MonotoneOn (fun r => first r z x) (Icc (0:ℝ) (2/3)) := by
  have hv {r : ℝ} (hr : r∈Icc (0:ℝ) (2/3:ℝ)) :=
    second_coordinate_pos ⟨hr.1,by linarith [hr.2]⟩ hz
  apply monoOn_of_hasDeriv_nonneg
    (fun r hr => (firstR_hasDerivAt (x:=x) (hv hr)).continuousAt.continuousWithinAt)
    (fun r hr => firstR_hasDerivAt (hv (Ioo_subset_Icc_self hr)))
  intro r hr
  have htr := transport_trig hz
  exact div_nonneg
    (mul_nonneg (hv (Ioo_subset_Icc_self hr)).le
      (add_nonneg (by linarith [htr.1]) (mul_nonneg hx htr.2.2.1)))
    (pow_nonneg (Real.sqrt_nonneg _) 3)

theorem first_z_monotone :
    MonotoneOn (fun z => first (2/3) z (32/125)) (Icc (0:ℝ) frameCap) := by
  have hv {z : ℝ} (hz : z∈Icc 0 frameCap) :=
    second_coordinate_pos (r:=(2/3:ℝ)) (by norm_num) hz
  apply monoOn_of_hasDeriv_nonneg
    (fun z hz => (firstZ_hasDerivAt (x:=(32/125:ℝ)) (hv hz)).continuousAt.continuousWithinAt)
    (fun z hz => firstZ_hasDerivAt (x:=(32/125:ℝ)) (hv (Ioo_subset_Icc_self hz)))
  intro z hz
  have ht := transport_trig (Ioo_subset_Icc_self hz)
  have hb : 0≤(2/3:ℝ)+(32/125)*Real.cos z-Real.sin z := by
    linarith [ht.1,ht.2.2.2.1]
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hv (Ioo_subset_Icc_self hz)).le) hb)
    (pow_nonneg (Real.sqrt_nonneg _) 3)

theorem endpoint : R*first (2/3) frameCap (32/125)<8/5 := by
  have ht := transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hc := HighOrderTaylor.cos_le_C12 (by norm_num [frameCap] : (0:ℝ)≤frameCap)
  norm_num [frameCap,HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8] at hc
  have hu0 : 0≤(32/125:ℝ)+(2/3)*Real.cos frameCap := by linarith [ht.1]
  have hu : (32/125:ℝ)+(2/3)*Real.cos frameCap<383/500 := by linarith
  have hv : (713/1250:ℝ)<1-(2/3)*Real.sin frameCap := by linarith [ht.2.2.2.1]
  have hn := norm_pos (x:=(32/125:ℝ)) (show 0<1-(2/3)*Real.sin frameCap by linarith)
  have hn2 := norm_sq (2/3) frameCap (32/125)
  have hu2 := pow_le_pow_left₀ hu0 hu.le 2
  have hv2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤713/1250) hv.le 2
  have hQ : 0≤qCap-(8/5:ℝ)^2 := by norm_num [qCap]
  have hscale := mul_le_mul_of_nonneg_left hu2 hQ
  have htest : qCap*(383/500:ℝ)^2<(8/5:ℝ)^2*((383/500:ℝ)^2+(713/1250:ℝ)^2) := by
    norm_num [qCap]
  have hR0 : 0≤R := Real.sqrt_nonneg qCap
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hprod : 0≤R*((32/125:ℝ)+(2/3)*Real.cos frameCap) := mul_nonneg hR0 hu0
  have hsquare : (R*((32/125:ℝ)+(2/3)*Real.cos frameCap))^2<
      ((8/5)*norm (2/3) frameCap (32/125))^2 := by
    rw [mul_pow,mul_pow,hR2,hn2]
    nlinarith only [hscale,hv2,htest]
  have hh : R*((32/125:ℝ)+(2/3)*Real.cos frameCap)<
      (8/5)*norm (2/3) frameCap (32/125) := by
    nlinarith
  dsimp [first]
  rw [←mul_div_assoc]
  exact (div_lt_iff₀ hn).2 hh

theorem normalized_norm_slope {r z x : ℝ} (hr : r∈Icc (0:ℝ) (2/3:ℝ))
    (hz : z∈Icc 0 frameCap) (hx : x∈Icc 0 (32/125:ℝ)) : R*first r z x<8/5 := by
  have h₁ := first_x_monotone hr hz hx (show (32/125:ℝ)∈Icc 0 (32/125:ℝ) by norm_num) hx.2
  have h₂ := first_r_monotone (x:=(32/125:ℝ)) (by norm_num) hz hr
    (show (2/3:ℝ)∈Icc 0 (2/3:ℝ) by norm_num) hr.2
  have h₃ := first_z_monotone hz
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hz.2
  exact (mul_le_mul_of_nonneg_left (h₁.trans (h₂.trans h₃)) (Real.sqrt_nonneg qCap)).trans_lt endpoint

theorem charged_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (charged r z) (chargedFirst r z x) x := by
  convert ((hasDerivAt_id x).const_mul (13/12+Real.sin frameCap)).sub
    ((norm_hasDerivAt hv).const_mul R) using 1
  · rfl
  · dsimp [chargedFirst]
    ring

theorem charged_slope {r z x : ℝ} (hr : r∈Icc (0:ℝ) (2/3:ℝ))
    (hz : z∈Icc 0 frameCap) (hx : x∈Icc 0 (32/125:ℝ)) :
    (127/1000:ℝ)<chargedFirst r z x := by
  have hh := normalized_norm_slope hr hz hx
  have hs := sin_lower_seven (by norm_num [frameCap] : (0:ℝ)≤frameCap)
  norm_num [frameCap] at hs
  dsimp [chargedFirst]
  linarith

theorem charged_monotone {r z : ℝ} (hr : r∈Icc (0:ℝ) (2/3:ℝ))
    (hz : z∈Icc 0 frameCap) : MonotoneOn (charged r z) (Icc (0:ℝ) (32/125)) := by
  have hv := second_coordinate_pos ⟨hr.1,by linarith [hr.2]⟩ hz
  apply monoOn_of_hasDeriv_nonneg
    (fun x _ => (charged_hasDerivAt (x:=x) hv).continuousAt.continuousWithinAt)
    (fun x _ => charged_hasDerivAt hv)
  intro x hx
  exact (by norm_num : (0:ℝ)≤127/1000).trans (charged_slope hr hz (Ioo_subset_Icc_self hx)).le

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowAffectedSlope
end
end
end

section
/-!
## A negative A primary pays for a shorter nonnegative E total

The only scalar maxima are the two displayed completed squares, one for
each original A owner. All trigonometric estimates hold on whole intervals.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeA.ShortE
open Candidate Secondary PositiveAngularEnvelope
open NegativeAPositiveTD

def gain (B r : ℝ) : ℝ := (13/12)*Real.sin r-B*(1-Real.cos r)
def coefficient (B x e : ℝ) : ℝ :=
  13/12-B*Real.tan x-((13/12)*Real.tan x+B)*Real.tan (e/2)
def capB (atG : Bool) : ℝ := if atG then 82/125 else 2/5
def minimumL : ℝ := 1023/1000
def alpha : ℝ := 53/50
def beta : ℝ := 51/100
def quadraticC : ℝ := (13/12)*alpha*beta
def linearA (atG : Bool) : ℝ := capB atG*alpha
def linearD (atG : Bool) : ℝ := (capB atG+1/(2*minimumL))*beta

/-- The AB contact itself supplies the missing lower tangent cut. -/
theorem AB_tangent_lower {q s : ℝ} {P Q : SignedPoint}
    (hQs : Q.Sorted) (hQc : Q.Contained q) (hq : q≤qCap)
    (hQy : Q.y≤0) (hPy : 0≤P.y) (hPa : P.a=7/12)
    (hs : s∈Icc 0 frameCap) (hAB : zeroFeasible P Q (-s) 2) :
    (1/10:ℝ)<P.y := by
  have hQ := actual_coordinate_bounds (P:=Q.reflect)
    (by simpa using hQs)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hQy)
    (by simpa using hQc) hq
  have hsin := (transport_trig hs).2.2.1
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one s) hPy
  have hproj : edgeWidth (-s)≤ -(7/12)*Real.sin s+P.y*Real.cos s-Q.y := by
    simpa [zeroFeasible,zeroProjection,Real.sin_neg,Real.cos_neg,hPa] using hAB
  have hw := edgeWidth_ge_one (-s)
  dsimp [SignedPoint.reflect] at hQ
  linarith [hQ.2.1,diagonal_bounds.2]

/-- Concavity of `a*u*cos u-sin u` turns the single endpoint Taylor
comparison into a bound for every smaller nonnegative argument. -/
theorem tangent_linear_of_endpoint {a M : ℝ}
    (ha : 1/2≤a) (hM : M∈Icc 0 frameCap)
    (hend : 0≤a*M*Real.cos M-Real.sin M) {u : ℝ}
    (hu : u∈Icc 0 M) : Real.tan u≤a*u := by
  let f : ℝ→ℝ := fun x => a*x*Real.cos x-Real.sin x
  have hc : ConcaveOn ℝ (Icc 0 M) f := by
    apply concave_of_deriv2
      (f':=fun x => (a-1)*Real.cos x-a*x*Real.sin x)
      (f'':=fun x => -(2*a-1)*Real.sin x-a*x*Real.cos x)
    · intro x hx
      have h := (((hasDerivAt_id' x).const_mul a).fun_mul (Real.hasDerivAt_cos x)).fun_sub
        (Real.hasDerivAt_sin x)
      convert h using 1
      ring
    · intro x hx
      have h := ((Real.hasDerivAt_cos x).const_mul (a-1)).fun_sub
        (((hasDerivAt_id' x).const_mul a).fun_mul (Real.hasDerivAt_sin x))
      convert h using 1
      ring
    · intro x hx
      have ht := transport_trig (show x∈Icc 0 frameCap from
        ⟨hx.1,hx.2.trans hM.2⟩)
      have h₁ := mul_nonneg (show 0≤2*a-1 by linarith) ht.2.2.1
      have h₂ := mul_nonneg (mul_nonneg (show 0≤a by linarith) hx.1)
        (show 0≤Real.cos x by linarith [ht.1])
      linarith
  have hz : 0≤f 0 := by simp [f]
  have he : 0≤f M := hend
  have hf := (le_min hz he).trans (hc.min_le_of_mem_Icc
    ⟨le_rfl,hM.1⟩ ⟨hM.1,le_rfl⟩ hu)
  have hcos : 0<Real.cos u := by
    linarith [(transport_trig ⟨hu.1,hu.2.trans hM.2⟩).1]
  rw [Real.tan_eq_sin_div_cos,div_le_iff₀ hcos]
  dsimp [f] at hf
  linarith

theorem tangent_bound {x : ℝ} (hx : x∈Icc 0 (19/50:ℝ)) :
    Real.tan x≤alpha*x := by
  apply tangent_linear_of_endpoint (by norm_num [alpha])
    (show (19/50:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) _ hx
  have hc := cos_lower_six (show (0:ℝ)≤19/50 by norm_num)
  have hs := sin_upper_five (show (0:ℝ)≤19/50 by norm_num)
  norm_num [alpha] at hc hs ⊢
  linarith

theorem half_tangent_bound {e : ℝ} (he : e∈Icc 0 (19/50:ℝ)) :
    Real.tan (e/2)≤beta*e := by
  have hh := tangent_linear_of_endpoint
    (a:=(51/50:ℝ)) (M:=(19/100:ℝ)) (by norm_num)
    (by norm_num [frameCap]) (by
      have hc := cos_lower_six (show (0:ℝ)≤19/100 by norm_num)
      have hs := sin_upper_five (show (0:ℝ)≤19/100 by norm_num)
      norm_num at hc hs ⊢
      linarith)
    (show e/2∈Icc 0 (19/100:ℝ) by constructor <;> linarith [he.1,he.2])
  dsimp [beta]
  linarith

theorem tangent_nonnegative {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0≤Real.tan x := by
  rw [Real.tan_eq_sin_div_cos]
  exact div_nonneg (transport_trig hx).2.2.1
    (by linarith [(transport_trig hx).1])

/-- The exact two completed-square reserves from equations (16)--(17).
The common lower reserve is chosen below both displayed rational values. -/
theorem quadratic_reserve (atG : Bool) {x e : ℝ}
    (hx : 0≤x) (_he : 0≤e) (hs : x+e≤Explicit.angleCut atG) :
    (7/10000:ℝ)< minimumL*(13/12-linearA atG*x-linearD atG*e-
      quadraticC*x*e)-183/200 := by
  have hC : 0<quadraticC := by norm_num [quadraticC,alpha,beta]
  have hD : 0≤linearD atG+quadraticC*x := by
    cases atG <;> dsimp [linearD,capB,minimumL,quadraticC,alpha,beta] <;> positivity
  have hfill := mul_nonneg (show 0≤Explicit.angleCut atG-x-e by linarith) hD
  have hsquare := sq_nonneg
    (x-(linearA atG-linearD atG+quadraticC*Explicit.angleCut atG)/(2*quadraticC))
  cases atG <;>
    norm_num [linearA,linearD,capB,minimumL,quadraticC,alpha,beta,
      Explicit.angleCut] at hfill hsquare ⊢ <;>
    nlinarith only [hfill,hsquare]

theorem coefficient_lower (atG : Bool) {B x e : ℝ}
    (hB : B∈Icc 0 (capB atG)) (hx : 0≤x) (he : 0≤e)
    (hs : x+e≤Explicit.angleCut atG) :
    13/12-capB atG*alpha*x-capB atG*beta*e-quadraticC*x*e≤
      coefficient B x e := by
  have hcut : Explicit.angleCut atG≤(19/50:ℝ) := by
    cases atG <;> norm_num [Explicit.angleCut]
  have hx' : x∈Icc 0 (19/50:ℝ) := ⟨hx,by linarith⟩
  have he' : e∈Icc 0 (19/50:ℝ) := ⟨he,by linarith⟩
  have htx := tangent_bound hx'
  have htq := half_tangent_bound he'
  have htx0 := tangent_nonnegative (show x∈Icc 0 frameCap from
    ⟨hx'.1,by simp only [frameCap]; linarith [hx'.2]⟩)
  have htq0 := tangent_nonnegative (show e/2∈Icc 0 frameCap from
    ⟨by linarith [he'.1],by simp only [frameCap]; linarith [he'.2]⟩)
  have hb0 : 0≤capB atG := by cases atG <;> norm_num [capB]
  have hbx := mul_le_mul hB.2 htx htx0 hb0
  have hbq := mul_le_mul hB.2 htq htq0 hb0
  have hxq := mul_le_mul htx htq htq0 (show 0≤alpha*x by
    dsimp [alpha]; positivity)
  dsimp [coefficient,quadraticC]
  nlinarith only [hbx,hbq,hxq]

theorem normalized_reserve (atG : Bool) {B x e l : ℝ}
    (hB : B∈Icc 0 (capB atG)) (hx : 0≤x) (he : 0≤e)
    (hs : x+e≤Explicit.angleCut atG) (hl : minimumL≤l) :
    (7/10000:ℝ)<l*coefficient B x e-(axial-1/2)-Real.tan (e/2)/2 := by
  have hlo := coefficient_lower atG hB hx he hs
  have hres := quadratic_reserve atG hx he hs
  have hcut : Explicit.angleCut atG≤(19/50:ℝ) := by
    cases atG <;> norm_num [Explicit.angleCut]
  have he' : e∈Icc 0 (19/50:ℝ) := ⟨he,by linarith⟩
  have hq := half_tangent_bound he'
  have hq0 := tangent_nonnegative (show e/2∈Icc 0 frameCap from
    ⟨by linarith [he'.1],by simp only [frameCap]; linarith [he'.2]⟩)
  have hbase : (7/10000:ℝ)< minimumL*coefficient B x e-183/200-
      Real.tan (e/2)/2 := by
    dsimp [linearA,linearD,minimumL,quadraticC,alpha,beta] at hlo hres hq ⊢
    nlinarith only [hlo,hres,hq]
  have hc : 0<coefficient B x e := by
    dsimp [minimumL] at hbase
    nlinarith only [hbase,hq0]
  have hmul := mul_le_mul_of_nonneg_right hl hc.le
  have ha : axial-1/2<183/200 := by linarith [axial_bounds.2]
  linarith

theorem half_angle_identity {e : ℝ} (he : e∈Icc 0 frameCap) :
    1-Real.cos e=Real.sin e*Real.tan (e/2) := by
  have hc := (TwoPositive.ASupport.half_trig he).2
  obtain ⟨hs,hh⟩ := TwoPositive.ASupport.double_angle e
  rw [Real.tan_eq_sin_div_cos,hs,hh]
  field_simp [hc.ne']

theorem transfer_identity {B x e l : ℝ}
    (hx : x∈Icc 0 frameCap) (he : e∈Icc 0 (19/50:ℝ)) :
    l/Real.cos x*(gain B (x+e)-gain B x)+TwoPositive.ASupport.charge e=
      Real.sin e*(l*coefficient B x e-(axial-1/2)-Real.tan (e/2)/2) := by
  have hc : Real.cos x≠0 := (show 0<Real.cos x by
    linarith [(transport_trig hx).1]).ne'
  have he' : e∈Icc 0 frameCap := ⟨he.1,by simp only [frameCap]; linarith [he.2]⟩
  have hh := half_angle_identity he'
  have hle : e≤TwoPositive.ASupport.alpha := by
    linarith [he.2,TwoPositive.ASupport.alpha_bounds.1]
  rw [TwoPositive.ASupport.charge]
  simp only [hle,↓reduceIte]
  calc
    l/Real.cos x*(gain B (x+e)-gain B x)+TwoPositive.ASupport.axialCharge e=
        (l*(13/12-B*Real.tan x)-(axial-1/2))*Real.sin e-
          (l*((13/12)*Real.tan x+B)+1/2)*(1-Real.cos e) := by
      dsimp [gain,TwoPositive.ASupport.axialCharge]
      rw [Real.sin_add,Real.cos_add,Real.tan_eq_sin_div_cos x]
      field_simp [hc]
      ring
    _=Real.sin e*(l*coefficient B x e-(axial-1/2)-Real.tan (e/2)/2) := by
      rw [hh]
      dsimp [coefficient]
      ring

/-- Equation (8), including both closed endpoints `e=0` and `e=s`. -/
theorem transfer (atG : Bool) {B s e l : ℝ}
    (hB : B∈Icc 0 (capB atG)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (he : e∈Icc 0 s) (hl : minimumL≤l) :
    0≤l/Real.cos (s-e)*(gain B s-gain B (s-e))+
      TwoPositive.ASupport.charge e := by
  have hcut : Explicit.angleCut atG≤(19/50:ℝ) := by
    cases atG <;> norm_num [Explicit.angleCut]
  have hx : s-e∈Icc 0 frameCap := ⟨by linarith [he.2],by simp only [frameCap]; linarith [he.1,hs.2]⟩
  have he' : e∈Icc 0 (19/50:ℝ) := ⟨he.1,by linarith [he.2,hs.2]⟩
  have hr := normalized_reserve atG hB hx.1 he.1
    (show s-e+e≤Explicit.angleCut atG by linarith [hs.2]) hl
  have hid := transfer_identity (B:=B) (l:=l) hx he'
  rw [show s-e+e=s by ring] at hid
  rw [hid]
  exact mul_nonneg (transport_trig (show e∈Icc 0 frameCap from
    ⟨he'.1,by simp only [frameCap]; linarith [he'.2]⟩)).2.2.1
    (by linarith)

end SquaresInCircles.Eight.GlobalGA.NegativeA.ShortE
end
end
end

section
/-!
## The negative-A gain and the small-total comparison

The strict GA contact comparison is made on the pair G, A of the cycle (`GA_sharp_cut`). The
common gain `gain` is concave on the whole analytic interval (`gain_concave`), including values
beyond the smaller GA cut.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeA.LongE
open Candidate Secondary

def gain (s : ℝ) : ℝ :=
  (13/12)*Real.sin s-(82/125-(63/100)*s)*(1-Real.cos s)
def gainD (s : ℝ) : ℝ :=
  (13/12-63/100)*Real.cos s+63/100-(82/125-(63/100)*s)*Real.sin s
def gainDD (s : ℝ) : ℝ :=
  (53/300)*Real.sin s+((63/100)*s-82/125)*Real.cos s

@[simp] theorem gain_zero : gain 0=0 := by simp [gain]

theorem gain_hasDerivAt (s : ℝ) : HasDerivAt gain (gainD s) s := by
  have h := ((Real.hasDerivAt_sin s).const_mul (13/12)).fun_sub
    (((hasDerivAt_const s (82/125:ℝ)).fun_sub ((hasDerivAt_id' s).const_mul (63/100))).fun_mul
      ((hasDerivAt_const s (1:ℝ)).fun_sub (Real.hasDerivAt_cos s)))
  unfold gain
  convert h using 1
  dsimp [gainD]
  ring

theorem gainD_hasDerivAt (s : ℝ) : HasDerivAt gainD (gainDD s) s := by
  have h := (((Real.hasDerivAt_cos s).const_mul (13/12-63/100)).add_const (63/100)).fun_sub
    (((hasDerivAt_const s (82/125:ℝ)).fun_sub ((hasDerivAt_id' s).const_mul (63/100))).fun_mul
      (Real.hasDerivAt_sin s))
  unfold gainD
  convert h using 1
  dsimp [gainDD]
  ring

theorem gain_curvature {s : ℝ} (hs : s∈Icc 0 (19/50:ℝ)) : gainDD s< -31/100 := by
  have hsin := Real.sin_le hs.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=s)
  have hsq := pow_le_pow_left₀ hs.1 hs.2 2
  have hc : (1:ℝ)-(19/50)^2/2≤Real.cos s := by linarith
  have hb : (82/125:ℝ)-(63/100)*(19/50)≤82/125-(63/100)*s := by linarith [hs.2]
  have hprod := mul_le_mul hb hc (by norm_num : (0:ℝ)≤1-(19/50)^2/2)
    (by linarith [hs.2] : (0:ℝ)≤82/125-(63/100)*s)
  dsimp [gainDD]
  nlinarith only [hprod,hs.2,hsin]

theorem gain_concave : ConcaveOn ℝ (Icc (0:ℝ) (19/50)) gain := by
  apply concave_of_deriv2 (fun s _ => gain_hasDerivAt s) (fun s _ => gainD_hasDerivAt s)
  intro s hs
  linarith [gain_curvature hs]

namespace Contact

def root (s : ℝ) : ℝ := Real.sqrt (qCap-(13/12+Real.sin s)^2)
def cap (s : ℝ) : ℝ := root s-Real.cos s-1/2
def slope (s : ℝ) : ℝ := Real.sin s-(13/12+Real.sin s)*Real.cos s/root s
def P (y : ℝ) : ℝ := 76784149/900000000-(321217/750000)*y+
  (2113/10000)*y^2+(63/50)*y^3
def PD (y : ℝ) : ℝ := -321217/750000+(2113/5000)*y+(189/50)*y^2

theorem P_hasDerivAt (y : ℝ) : HasDerivAt P (PD y) y := by
  have h := (((hasDerivAt_const y (76784149/900000000:ℝ)).fun_sub
    ((hasDerivAt_id' y).const_mul (321217/750000))).fun_add
      (((hasDerivAt_id' y).fun_pow 2).const_mul (2113/10000))).fun_add
        (((hasDerivAt_id' y).fun_pow 3).const_mul (63/50))
  unfold P
  convert h using 1
  simp only [PD,Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,show (3:ℕ)-1=2 from rfl,pow_one]
  ring

theorem P_positive {y : ℝ} (hy : y∈Icc 0 (1/4:ℝ)) : 0<P y := by
  have hm : AntitoneOn P (Icc (0:ℝ) (1/4)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun y _ => (P_hasDerivAt y).continuousAt.continuousWithinAt)
      (fun y _ => P_hasDerivAt y)
    intro t ht
    have hs := pow_le_pow_left₀ ht.1.le ht.2.le 2
    dsimp [PD]
    nlinarith only [ht.2,hs]
  have hh := hm hy (show (1/4:ℝ)∈Icc 0 (1/4) by norm_num) hy.2
  have hp : (0:ℝ)<P (1/4) := by norm_num [P]
  exact hp.trans_le hh

theorem root_data {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    0<root s ∧ (root s)^2=qCap-(13/12+Real.sin s)^2 := by
  have hsin0 := (transport_trig (show s∈Icc 0 frameCap from
    ⟨hs.1,by simp only [frameCap]; linarith [hs.2]⟩)).2.2.1
  have hsin := Real.sin_le hs.1
  have hsq := pow_le_pow_left₀ (by linarith : (0:ℝ)≤13/12+Real.sin s)
    (show 13/12+Real.sin s≤13/12+1/4 by linarith [hs.2]) 2
  have hrad : 0<qCap-(13/12+Real.sin s)^2 := by dsimp [qCap]; nlinarith only [hsq]
  exact ⟨Real.sqrt_pos.2 hrad,Real.sq_sqrt hrad.le⟩

theorem cap_hasDerivAt {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    HasDerivAt cap (slope s) s := by
  have hr := root_data hs
  have hrad : qCap-(13/12+Real.sin s)^2≠0 := by rw [←hr.2]; exact pow_ne_zero 2 hr.1.ne'
  have hd := ((hasDerivAt_const s qCap).fun_sub
    (((Real.hasDerivAt_sin s).const_add (13/12)).fun_pow 2)).sqrt hrad
  have h := (hd.fun_sub (Real.hasDerivAt_cos s)).sub_const (1/2)
  unfold cap root
  convert h using 1
  have hroot : Real.sqrt (qCap-(13/12+Real.sin s)^2)≠0 := hr.1.ne'
  simp only [slope,root,Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one]
  field_simp
  ring

theorem slope_upper {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) : slope s< -63/100 := by
  have ht := transport_trig (show s∈Icc 0 frameCap from
    ⟨hs.1,by simp only [frameCap]; linarith [hs.2]⟩)
  have hy : Real.sin s∈Icc 0 (1/4:ℝ) := ⟨ht.2.2.1,(Real.sin_le hs.1).trans hs.2⟩
  have hp := P_positive hy
  have hr := root_data hs
  have hid : ((13/12+Real.sin s)*Real.cos s)^2-
      ((Real.sin s+63/100)*root s)^2=P (Real.sin s) := by
    rw [mul_pow,mul_pow,hr.2]
    dsimp [P,qCap]
    nlinarith [Real.sin_sq_add_cos_sq s,
      congrArg (fun t : ℝ => (13/12+Real.sin s)^2*t) (Real.sin_sq_add_cos_sq s)]
  have hleft : 0≤(Real.sin s+63/100)*root s := mul_nonneg (by linarith [hy.1]) hr.1.le
  have hright : 0≤(13/12+Real.sin s)*Real.cos s :=
    mul_nonneg (by linarith [hy.1]) (by linarith [ht.1])
  have hstrict : (Real.sin s+63/100)*root s<(13/12+Real.sin s)*Real.cos s := by
    nlinarith only [hid,hp,hleft,hright]
  have hquot := (lt_div_iff₀ hr.1).2 hstrict
  dsimp [slope]
  linarith

theorem cap_linear {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    cap s<39/250-(63/100)*s := by
  have hm : AntitoneOn (fun t => cap t+(63/100)*t) (Icc (0:ℝ) (1/4)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun t ht => ((cap_hasDerivAt ht).add ((hasDerivAt_id t).const_mul (63/100))).continuousAt.continuousWithinAt)
      (fun t ht => (cap_hasDerivAt (Ioo_subset_Icc_self ht)).add ((hasDerivAt_id t).const_mul (63/100)))
    intro t ht
    linarith [slope_upper (Ioo_subset_Icc_self ht)]
  have hh := hm (show (0:ℝ)∈Icc 0 (1/4) by norm_num) hs hs.1
  have hr := root_data (show (0:ℝ)∈Icc 0 (1/4) by norm_num)
  have hzero : cap 0<39/250 := by
    simp only [cap,Real.cos_zero] at ⊢
    simp only [Real.sin_zero,add_zero] at hr
    dsimp [qCap] at hr
    nlinarith only [hr.1,hr.2]
  simp only [mul_zero,add_zero] at hh
  linarith

theorem corner_cut {b s : ℝ} (hb : 0≤b) (hs : s∈Icc 0 (1/4:ℝ))
    (hcorner : (b+1/2+Real.cos s)^2+(13/12+Real.sin s)^2<qCap) :
    b<39/250-(63/100)*s ∧ s<61/250 := by
  have ht := transport_trig (show s∈Icc 0 frameCap from
    ⟨hs.1,by simp only [frameCap]; linarith [hs.2]⟩)
  have hr := root_data hs
  have hroot : b+1/2+Real.cos s<root s := by
    have hbpos : 0≤b+1/2+Real.cos s := by linarith [ht.1]
    nlinarith only [hcorner,hr.1,hr.2,hbpos]
  have hcap : b<cap s := by dsimp [cap]; linarith
  refine ⟨hcap.trans (cap_linear hs),?_⟩
  by_contra! hlarge
  have hm := PrimaryCap.contactHeight_strictMono.monotoneOn
    (show (61/250:ℝ)∈Icc 0 (7/10) by norm_num)
    (show s∈Icc 0 (7/10) from ⟨hs.1,by linarith [hs.2]⟩) hlarge
  have t := PositiveTD.Certificate.taylor_bounds
    (show (61/250:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hsingle : qCap<(13/12:ℝ)^2+5/4+
      aeval (61/250:ℝ) PositiveTD.Certificate.C10+
        (13/6)*aeval (61/250:ℝ) PositiveTD.Certificate.S11 := by
    norm_num [qCap,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4,
      PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5]
  have hdrop := mul_nonneg hb (by linarith [ht.1] : 0≤1+2*Real.cos s+b)
  dsimp [PrimaryCap.contactHeight,PrimaryCap.K] at hm
  nlinarith [Real.sin_sq_add_cos_sq s]

end Contact

/-- The sharper cut uses the GA3 contact and the strict failure of the GA2 contact, at the two
states of G and A. -/
theorem GA_sharp_cut {q s : ℝ} {G A : SignedPoint}
    (_hGs : G.Sorted) (hGc : G.Contained q) (hAs : A.Sorted) (hq : q≤qCap)
    (hGy : G.y≤0) (hAy : 0≤A.y) (hAa : A.a=7/12)
    (hs : s∈Ioc 0 (1/4:ℝ))
    (hGA : quarterFeasible G A (-s) 3) (hnot : ¬quarterFeasible G A (-s) 2) :
    A.y<39/250-(63/100)*s ∧ s<61/250 := by
  have hv := negative_primary_contact_vector (a:=A.a) (g:=A.y) (A:=G.a) (b:=-G.y) (z:=s) hAs.1 hAy
    (by simpa [abs_of_nonneg hAy] using hAs.2)
    ⟨hs.1,by linarith [hs.2]⟩
    (by
      have h : edgeWidth (-s)≤G.a+A.a*Real.sin (-s)-A.y*Real.cos (-s) := hGA
      rw [Real.sin_neg,Real.cos_neg] at h
      linarith)
    (by
      have h : ¬edgeWidth (-s)≤G.a*Real.cos (-s)-G.y*Real.sin (-s)-A.y := hnot
      rw [Real.sin_neg,Real.cos_neg,not_le] at h
      linarith)
  have hc : (G.a+1/2)^2+(-G.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hGy] using hGc.trans hq
  have hcorner : (A.y+1/2+Real.cos s)^2+(13/12+Real.sin s)^2<qCap := by
    rw [hAa] at hv
    nlinarith [Real.sin_sq_add_cos_sq s]
  exact Contact.corner_cut hAy ⟨hs.1.le,hs.2⟩ hcorner

theorem gain_le_GA {b s : ℝ} (hb : b≤39/250-(63/100)*s) :
    gain s≤ShortE.gain (b+1/2) s := by
  have hh := mul_le_mul_of_nonneg_right
    (show b+1/2≤82/125-(63/100)*s by linarith) (sub_nonneg.mpr (Real.cos_le_one s))
  dsimp [gain,ShortE.gain]
  linarith

theorem gain_le_AB {b s : ℝ} (hb : 1/10≤b) (hs : s≤19/50) :
    gain s≤ShortE.gain (1/2-b) s := by
  have hh := mul_le_mul_of_nonneg_right
    (show 1/2-b≤82/125-(63/100)*s by linarith) (sub_nonneg.mpr (Real.cos_le_one s))
  dsimp [gain,ShortE.gain]
  linarith

theorem gain_small {s : ℝ} (hs : s∈Icc 0 (1/6:ℝ)) : s≤gain s := by
  have hsin := Real.sin_ge_sub_cube hs.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=s)
  have hcos1 := Real.cos_le_one s
  have hpositive := mul_nonneg hs.1 (sub_nonneg.mpr hcos1)
  have hsq := mul_le_mul_of_nonneg_right hs.2 hs.1
  have hcub := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.1 hs.2 2) hs.1
  dsimp [gain]
  nlinarith only [hsin,hcos,hpositive,hsq,hcub,hs.1]

theorem charge_small_slope {u : ℝ} (hu : u∈Icc 0 (1/6:ℝ)) :
    -(599/600:ℝ)≤TwoPositive.ASupport.axialD u := by
  have hsin := Real.sin_le hu.1
  have hcos := Real.cos_le_one u
  have hb : 0≤axial-1/2 := by linarith [axial_bounds.1]
  have hh := mul_le_mul_of_nonneg_left hcos hb
  have ha : axial-1/2<183/200 := by linarith [axial_bounds.2]
  dsimp [TwoPositive.ASupport.axialD]
  linarith [hu.2]

theorem small_transfer {l s e : ℝ} (hl : 1≤l)
    (hs : 0≤ s) (hse : s≤e) (he : e≤1/6) :
    TwoPositive.ASupport.charge (e-s)+s/600≤l*gain s+TwoPositive.ASupport.charge e := by
  have hm : MonotoneOn
      (fun u => TwoPositive.ASupport.axialCharge u+(599/600)*u) (Icc (0:ℝ) (1/6)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun u _ => ((TwoPositive.ASupport.axial_derivative u).add
        ((hasDerivAt_id u).const_mul (599/600))).continuousAt.continuousWithinAt)
      (fun u _ => (TwoPositive.ASupport.axial_derivative u).add
        ((hasDerivAt_id u).const_mul (599/600)))
    intro u hu
    linarith [charge_small_slope (Ioo_subset_Icc_self hu)]
  have hh := hm (show e-s∈Icc 0 (1/6:ℝ) by constructor <;> linarith)
    (show e∈Icc 0 (1/6:ℝ) by constructor <;> linarith) (by linarith)
  have hg := gain_small (show s∈Icc 0 (1/6:ℝ) by constructor <;> linarith)
  have hprod := mul_le_mul_of_nonneg_right hl (hs.trans hg)
  rw [TwoPositive.ASupport.charge_low he,
    TwoPositive.ASupport.charge_low (show e-s≤1/6 by linarith)]
  linarith

theorem polynomial_gain_lower {s : ℝ} (hs : s∈Icc 0 (8/15:ℝ)) :
    (13/12)*aeval s PositiveTD.Certificate.S11+
      (82/125-(63/100)*s)*(aeval s PositiveTD.Certificate.C10-1)≤gain s := by
  have ht := PositiveTD.Certificate.taylor_bounds
    (show s∈Icc 0 frameCap from ⟨hs.1,by simp only [frameCap]; linarith [hs.2]⟩)
  have hb : 0≤82/125-(63/100)*s := by linarith [hs.2]
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hb
  dsimp [gain]
  linarith [ht.2.1]

end SquaresInCircles.Eight.GlobalGA.NegativeA.LongE
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeA.LongE.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

abbrev aError := NegativeAPositiveTD.Source.aError
abbrev eTotal := PairedE.cycleTotal
def effective (C : SignedCycle) (de eh : Bool) (s : ℝ) : ℝ :=
  delta C.theta T+eTotal C de eh-s
def blocks (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ) : Fin 4 → Block :=
  NonnegativeTotals.Source.blocks C hg atG (!atG) de eh k l c
def actualBlocks (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ) : Fin 4 → ℝ :=
  NonnegativeTotals.Source.actualBlocks C hg atG (!atG) de eh k l c
def actualStress (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ) : ℝ :=
  NonnegativeTotals.Source.actualStress C hg atG (!atG) de eh k l c
def eParts (C : SignedCycle) (de eh : Bool) (f : ℝ → ℝ) : ℝ :=
  f (PairedE.selected de (delta C.theta D))+f (PairedE.selected eh (delta C.theta E))

theorem eParts_nonnegative (C : SignedCycle) (de eh : Bool) (f : ℝ → ℝ)
    (hf : ∀u,0≤f u) : 0≤eParts C de eh f := by
  exact add_nonneg (hf _) (hf _)

theorem eParts_signed (C : SignedCycle) (de eh : Bool) :
    eParts C de eh positivePart-eParts C de eh negativePart=eTotal C de eh := by
  have hD := positive_sub_negative (PairedE.selected de (delta C.theta D))
  have hE := positive_sub_negative (PairedE.selected eh (delta C.theta E))
  dsimp [eParts,eTotal,PairedE.cycleTotal,PairedE.total]
  linarith

theorem selected_parts {C : SignedCycle} {s : ℝ} (atG de eh : Bool)
    (ha : aError C atG= -s) (f : ℝ → ℝ) (hf : f 0=0) :
    NonnegativeTotals.Source.selectedSum C atG (!atG) de eh f=f (-s)+eParts C de eh f := by
  cases atG <;>
    simp only [aError,NegativeAPositiveTD.Source.aError,Bool.false_eq_true,ite_false,ite_true] at ha <;>
    simp [NonnegativeTotals.Source.selectedSum,PairedE.selected,eParts,ha,hf] <;> ring

theorem block_parts {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool)
    (k l c : ℝ) (ha : aError C atG= -s) (f : ℝ → ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg atG de eh k l c i).u+f (blocks C hg atG de eh k l c i).v))=
      (∑v,f (delta C.theta v))-f (delta C.theta T)-f (-s)-eParts C de eh f := by
  have hh := NonnegativeTotals.Source.sum_parts C hg atG (!atG) de eh k l c f hf
  rw [selected_parts atG de eh ha f hf] at hh
  dsimp [blocks]
  linarith

structure Budget (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c s : ℝ) : Prop where
  td_domain : delta C.theta T∈Icc 0 frameCap
  e_domain : eTotal C de eh∈Icc 0 frameCap
  total_upper : delta C.theta T+eTotal C de eh≤frameCap
  residual_domain : effective C de eh s∈Icc 0 frameCap
  positive_original : (∑i,(blocks C hg atG de eh k l c i).P)≤frameCap-delta C.theta T-eTotal C de eh
  positive_bound : (∑i,(blocks C hg atG de eh k l c i).P)≤frameCap-effective C de eh s
  negative_original : (∑i,(blocks C hg atG de eh k l c i).N)≤frameCap-s
  negative_bound : (∑i,(blocks C hg atG de eh k l c i).N)≤frameCap
  balance : (∑i,(blocks C hg atG de eh k l c i).N)=
    effective C de eh s+∑i,(blocks C hg atG de eh k l c i).P

theorem budgets {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (hs : 0≤ s) (ha : aError C atG= -s)
    (hz : 0≤delta C.theta T) (he : s≤eTotal C de eh) :
    Budget C hg atG de eh k l c s := by
  have hp := block_parts hg atG de eh k l c ha positivePart positivePart_zero
  have hn := block_parts hg atG de eh k l c ha negativePart negativePart_zero
  have hpz : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hnz : negativePart (delta C.theta T)=0 := max_eq_right (by linarith)
  have hps : positivePart (-s)=0 := max_eq_right (by linarith)
  have hns : negativePart (-s)=s := by simp [negativePart,hs]
  have hP : (∑i,(blocks C hg atG de eh k l c i).P)=
      positiveVariation C.theta-delta C.theta T-eParts C de eh positivePart := by
    simpa only [Block.P,hpz,hps,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg atG de eh k l c i).N)=
      negativeVariation C.theta-s-eParts C de eh negativePart := by
    simpa only [Block.N,hnz,hns,sub_zero,negativeVariation] using hn
  have heq := eParts_signed C de eh
  have hEneg := eParts_nonnegative C de eh negativePart negativePart_nonneg
  have hP0 : 0≤∑i,(blocks C hg atG de eh k l c i).P :=
    Finset.sum_nonneg (fun i _ => (blocks C hg atG de eh k l c i).P_nonneg)
  have hN0 : 0≤∑i,(blocks C hg atG de eh k l c i).N :=
    Finset.sum_nonneg (fun i _ => (blocks C hg atG de eh k l c i).N_nonneg)
  have hPcap : (∑i,(blocks C hg atG de eh k l c i).P)≤frameCap-delta C.theta T-eTotal C de eh := by
    linarith
  have hNcap : (∑i,(blocks C hg atG de eh k l c i).N)≤frameCap-s := by
    linarith [variations_equal C.theta]
  have hbalance : (∑i,(blocks C hg atG de eh k l c i).N)=
      effective C de eh s+∑i,(blocks C hg atG de eh k l c i).P := by
    dsimp [effective]
    linarith [variations_equal C.theta]
  have htotal : delta C.theta T+eTotal C de eh≤frameCap := by linarith
  refine ⟨⟨hz,by linarith⟩,⟨by linarith,by linarith⟩,htotal,
    ?_,hPcap,?_,hNcap,by linarith,hbalance⟩
  · dsimp [effective]; constructor <;> linarith
  · dsimp [effective]; linarith

theorem block_budgets {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (hs : 0≤ s) (ha : aError C atG= -s)
    (hz : 0≤delta C.theta T) (he : s≤eTotal C de eh) (i : Fin 4) :
    (blocks C hg atG de eh k l c i).P≤frameCap ∧ (blocks C hg atG de eh k l c i).N≤frameCap := by
  have hb := budgets hg atG de eh k l c hvar hs ha hz he
  have hP := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG de eh k l c j).P_nonneg) (Finset.mem_univ i)
  have hN := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG de eh k l c j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.residual_domain.1],hN.trans hb.negative_bound⟩

theorem actual_gain_identity {C : SignedCycle} {s : ℝ} (atG : Bool)
    (ha : aError C atG= -s) (hflat : (C.point A).a=7/12) (hs : s∈Icc 0 frameCap) :
    PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A)=
      ShortE.gain (if atG then (C.point A).y+1/2 else 1/2-(C.point A).y) s := by
  cases atG <;>
    simp only [aError,NegativeAPositiveTD.Source.aError,Bool.false_eq_true,ite_false,ite_true] at ha <;>
    simp [PairedE.primaryGain,ha,Real.sin_neg,Real.cos_neg,edgeWidth_negative_formula hs,
      hflat,ShortE.gain] <;> ring

theorem gain_lower {q s : ℝ} {C : SignedCycle} (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hGy : (C.point G).y≤0) (hBy : (C.point B).y≤0)
    (hflat : (C.point A).a=7/12) (hAy : 0≤(C.point A).y)
    (hs : s∈Icc 0 (NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : aError C atG= -s) (hnot : atG=true → ¬C.Feasible G 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) :
    gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A) := by
  have hsframe := (NegativeAPositiveTD.Explicit.angle_domain atG hs).2
  rw [actual_gain_identity atG ha hflat hsframe]
  by_cases hzero : s=0
  · subst s; simp [gain,ShortE.gain]
  have hpos : 0<s := lt_of_le_of_ne hs.1 (Ne.symm hzero)
  cases atG
  · have hAB' : zeroFeasible (C.point A) (C.point B) (-s) 2 := by
      change delta C.theta A= -s at ha
      have h : 0≤zeroProjection (C.point A) (C.point B) (delta C.theta A) 2-
          edgeWidth (delta C.theta A) := hAB
      rw [ha] at h
      exact sub_nonneg.mp h
    have hb := ShortE.AB_tangent_lower (hsorted B) (hcontained B) hq hBy hAy hflat hsframe hAB'
    exact gain_le_AB hb.le (by simpa [NegativeAPositiveTD.Explicit.angleCut] using hs.2)
  · have hga : quarterFeasible (C.point G) (C.point A) (-s) 3 := by
      change delta C.theta G= -s at ha
      have h : 0≤quarterProjection (C.point G) (C.point A) (delta C.theta G) 3-
          edgeWidth (delta C.theta G) := hGA
      rw [ha] at h
      exact sub_nonneg.mp h
    have hga2 : ¬quarterFeasible (C.point G) (C.point A) (-s) 2 := by
      intro hh
      apply hnot rfl
      change delta C.theta G= -s at ha
      show 0≤quarterProjection (C.point G) (C.point A) (delta C.theta G) 2-
          edgeWidth (delta C.theta G)
      rw [ha]
      exact sub_nonneg.mpr hh
    have hcut := GA_sharp_cut (hsorted G) (hcontained G) (hsorted A) hq hGy hAy hflat
      ⟨hpos,by simpa [NegativeAPositiveTD.Explicit.angleCut] using hs.2⟩ hga hga2
    exact gain_le_GA hcut.1.le

end SquaresInCircles.Eight.GlobalGA.NegativeA.LongE.Source
end
end
end
