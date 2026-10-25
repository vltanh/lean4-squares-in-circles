module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2Source
public import SquaresInCircles.Eight.TableFree.GlobalGAPairedECharge

/-!
# A negative A primary pays for a shorter nonnegative E total

Uncompiled transcription of Sections 2--3 of
`HAND_G3_NEGATIVE_A_PRIMARY_DOMINATES_SHORTER_E_TOTAL.md`.
The only scalar maxima are the two displayed completed squares, one for
each original A owner. All trigonometric estimates hold on whole intervals.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.ShortE
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
    (hx : 0≤x) (he : 0≤e) (hs : x+e≤Explicit.angleCut atG) :
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.ShortE
