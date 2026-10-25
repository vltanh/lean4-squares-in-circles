module

public import SquaresInCircles.Eight.Arithmetic.PackedModels
public import SquaresInCircles.Eight.Owners.Critical.EExclusion
public import SquaresInCircles.Eight.Owners.Critical.EWeightBounds
public import SquaresInCircles.Eight.Owners.Critical.EPosition
public import SquaresInCircles.Eight.Owners.Flat.TStress

/-!
# Eight squares: exact sharp-strip negative-T secant endpoints

The two rationalized certificates are joined to the
literal full-circle secant charges. The factors are exact identities,
including the difference of the shifted ordinary B norms. The A endpoint
uses an integrated coefficient comparison, so no ordering of k and c is
assumed. All coefficients come from the original minimizing chain.
-/

section
/-!
## The two negative-T gains on the whole critical strip

The critical strip is one square of the variables `x, y ∈ [-1, 1]`, with `t = 13/100 + (3/100) x`
and `u = 1 - (51/80) t + (7/4000) y`; the sharp radius lies in a fixed rational interval and is
carried as a remainder (`models_contain`). Both gain formulas keep their rationalized norm
differences. The gains `jD` and `jB` exceed `0` and `7/500` on the whole strip (`reserves`,
`whole_strip`), hence at the minimizing positions (`minimizing_strip`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalNegativeTPolynomials
open TensorPolynomialEnclosure TensorResidualEnclosure TensorRadicalExpression
open Candidate Stationary.FiveCornerGeometry

def jD (R l c t : ℝ) : ℝ :=
  (Real.sin t+13/12)/Real.cos t-R*
    (c*Real.sin t/(Real.cos t^2*(Real.sqrt (1+c^2/Real.cos t^2)+Real.sqrt (1+c^2)))+
      2*l/(Real.sqrt (l^2+c^2)+Real.sqrt (l^2+c^2-2*l*c*Real.sin t)))

def shortAngle : ℝ := 9/100

def jB (R l c t : ℝ) : ℝ :=
  let b := shortAngle
  let a := Real.sin b/(1+Real.cos b)
  a*(1/Real.cos b-Real.cos t)+(13/12)/Real.cos b+Real.sin t-R*
    (c*Real.sin b/(Real.cos b^2*(Real.sqrt (l^2+c^2/Real.cos b^2)+Real.sqrt (l^2+c^2)))+
      2*l*(Real.cos t+Real.sin t*a)/
        (Real.sqrt (l^2+c^2-2*l*c*Real.sin (t-b))+
          Real.sqrt (l^2+c^2-2*l*c*Real.sin t)))

abbrev E := Expr (Fin 3)
def timeE : E := .variable 0
def radiusE : E := .variable 1
def positionE : E := .variable 2
def sineE : E := .sine timeE
def cosineE : E := .cosine timeE
def rE : E := .root (radiusE-positionE^2)
def UE : E := .root (radiusE-(2-positionE)^2)
def VE : E := 3-UE
def YE : E := .root (radiusE-VE^2)
def vE : E := 2-YE
def wE : E := .root (radiusE-vE^2)
def firstE : E := 2-cosineE*(rE-1)+sineE*positionE
def secondE : E := 1+cosineE*vE-sineE*(wE-1)
def etaE : E := vE/wE
def lambdaE : E := cosineE+etaE*sineE
def kE : E := lambdaE*VE/YE
def ellE : E := kE*(2-positionE)/UE
def cE : E := firstE/secondE

def normZeroE : E := .root (ellE^2+cE^2)
def normAtE (a : E) : E := .root (ellE^2+cE^2-2*ellE*cE*(.sine a))

def jDE : E :=
  (sineE+.literal (13/12))/cosineE-(.root radiusE)*
    (cE*sineE/(cosineE^2*((.root (1+cE^2/cosineE^2))+(.root (1+cE^2))))+
      2*ellE/(normZeroE+normAtE timeE))

def bE : E := .literal (9/100)
def sinBE : E := .sine bE
def cosBE : E := .cosine bE
def tanHalfBE : E := sinBE/(1+cosBE)
def jBE : E :=
  tanHalfBE*(1/cosBE-cosineE)+(.literal (13/12))/cosBE+sineE-(.root radiusE)*
    (cE*sinBE/(cosBE^2*((.root (ellE^2+cE^2/cosBE^2))+normZeroE))+
      2*ellE*(cosineE+sineE*tanHalfBE)/(normAtE (timeE-bE)+normAtE timeE))

def values (q t u : ℝ) : Fin 3 → ℝ := ![t,q,u]

private theorem r51_v_sub (v : Fin 3 → ℝ) (a b : E) :
    Expr.value v (a-b)=Expr.value v a-Expr.value v b := by
  show Expr.value v a+-Expr.value v b=_
  ring
private theorem r51_v_div (v : Fin 3 → ℝ) (a b : E) :
    Expr.value v (a/b)=Expr.value v a/Expr.value v b := by
  show Expr.value v a*(1/Expr.value v b)=_
  ring
private theorem r51_v_pow (v : Fin 3 → ℝ) (a : E) (n : ℕ) :
    Expr.value v (a^n)=Expr.value v a^n := rfl

theorem expression_weights (q t u : ℝ) :
    Expr.value (values q t u) ellE=CriticalEFamily.ell q t u ∧
      Expr.value (values q t u) cE=CriticalEFamily.c q t u := by
  refine ⟨?_,?_⟩ <;>
    simp only [ellE,kE,lambdaE,etaE,cE,firstE,secondE,rE,UE,VE,YE,vE,wE,
      timeE,radiusE,positionE,sineE,cosineE,r51_v_sub,r51_v_div,r51_v_pow,
      Expr.value,values,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
      Matrix.tail_cons,CriticalEFamily.ell,CriticalEFamily.k,CriticalEFamily.lam,
      CriticalEFamily.eta,CriticalEFamily.c,lowerRight,topRight,topLeft,topHeight,lowerHeight,
      lowerLeft,upper,firstComponent,secondComponent] <;> norm_num

theorem expression_values (q t u : ℝ) :
    Expr.value (values q t u) jDE=jD (Real.sqrt q) (CriticalEFamily.ell q t u) (CriticalEFamily.c q t u) t ∧
    Expr.value (values q t u) jBE=jB (Real.sqrt q) (CriticalEFamily.ell q t u) (CriticalEFamily.c q t u) t := by
  obtain ⟨hl,hc⟩ := expression_weights q t u
  have h0 : values q t u 0=t := rfl
  have h1 : values q t u 1=q := rfl
  refine ⟨?_,?_⟩
  · simp only [jDE,normZeroE,normAtE,timeE,radiusE,sineE,cosineE,r51_v_sub,
      r51_v_div,r51_v_pow,Expr.value,h0,h1,hl,hc,jD,
      Rat.cast_div,Rat.cast_ofNat]
    all_goals ring
  · simp only [jBE,normZeroE,normAtE,bE,sinBE,cosBE,tanHalfBE,timeE,radiusE,sineE,cosineE,
      r51_v_sub,r51_v_div,r51_v_pow,Expr.value,
      h0,h1,hl,hc,jB,shortAngle,Rat.cast_div,Rat.cast_ofNat]
    all_goals ring

/-! ### The packed certificate

Both gain formulas are mirrored by `IE` expressions, evaluated by the packed Taylor models of
`PackedModels` (with their own root, reciprocal, sine and cosine checks), and their degree-10
Bernstein coefficients are checked by the kernel in natural-number arithmetic. -/

section packed
open PackedModels

/-- Expressions of packed models over time, radius and position. -/
abbrev IExpr := IE (Fin 3)
def lq (n d : ℕ) : IExpr := .lit (.q n d)
def timeI : IExpr := .var 0
def radiusI : IExpr := .var 1
def positionI : IExpr := .var 2
def sineI : IExpr := .sin timeI
def cosineI : IExpr := .cos timeI
def rI : IExpr := .sqrt (radiusI-positionI^2)
def UI : IExpr := .sqrt (radiusI-(2-positionI)^2)
def VI : IExpr := 3-UI
def YI : IExpr := .sqrt (radiusI-VI^2)
def vI : IExpr := 2-YI
def wI : IExpr := .sqrt (radiusI-vI^2)
def firstI : IExpr := 2-cosineI*(rI-1)+sineI*positionI
def secondI : IExpr := 1+cosineI*vI-sineI*(wI-1)
def etaI : IExpr := vI/wI
def lambdaI : IExpr := cosineI+etaI*sineI
def kI : IExpr := lambdaI*VI/YI
def ellI : IExpr := kI*(2-positionI)/UI
def cI : IExpr := firstI/secondI
def normZeroI : IExpr := .sqrt (ellI^2+cI^2)
def normAtI (a : IExpr) : IExpr := .sqrt (ellI^2+cI^2-2*ellI*cI*(.sin a))
def jDI : IExpr :=
  (sineI+lq 13 12)/cosineI-(.sqrt radiusI)*
    (cI*sineI/(cosineI^2*((.sqrt (1+cI^2/cosineI^2))+(.sqrt (1+cI^2))))+
      2*ellI/(normZeroI+normAtI timeI))
def bI : IExpr := lq 9 100
def sinBI : IExpr := .sin bI
def cosBI : IExpr := .cos bI
def tanHalfBI : IExpr := sinBI/(1+cosBI)
def jBI : IExpr :=
  tanHalfBI*(1/cosBI-cosineI)+(lq 13 12)/cosBI+sineI-(.sqrt radiusI)*
    (cI*sinBI/(cosBI^2*((.sqrt (ellI^2+cI^2/cosBI^2))+normZeroI))+
      2*ellI*(cosineI+sineI*tanHalfBI)/(normAtI (timeI-bI)+normAtI timeI))

theorem jDI_eq : jDI.toExpr=jDE := rfl
theorem jBI_eq : jBI.toExpr=jBE := rfl

/-- The models work at scale `2 ^ 64` with total degree `8`. -/
def config : Config := ⟨64,8,168⟩

theorem config_valid : config.Valid := ⟨by decide,by decide⟩

def timeModelI : Model :=
  Model.add config (Model.lit config 13 100) (Model.mul config (Model.lit config 3 100) (Model.X config))
/-- The center of `[qLower, qUpper]`, widened by its half-width `67069 / 10 ^ 9 ≤ r / 2 ^ 64`. -/
def radiusModelI : Model := Model.widen (Model.lit config 3915467069 1000000000) 1237204678279626
def positionModelI : Model :=
  Model.add config (Model.add config (Model.lit config 1 1)
    (Model.neg (Model.mul config (Model.lit config 51 80) timeModelI)))
    (Model.mul config (Model.lit config 7 4000) (Model.Y config))
def modelsI : Fin 3 → Model := ![timeModelI,radiusModelI,positionModelI]

theorem models_contain {q t u x y : ℝ}
    (hq : q∈Icc (CriticalEPolynomials.qLower:ℝ) (CriticalEPolynomials.qUpper:ℝ))
    (hx : |x|≤1) (hy : |y|≤1)
    (ht : t=13/100+(3/100)*x) (hu : u=1-(51/80)*t+(7/4000)*y) :
    ∀ i,(modelsI i).Contains config x y (values q t u i) := by
  have hc := config_valid
  have hl (n : ℤ) (d : ℕ) := Model.contains_lit config n d (x := x) (y := y)
  have htime : timeModelI.Contains config x y t := by
    have h := Model.contains_add hc (hl 13 100) (Model.contains_mul hc hx hy (hl 3 100)
      (Model.contains_X hc x y))
    have e : t=((13:ℤ):ℝ)/((100:ℕ):ℝ)+((3:ℤ):ℝ)/((100:ℕ):ℝ)*x := by rw [ht]; push_cast; ring
    rw [e]
    exact h
  have hrad : radiusModelI.Contains config x y q := by
    apply Model.contains_widen (hl 3915467069 1000000000)
    simp only [CriticalEPolynomials.qLower,CriticalEPolynomials.qUpper] at hq
    push_cast at hq ⊢
    rw [abs_le]
    have : (67069:ℝ)/1000000000≤1237204678279626/2^config.K := by
      rw [show config.K=64 from rfl]; norm_num
    constructor <;> linarith [hq.1,hq.2]
  have hpos : positionModelI.Contains config x y u := by
    have h := Model.contains_add hc (Model.contains_add hc (hl 1 1)
      (Model.contains_neg (Model.contains_mul hc hx hy (hl 51 80) htime)))
      (Model.contains_mul hc hx hy (hl 7 4000) (Model.contains_Y hc x y))
    have e : u=((1:ℤ):ℝ)/((1:ℕ):ℝ)+-(((51:ℤ):ℝ)/((80:ℕ):ℝ)*t)+((7:ℤ):ℝ)/((4000:ℕ):ℝ)*y := by
      rw [hu]; push_cast; ring
    rw [e]
    exact h
  intro i
  fin_cases i
  · exact htime
  · exact hrad
  · exact hpos

/-- Everything the kernel checks. -/
def certificate : Bool :=
  check config 10 modelsI jDI 0 1 true && jDI.seedFree &&
    check config 10 modelsI jBI 7 500 true && jBI.seedFree

theorem certificate_eq : certificate=true := by decide +kernel

end packed

theorem reserves {q t u x y : ℝ}
    (hq : q∈Icc (CriticalEPolynomials.qLower:ℝ) (CriticalEPolynomials.qUpper:ℝ))
    (hx : |x|≤1) (hy : |y|≤1)
    (ht : t=13/100+(3/100)*x) (hu : u=1-(51/80)*t+(7/4000)*y) :
    0<Expr.value (values q t u) jDE ∧ (7/500:ℝ)<Expr.value (values q t u) jBE := by
  have hc := certificate_eq
  simp only [certificate,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hD,hDs⟩,hB⟩,hBs⟩ := hc
  have hw := models_contain hq hx hy ht hu
  have h1 := PackedModels.check_lt config_valid hD hx hy hw (PackedModels.IE.seedsOK_of_seedFree _ hDs)
  have h2 := PackedModels.check_lt config_valid hB hx hy hw (PackedModels.IE.seedsOK_of_seedFree _ hBs)
  rw [← jDI_eq,PackedModels.IE.value_toExpr]
  rw [← jBI_eq,PackedModels.IE.value_toExpr]
  norm_num at h1 h2
  exact ⟨h1,h2⟩

theorem whole_strip {q t u : ℝ}
    (hq : q∈Icc (CriticalEPolynomials.qLower:ℝ) (CriticalEPolynomials.qUpper:ℝ))
    (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : u∈Icc (499/500-(127/200)*t) (501/500-(16/25)*t)) :
    0<jD (Real.sqrt q) (CriticalEFamily.ell q t u) (CriticalEFamily.c q t u) t ∧
    (7/500:ℝ)<jB (Real.sqrt q) (CriticalEFamily.ell q t u) (CriticalEFamily.c q t u) t := by
  obtain ⟨x,hxdef⟩ : ∃ x : ℝ,x=(t-13/100)/(3/100) := ⟨_,rfl⟩
  obtain ⟨y,hydef⟩ : ∃ y : ℝ,y=(u-(1-(51/80)*t))/(7/4000) := ⟨_,rfl⟩
  have hx : |x|≤1 := by rw [abs_le,hxdef]; constructor <;> linarith [ht.1,ht.2]
  have hy : |y|≤1 := by
    rw [abs_le,hydef]; constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
  have htime : t=13/100+(3/100)*x := by rw [hxdef]; ring
  have hpos : u=1-(51/80)*t+(7/4000)*y := by rw [hydef]; ring
  obtain ⟨hD,hB⟩ := reserves hq hx hy htime hpos
  obtain ⟨heD,heB⟩ := expression_values q t u
  rw [heD] at hD
  rw [heB] at hB
  exact ⟨hD,hB⟩

theorem minimizing_strip {q t : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    0<jD (Real.sqrt q) (CriticalEFamily.ell q t (minimizingPosition q t))
      (CriticalEFamily.c q t (minimizingPosition q t)) t ∧
    (7/500:ℝ)<jB (Real.sqrt q) (CriticalEFamily.ell q t (minimizingPosition q t))
      (CriticalEFamily.c q t (minimizingPosition q t)) t := by
  have hq' : q∈Icc (CriticalEPolynomials.qLower:ℝ) (CriticalEPolynomials.qUpper:ℝ) := by
    simpa [CriticalEPolynomials.qLower,CriticalEPolynomials.qUpper,qLow,qTrial] using hq
  have hu := CriticalEPosition.minimizingPosition_strip hq' ht
  exact whole_strip hq' ht ⟨hu.1.le,hu.2.le⟩

end SquaresInCircles.Eight.CriticalNegativeTPolynomials
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalNegativeTGain
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open CriticalECoefficients CriticalEExclusion CriticalNegativeTPolynomials
open FlatTStress SoleNormGain SingleAngleConcavity

theorem sqrt_difference {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hden : 0<Real.sqrt a+Real.sqrt b) :
    Real.sqrt a-Real.sqrt b=(a-b)/(Real.sqrt a+Real.sqrt b) := by
  apply (eq_div_iff hden.ne').2
  nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb]

theorem secant_norm_difference {a c s : ℝ} (hc : 0<c) (hcos : 0<Real.cos s) :
    Real.sqrt (a^2+c^2/Real.cos s^2)-Real.sqrt (a^2+c^2)=
      c^2*Real.sin s^2/(Real.cos s^2*
        (Real.sqrt (a^2+c^2/Real.cos s^2)+Real.sqrt (a^2+c^2))) := by
  have hn : 0<Real.sqrt (a^2+c^2) := Real.sqrt_pos.mpr (by positivity)
  have hd : 0<Real.sqrt (a^2+c^2/Real.cos s^2)+Real.sqrt (a^2+c^2) :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hn
  rw [sqrt_difference (by positivity) (by positivity) hd]
  field_simp [hcos.ne',hd.ne']
  nlinarith [Real.sin_sq_add_cos_sq s]

theorem negative_norm_difference {l c t : ℝ} (hl : 0<l) (hc : 0<c)
    (ht : t∈Icc 0 frameCap) :
    Real.sqrt (l^2+c^2)-Real.sqrt (l^2+c^2-2*l*c*Real.sin t)=
      2*l*c*Real.sin t/
        (Real.sqrt (l^2+c^2)+Real.sqrt (l^2+c^2-2*l*c*Real.sin t)) := by
  have hneg : 0<l^2+c^2-2*l*c*Real.sin t := by
    simpa only [Real.sin_neg,mul_neg,sub_eq_add_neg] using
      pair_radicand_pos hl hc (by simpa [abs_of_nonneg ht.1] using ht.2 : |-t|≤frameCap)
  have hzero : 0<Real.sqrt (l^2+c^2) := Real.sqrt_pos.mpr (by positivity)
  rw [sqrt_difference (by positivity) hneg.le
    (add_pos_of_pos_of_nonneg hzero (Real.sqrt_nonneg _))]
  congr 1
  ring

theorem TD_factor {R l c t : ℝ} (hl : 0<l) (hc : 0<c)
    (ht : t∈Icc 0 frameCap) :
    secantCharge R c 1 t-V R l c t=c*Real.sin t*jD R l c t := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hD := secant_norm_difference (a := 1) hc hcos
  have hB := negative_norm_difference hl hc ht
  have hbase : c*(1/Real.cos t-1+(13/12)*(Real.sin t/Real.cos t))-
      c*(Real.cos t-1)=c*Real.sin t*((Real.sin t+13/12)/Real.cos t) := by
    field_simp [hcos.ne']
    nlinarith [Real.sin_sq_add_cos_sq t]
  calc
    secantCharge R c 1 t-V R l c t=
        (c*(1/Real.cos t-1+(13/12)*(Real.sin t/Real.cos t))-c*(Real.cos t-1))-
          R*((Real.sqrt (1+c^2/Real.cos t^2)-Real.sqrt (1+c^2))+
            (Real.sqrt (l^2+c^2)-Real.sqrt (l^2+c^2-2*l*c*Real.sin t))) := by
      simp only [secantCharge,V,pairNorm,Real.sin_neg,Real.sin_zero,mul_zero,
        add_zero,Real.tan_eq_sin_div_cos,div_pow,one_pow]
      ring_nf
    _=c*Real.sin t*jD R l c t := by
      rw [hbase,show Real.sqrt (1+c^2/Real.cos t^2)-Real.sqrt (1+c^2)=
        c^2*Real.sin t^2/(Real.cos t^2*
          (Real.sqrt (1+c^2/Real.cos t^2)+Real.sqrt (1+c^2))) by simpa using hD,hB]
      dsimp [jD]
      ring

theorem BT_factor {R l c t : ℝ} (hl : 0<l) (hc : 0<c)
    (ht : t∈Icc shortAngle frameCap) :
    secantCharge R c l shortAngle+V R l c (t-shortAngle)-V R l c t=
      c*Real.sin shortAngle*jB R l c t := by
  let b : ℝ := shortAngle
  let a : ℝ := Real.sin b/(1+Real.cos b)
  have hb : b∈Icc 0 frameCap := by norm_num [b,shortAngle,frameCap]
  have hcB := transport_cos_pos (by rw [abs_of_nonneg hb.1]; exact hb.2)
  have hc1 : 0<1+Real.cos b := by linarith
  have hhalf : Real.sin b*a=1-Real.cos b := by
    dsimp only [a]
    rw [mul_div_assoc',div_eq_iff hc1.ne']
    nlinarith [Real.sin_sq_add_cos_sq b]
  have hcosSub : Real.cos (t-b)-Real.cos t=
      Real.sin b*(Real.sin t-Real.cos t*a) := by
    rw [Real.cos_sub]
    nlinarith [congrArg (fun x : ℝ => Real.cos t*x) hhalf]
  have hsinSub : Real.sin t-Real.sin (t-b)=
      Real.sin b*(Real.cos t+Real.sin t*a) := by
    rw [Real.sin_sub]
    nlinarith [congrArg (fun x : ℝ => Real.sin t*x) hhalf]
  have hsec : 1/Real.cos b-1=Real.sin b*a/Real.cos b := by
    rw [hhalf]
    field_simp [hcB.ne']
  have ht0 : t∈Icc 0 frameCap := ⟨hb.1.trans ht.1,ht.2⟩
  have hd : t-b∈Icc 0 frameCap := ⟨sub_nonneg.mpr ht.1,by linarith [ht.2,hb.1]⟩
  have hr (u : ℝ) (hu : u∈Icc 0 frameCap) : 0<l^2+c^2-2*l*c*Real.sin u := by
    simpa only [Real.sin_neg,mul_neg,sub_eq_add_neg] using
      pair_radicand_pos hl hc (by simpa [abs_of_nonneg hu.1] using hu.2 : |-u|≤frameCap)
  have hshift : Real.sqrt (l^2+c^2-2*l*c*Real.sin (t-b))-
      Real.sqrt (l^2+c^2-2*l*c*Real.sin t)=
      2*l*c*Real.sin b*(Real.cos t+Real.sin t*a)/
        (Real.sqrt (l^2+c^2-2*l*c*Real.sin (t-b))+
          Real.sqrt (l^2+c^2-2*l*c*Real.sin t)) := by
    rw [sqrt_difference (hr _ hd).le (hr _ ht0).le
      (add_pos (Real.sqrt_pos.mpr (hr _ hd)) (Real.sqrt_pos.mpr (hr _ ht0)))]
    congr 1
    nlinarith [congrArg (fun x : ℝ => 2*l*c*x) hsinSub]
  have hnew := secant_norm_difference (a := l) hc hcB
  have hbase : c*(1/Real.cos b-1+(13/12)*(Real.sin b/Real.cos b))+
      c*(Real.cos (t-b)-1)-c*(Real.cos t-1)=
      c*Real.sin b*(a*(1/Real.cos b-Real.cos t)+(13/12)/Real.cos b+Real.sin t) := by
    rw [hsec]
    linear_combination c*hcosSub
  calc
    secantCharge R c l b+V R l c (t-b)-V R l c t=
        (c*(1/Real.cos b-1+(13/12)*(Real.sin b/Real.cos b))+
          c*(Real.cos (t-b)-1)-c*(Real.cos t-1))-
          R*((Real.sqrt (l^2+c^2/Real.cos b^2)-Real.sqrt (l^2+c^2))+
            (Real.sqrt (l^2+c^2-2*l*c*Real.sin (t-b))-
              Real.sqrt (l^2+c^2-2*l*c*Real.sin t))) := by
      simp only [secantCharge,V,pairNorm,Real.sin_neg,Real.sin_zero,mul_zero,
        add_zero,Real.tan_eq_sin_div_cos,div_pow]
      ring_nf
    _=c*Real.sin b*jB R l c t := by
      rw [hbase,hnew,hshift]
      dsimp [jB,a,b]
      ring

/-- An error of at most .011d suffices at the shifted BT endpoint. -/
theorem A_lower {R t k l c eta d : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t k l c eta) (hd : d∈Icc 0 (1/5:ℝ)) :
    V R l c d-(11/1000)*d≤Vnu R l k l d := by
  have ho := h.order
  have hd' : d∈Icc 0 frameCap := ⟨hd.1,by show d≤7/10; linarith [hd.2]⟩
  have hpen : 0≤(c-l)*(1-Real.cos d) :=
    mul_nonneg (sub_nonneg.mpr ho.2.2.1) (by linarith [Real.cos_le_one d])
  by_cases hck : c≤k
  · have hm := HalfRatioNormGain.larger_monotone hR.1 h.ell_pos ho.2.2.1 hck
      ho.2.2.2.2.2.1 hd'
    dsimp [V,Vnu,normGain] at *
    linarith [hd.1]
  · have hkc : k≤c := le_of_lt (lt_of_not_ge hck)
    have hm := coefficient_short hR ho.1 hkc ho.2.2.2.1
      (show l≤(18/25)*k by linarith [h.ell_k]) hd
    have hdif := mul_le_mul_of_nonneg_left h.difference.le
      (show 0≤(11/20)*d by linarith [hd.1])
    dsimp [V,Vnu,normGain] at *
    nlinarith

theorem TD_endpoint {q t : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    V (Real.sqrt q) (L q t) (Cc q t) t<secantCharge (Real.sqrt q) (Cc q t) 1 t := by
  have h := coefficient_bounds hq ht
  have hj := (minimizing_strip hq ht).1
  change 0<jD (Real.sqrt q) (L q t) (Cc q t) t at hj
  have hs : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [ht.1]) (by linarith [ht.2,Real.pi_gt_three])
  have hp := mul_pos (mul_pos (show 0<Cc q t by linarith [h.c_lower]) hs) hj
  rw [← TD_factor h.ell_pos (by linarith [h.c_lower]) h.angle] at hp
  linarith

theorem BT_endpoints {q t : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    V (Real.sqrt q) (L q t) (Cc q t) t+11/10000<
      secantCharge (Real.sqrt q) (Cc q t) (L q t) shortAngle+
        V (Real.sqrt q) (L q t) (Cc q t) (t-shortAngle) ∧
    V (Real.sqrt q) (L q t) (Cc q t) t+3/10000<
      secantCharge (Real.sqrt q) (Cc q t) (L q t) shortAngle+
        Vnu (Real.sqrt q) (L q t) (K q t) (L q t) (t-shortAngle) := by
  have h := coefficient_bounds hq ht
  have hj := (minimizing_strip hq ht).2
  change (7/500:ℝ)<jB (Real.sqrt q) (L q t) (Cc q t) t at hj
  have hs : (89/1000:ℝ)<Real.sin shortAngle := by
    have hh := sin_lower_seven (show (0:ℝ)≤ shortAngle by norm_num [shortAngle])
    norm_num [shortAngle] at hh ⊢
    linarith
  have hcs : (37/40)*(89/1000)<Cc q t*Real.sin shortAngle :=
    mul_lt_mul'' h.c_lower hs (by norm_num) (by norm_num)
  have hp : (11/10000:ℝ)<Cc q t*Real.sin shortAngle*jB (Real.sqrt q) (L q t) (Cc q t) t := by
    have hm := mul_lt_mul'' hcs hj (by norm_num) (by norm_num)
    linarith
  rw [← BT_factor h.ell_pos (by linarith [h.c_lower])
    (show t∈Icc shortAngle frameCap by constructor <;> dsimp [shortAngle,frameCap] <;>
      linarith [ht.1,ht.2])] at hp
  have hq0 : 0≤q := by norm_num [qLow] at hq; linarith [hq.1]
  have hR : Real.sqrt q≤2 := by
    have hq2 := Real.sq_sqrt hq0
    norm_num [qTrial] at hq
    nlinarith [Real.sqrt_nonneg q,hq.2]
  have hd : t-shortAngle∈Icc 0 (1/5:ℝ) := by
    constructor <;> dsimp [shortAngle] <;> linarith [ht.1,ht.2]
  have hA := A_lower ⟨Real.sqrt_nonneg q,hR⟩ h hd
  have hshort : t-shortAngle≤7/100 := by dsimp [shortAngle]; linarith [ht.2]
  constructor <;> nlinarith

end SquaresInCircles.Eight.CriticalNegativeTGain
end
end
end
