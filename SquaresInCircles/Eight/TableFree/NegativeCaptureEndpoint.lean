module

public import SquaresInCircles.Eight.TableFree.NegativeCapturePolynomials
public import SquaresInCircles.Eight.TableFree.NegativeCaptureModel
public import SquaresInCircles.Eight.TableFree.NegativeLargeDEEndpoint

/-!
# Positive actual endpoints for canonical negative capture

Uncompiled reconstruction.  The original cosine is retained in the
cleared identity.  Positive circle masses majorize the exact support
norms only after the four geometric vertices have been selected.
The two short-angle vertices pay their proved original-model error.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.NegativeCaptureEndpoint
open NegativeCaptureData NegativeCapturePolynomials
open NegativeCaptureShortAngle

abbrev C6 := NegativeLargeDEEndpoint.C6
abbrev massSupport := NegativeLargeDEEndpoint.massSupport

theorem cleared_positive {b : Band} {s c : ℝ} (hs : s∈domain b)
    (hc : 0≤c) (hunit : c^2+s^2=1) (j : Fin 4) :
    0<aeval s (constantNumerator b j)+aeval s (cosineNumerator b j)*c := by
  have hdom : s∈Icc (0:ℝ) (27/100) := ⟨by linarith [(domain_full hs).1],(domain_full hs).2⟩
  have hcos := NegativeLargeDEEndpoint.cosine_sandwich hdom hc hunit
  have hB := cosine_upper hs j
  have hM : 0≤(cosineReserve b:ℝ) := by cases b <;> norm_num [cosineReserve]
  have h8 : 0≤s^8/20 := div_nonneg (pow_nonneg hdom.1 8) (by norm_num)
  have hcompare :
      aeval s (cosineNumerator b j)*C6 s-(cosineReserve b:ℝ)*(s^8/20)≤
        aeval s (cosineNumerator b j)*c := by
    by_cases hsign : 0≤aeval s (cosineNumerator b j)
    · have h1 := mul_le_mul_of_nonneg_left hcos.1 hsign
      have h2 := mul_le_mul_of_nonneg_right hB.le h8
      nlinarith
    · exact le_trans (by nlinarith [mul_nonneg hM h8])
        (mul_le_mul_of_nonpos_left hcos.2 (le_of_not_ge hsign))
  have hP := polynomial_positive hs j
  have he : aeval s (P b j)=
      aeval s (constantNumerator b j)+aeval s (cosineNumerator b j)*C6 s-
        (cosineReserve b:ℝ)*(s^8/20) := by
    simp [P,cosineSix,C6,NegativeLargeDEEndpoint.C6]
    ring
  rw [he] at hP
  linarith

def massValue (b : Band) (j : Fin 4) (s : ℝ) (i : Fin 5) : ℝ := aeval s (mass b j i)

/-- Expanded circle-mass lower bound.  At j=2,3 the constants sigma and
chi retain their actual, nonunit squared sum. -/
def rationalDefect (j : Fin 4) (a f mA mB mD mH mE s c : ℝ) : ℝ :=
  3+2*a+3/500+f+2*(307/1000)*s+f*s+
    (if j=0 ∨ j=1 then 2 else if j=2 then χ+1+σ*s
      else 1+(1+(13/12)*σ)/χ+σ*s)+
    (2*f+(if j=0 then 1 else if j=1 then 0 else χ))*c+
    (if j=1 then (1+(13/12)*s)/c else 0)-(delta j:ℝ)-
    qTrial*(mA+mB+mD+mH+s*mE)-
    (if j=0 then c^2+(a+3/500-s)^2
      else if j=2 then χ^2+(a+3/500-σ)^2 else 1+(a+3/500)^2)/(4*mA)-
    (if j=0 ∨ j=1 then 1+a^2
      else (c*χ+s*σ)^2+(a-s*χ+c*σ)^2)/(4*mB)-
    (f^2+1)/(4*mD)-
    ((f*c+(307/1000)*s)^2+
      (if j=1 then 1/c^2 else if j=3 then 1/χ^2 else 1))/(4*mH)-
    s*(f^2+(307/1000)^2)/(4*mE)

theorem cleared_identity {b : Band} {s c : ℝ} (hs : s∈domain b)
    (hc : c≠0) (hunit : c^2+s^2=1) (j : Fin 4) :
    aeval s (constantNumerator b j)+aeval s (cosineNumerator b j)*c=
      aeval s (denominator b j)*(if j=1 then c^2 else 1)*
        rationalDefect j (a b s) (f b s)
          (massValue b j s 0) (massValue b j s 1) (massValue b j s 2)
          (massValue b j s 3) (massValue b j s 4) s c := by
  have hma := (mass_positive hs j 0).ne'
  have hmb := (mass_positive hs j 1).ne'
  have hmd := (mass_positive hs j 2).ne'
  have hmh := (mass_positive hs j 3).ne'
  have hme := (mass_positive hs j 4).ne'
  have hχ : χ≠0 := by norm_num [χ,chi]
  have hA : c^2+(a b s+3/500-s)^2=
      1+(a b s+3/500)^2-2*(a b s+3/500)*s := by nlinarith
  have hAShort : χ^2+(a b s+3/500-σ)^2=
      χ^2+σ^2+(a b s+3/500)^2-2*σ*(a b s+3/500) := by ring
  have hB : (c*χ+s*σ)^2+(a b s-s*χ+c*σ)^2=
      χ^2+σ^2+(a b s)^2-2*χ*a b s*s+2*σ*a b s*c := by
    nlinarith [congrArg (fun x : ℝ => (χ^2+σ^2)*x) hunit]
  have hH : (f b s*c+(307/1000)*s)^2=
      (f b s)^2*(1-s^2)+(307/1000)^2*s^2+2*(307/1000)*f b s*s*c := by
    nlinarith [congrArg (fun x : ℝ => (f b s)^2*x) hunit]
  have hsc : 1-s^2=c^2 := by linarith
  fin_cases j <;>
    simp only [rationalDefect,Fin.isValue,ite_true,ite_false,Fin.reduceEq,
      or_self,or_true,true_or,false_or,or_false,hA,hAShort,hB,hH] <;>
    simp only [constantNumerator,cosineNumerator,denominator,otherA,otherB,otherD,
      otherH,otherE,base,totalMass,scale,endpointConstant,endpointCosine,secantSquare,
      normA,normB,normBCosine,Fin.isValue,Fin.reduceEq,ite_true,ite_false,
      or_self,or_true,true_or,false_or,or_false,map_add,map_sub,map_mul,map_pow,
      map_one,map_zero,aeval_C,aeval_X] <;>
    norm_num [Q,qTrial,eta,k,K,delta,χ,σ,chi,sigma] <;>
    dsimp [a,f,massValue] at * <;>
    simp only [hsc] <;>
    field_simp [hma,hmb,hmd,hmh,hme,hc,hχ] <;>
    ring

theorem rational_positive {b : Band} {s c : ℝ} (hs : s∈domain b)
    (hc : 0<c) (hunit : c^2+s^2=1) (j : Fin 4) :
    0<rationalDefect j (a b s) (f b s)
      (massValue b j s 0) (massValue b j s 1) (massValue b j s 2)
      (massValue b j s 3) (massValue b j s 4) s c := by
  have hp := cleared_positive hs hc.le hunit j
  rw [cleared_identity hs hc.ne' hunit j] at hp
  have hden : 0<aeval s (denominator b j) := by
    simp only [denominator,map_mul,aeval_C]
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num)
      (mass_positive hs j 0)) (mass_positive hs j 1))
        (mass_positive hs j 2)) (mass_positive hs j 3)) (mass_positive hs j 4)
  have hscale : 0<(if j=1 then c^2 else 1) := by split_ifs <;> positivity
  by_contra! hbad
  have hn := mul_nonpos_of_nonneg_of_nonpos (mul_pos hden hscale).le hbad
  linarith

theorem rational_is_mass_defect (j : Fin 4)
    (a f mA mB mD mH mE s c : ℝ) :
    rationalDefect j a f mA mB mD mH mE s c=
      NegativeCaptureModel.demand j a f s c-(delta j:ℝ)-
      (massSupport mA (NegativeCaptureModel.cT j s c)
          (a+3/500-NegativeCaptureModel.sT j s c)+
        massSupport mB (NegativeCaptureModel.cU j s c)
          (a-NegativeCaptureModel.sU j s c)+massSupport mD f 1+
        massSupport mH (f*c+(307/1000)*s) (NegativeCaptureModel.secE j s c)+
        s*massSupport mE f (307/1000)) := by
  fin_cases j <;>
    simp [rationalDefect,NegativeCaptureModel.demand,NegativeCaptureModel.cT,
      NegativeCaptureModel.sT,NegativeCaptureModel.cU,NegativeCaptureModel.sU,
      NegativeCaptureModel.secE,NegativeCaptureModel.tanE,
      massSupport,NegativeLargeDEEndpoint.massSupport,div_pow] <;>
    ring

theorem rational_le_model {b : Band} {s c : ℝ} (hs : s∈domain b) (j : Fin 4) :
    rationalDefect j (a b s) (f b s)
      (massValue b j s 0) (massValue b j s 1) (massValue b j s 2)
      (massValue b j s 3) (massValue b j s 4) s c≤
        NegativeCaptureModel.defect j (a b s) (f b s) s c-(delta j:ℝ) := by
  have hs0 : 0≤s := by linarith [(domain_full hs).1]
  have hA := NegativeLargeDEEndpoint.support_le_mass (mass_positive hs j 0)
    (NegativeCaptureModel.cT j s c) (a b s+3/500-NegativeCaptureModel.sT j s c)
  have hB := NegativeLargeDEEndpoint.support_le_mass (mass_positive hs j 1)
    (NegativeCaptureModel.cU j s c) (a b s-NegativeCaptureModel.sU j s c)
  have hD := NegativeLargeDEEndpoint.support_le_mass (mass_positive hs j 2) (f b s) 1
  have hH := NegativeLargeDEEndpoint.support_le_mass (mass_positive hs j 3)
    (f b s*c+(307/1000)*s) (NegativeCaptureModel.secE j s c)
  have hE := mul_le_mul_of_nonneg_left
    (NegativeLargeDEEndpoint.support_le_mass (mass_positive hs j 4) (f b s) (307/1000)) hs0
  have hE' : NegativeCaptureStress.support (f b s*s) ((307/1000)*s)≤
      s*massSupport (massValue b j s 4) (f b s) (307/1000) := by
    rw [mul_comm (f b s),mul_comm (307/1000:ℝ),
      NegativeLargeDEEndpoint.support_smul hs0]
    simpa [massValue] using hE
  rw [rational_is_mass_defect]
  dsimp [NegativeCaptureModel.defect,massValue] at *
  linarith

/-- Each exact trigonometric vertex is positive at the original trial
radius.  The one fixed-angle error has already been paid in delta_j. -/
theorem vertex_positive {b : Band} {α : ℝ}
    (hα : α∈Icc 0 (27/100:ℝ)) (hs : Real.sin α∈domain b) (j : Fin 4) :
    0<NegativeCaptureStress.defect (a b (Real.sin α)) (f b (Real.sin α)) α
      (NegativeCaptureModel.tVertex j α) (NegativeCaptureModel.uVertex j α)
      (NegativeCaptureModel.eVertex j α) := by
  have hc : 0<Real.cos α := by
    linarith [(NegativeLargeDECalculus.short_trig hα).1]
  have hunit : (Real.cos α)^2+(Real.sin α)^2=1 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  exact (rational_positive hs hc hunit j).trans_le
    ((rational_le_model hs j).trans
      (NegativeCaptureModel.model_le_actual j (a b (Real.sin α)) (f b (Real.sin α)) α))

end SquaresInCircles.Eight.TableFree.NegativeCaptureEndpoint
