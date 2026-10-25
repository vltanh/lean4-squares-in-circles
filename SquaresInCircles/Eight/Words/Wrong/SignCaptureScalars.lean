module

public import SquaresInCircles.Eight.Owners.Endpoint.BudgetScalars
public import SquaresInCircles.Eight.Words.Wrong.SignWeightPolynomial

/-!
# Eight squares: actual radical endpoint bounds for small wrong intermediate signs

The auxiliary quadratic tangents and every
weight are the printed exact rational polynomials.  Their whole-interval
positivity is transferred to the original trigonometric radical formulas.
No numerical enclosure or polynomial comparison is assumed as an input
to any concrete weight-family result.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.WrongSignCaptureScalars
open PositiveAngularEnvelope PairNormCalculus EndpointRotationPenalty EndpointBudgetScalars
open Polynomial

def U_T (rho a b : ℝ) : ℝ :=
  R*(pairNorm a b (-rho)+pairNorm 1 b 0)-2*a/5-8/5-2*b-a*Real.cos rho+charge*rho
def U_G (rho a b : ℝ) : ℝ :=
  R*(pairNorm a b 0+pairNorm 1 b (-rho))-7*a/5-3/5-2*b-Real.cos rho+charge*rho

def Admissible (a b : ℝ) : Prop :=
  a∈Icc (3/4 : ℝ) 1 ∧ b∈Icc (13/20 : ℝ) (23/25) ∧ b≤(23/25)*a

def sine7 (t : ℝ) : ℝ := t-t^3/6+t^5/120-t^7/5040
def cosine6 (t : ℝ) : ℝ := 1-t^2/2+t^4/24-t^6/720

theorem radius_reserves :
    R<(WrongSignWeightPolynomial.Rbar:ℝ) ∧
      (WrongSignWeightPolynomial.Sbar:ℝ)<S0 ∧
      (WrongSignWeightPolynomial.limit:ℝ)<S0+(1/10000 : ℝ) := by
  have hR := R_sq
  have hS := Real.sq_sqrt (show 0≤qCap-1 by norm_num [qCap])
  have hS0 := Real.sqrt_nonneg (qCap-1)
  dsimp [WrongSignWeightPolynomial.Rbar,WrongSignWeightPolynomial.Sbar,
    WrongSignWeightPolynomial.limit,S0,qCap] at *
  constructor
  · nlinarith [R_nonneg]
  constructor <;> nlinarith

@[simp] theorem S7_eval (z : ℚ[X]) (x : ℝ) :
    aeval x (WrongSignWeightPolynomial.S7 z)=sine7 (aeval x z) := by
  simp [WrongSignWeightPolynomial.S7,sine7]
  ring

@[simp] theorem C6_eval (z : ℚ[X]) (x : ℝ) :
    aeval x (WrongSignWeightPolynomial.C6 z)=cosine6 (aeval x z) := by
  simp [WrongSignWeightPolynomial.C6,cosine6]
  ring

theorem T_eval (a b z r₁ r₂ : ℚ[X]) (x : ℝ) :
    aeval x (WrongSignWeightPolynomial.T a b z r₁ r₂)=
      2*aeval x r₁*aeval x r₂*((WrongSignWeightPolynomial.limit:ℝ)+
        2*aeval x a/5+8/5+2*aeval x b+aeval x a*cosine6 (aeval x z)-charge*aeval x z)-
      (WrongSignWeightPolynomial.Rbar:ℝ)*
        (aeval x r₂*((aeval x a)^2+(aeval x b)^2-
          2*aeval x a*aeval x b*sine7 (aeval x z)+(aeval x r₁)^2)+
          aeval x r₁*(1+(aeval x b)^2+(aeval x r₂)^2)) := by
  simp only [WrongSignWeightPolynomial.T,WrongSignWeightPolynomial.targetT,
    WrongSignWeightPolynomial.radicandT,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,
    S7_eval,C6_eval,eq_ratCast,WrongSignWeightPolynomial.charge,charge]
  push_cast
  ring

theorem G_eval (a b z r₁ r₂ : ℚ[X]) (x : ℝ) :
    aeval x (WrongSignWeightPolynomial.G a b z r₁ r₂)=
      2*aeval x r₁*aeval x r₂*((WrongSignWeightPolynomial.limit:ℝ)+
        7*aeval x a/5+3/5+2*aeval x b+cosine6 (aeval x z)-charge*aeval x z)-
      (WrongSignWeightPolynomial.Rbar:ℝ)*
        (aeval x r₂*((aeval x a)^2+(aeval x b)^2+(aeval x r₁)^2)+
          aeval x r₁*(1+(aeval x b)^2-
            2*aeval x b*sine7 (aeval x z)+(aeval x r₂)^2)) := by
  simp only [WrongSignWeightPolynomial.G,WrongSignWeightPolynomial.targetG,
    WrongSignWeightPolynomial.radicandG,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,
    S7_eval,C6_eval,eq_ratCast,WrongSignWeightPolynomial.charge,charge]
  push_cast
  ring

/-- Two positive scalar tangents bound the actual pair of norms. -/
theorem two_norms {n₁ n₂ A B e r₁ r₂ : ℝ}
    (hn₁ : 0≤n₁) (hn₂ : 0≤n₂) (hA : n₁^2≤A) (hB : n₂^2≤B)
    (hr₁ : 0<r₁) (hr₂ : 0<r₂)
    (hcertificate : 0<2*r₁*r₂*e-(WrongSignWeightPolynomial.Rbar:ℝ)*
      (r₂*(A+r₁^2)+r₁*(B+r₂^2))) :
    R*(n₁+n₂)<e := by
  have hRbar : 0≤(WrongSignWeightPolynomial.Rbar:ℝ) := by
    norm_num [WrongSignWeightPolynomial.Rbar]
  have h₁ : 2*r₁*n₁≤A+r₁^2 := by linarith [sq_nonneg (n₁-r₁)]
  have h₂ : 2*r₂*n₂≤B+r₂^2 := by linarith [sq_nonneg (n₂-r₂)]
  have h₁w := mul_le_mul_of_nonneg_left h₁ (mul_nonneg hRbar hr₂.le)
  have h₂w := mul_le_mul_of_nonneg_left h₂ (mul_nonneg hRbar hr₁.le)
  have hR := mul_le_mul_of_nonneg_right radius_reserves.1.le (add_nonneg hn₁ hn₂)
  have hscale : 0<2*r₁*r₂ := by positivity
  have hRw := mul_le_mul_of_nonneg_left hR hscale.le
  refine lt_of_mul_lt_mul_left ?_ hscale.le
  linarith

theorem negative_norm_upper {a b rho : ℝ} (ha : 0<a) (hb : 0<b)
    (hrho : rho∈Icc 0 frameCap) :
    (pairNorm a b (-rho))^2≤a^2+b^2-2*a*b*sine7 rho := by
  have hρ : |-rho|≤frameCap := by rw [abs_neg,abs_of_nonneg hrho.1]; exact hrho.2
  have hN := pairNorm_sq ha hb hρ
  have hs := sin_lower_seven hrho.1
  have hm := mul_le_mul_of_nonneg_left hs (show 0≤2*a*b by positivity)
  dsimp [sine7]
  simp only [pairEnergy,pairProduct,Real.sin_neg] at hN
  nlinarith

theorem T_transfer {a b z r₁ r₂ : ℚ[X]} {x : ℝ}
    (ha : 0<aeval x a) (hb : 0<aeval x b)
    (hz : aeval x z∈Icc 0 frameCap) (hr₁ : 0<aeval x r₁) (hr₂ : 0<aeval x r₂)
    (hP : 0<aeval x (WrongSignWeightPolynomial.T a b z r₁ r₂)) :
    U_T (aeval x z) (aeval x a) (aeval x b)<(WrongSignWeightPolynomial.limit:ℝ) := by
  have hA := negative_norm_upper ha hb hz
  have hB : (pairNorm 1 (aeval x b) 0)^2=1+(aeval x b)^2 := by
    simpa [pairEnergy,pairProduct] using pairNorm_sq (show (0:ℝ)<1 by norm_num) hb
      (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  rw [T_eval] at hP
  have hnorm := two_norms (n₁ := pairNorm (aeval x a) (aeval x b) (-aeval x z))
    (n₂ := pairNorm 1 (aeval x b) 0)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hA hB.le hr₁ hr₂ hP
  have hcos := mul_le_mul_of_nonneg_left (cos_lower_six hz.1) ha.le
  dsimp [U_T,cosine6] at *
  linarith

theorem G_transfer {a b z r₁ r₂ : ℚ[X]} {x : ℝ}
    (ha : 0<aeval x a) (hb : 0<aeval x b)
    (hz : aeval x z∈Icc 0 frameCap) (hr₁ : 0<aeval x r₁) (hr₂ : 0<aeval x r₂)
    (hP : 0<aeval x (WrongSignWeightPolynomial.G a b z r₁ r₂)) :
    U_G (aeval x z) (aeval x a) (aeval x b)<(WrongSignWeightPolynomial.limit:ℝ) := by
  have hA : (pairNorm (aeval x a) (aeval x b) 0)^2=(aeval x a)^2+(aeval x b)^2 := by
    simpa [pairEnergy,pairProduct] using pairNorm_sq ha hb
      (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hB : (pairNorm 1 (aeval x b) (-aeval x z))^2≤
      1+(aeval x b)^2-2*aeval x b*sine7 (aeval x z) := by
    simpa only [one_pow,one_mul,mul_one] using
      negative_norm_upper (show (0:ℝ)<1 by norm_num) hb hz
  rw [G_eval] at hP
  have hnorm := two_norms (n₁ := pairNorm (aeval x a) (aeval x b) 0)
    (n₂ := pairNorm 1 (aeval x b) (-aeval x z))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hA.le hB hr₁ hr₂ hP
  have hcos := cos_lower_six hz.1
  dsimp [U_G,cosine6] at *
  linarith

theorem middle_admissible {x : ℝ} (hx : x∈Icc (-(1/10) : ℝ) (1/50)) :
    Admissible (aeval x WrongSignWeightPolynomial.middleA)
      (aeval x WrongSignWeightPolynomial.middleB) := by
  have hx2 : x^2≤(1/100 : ℝ) := by
    have hh : |x|≤(1/10 : ℝ) := abs_le.mpr ⟨hx.1,by linarith [hx.2]⟩
    nlinarith [pow_le_pow_left₀ (abs_nonneg x) hh 2,sq_abs x]
  have hprod := mul_nonneg (show 0≤x+1/10 by linarith [hx.1])
    (show 0≤1/50-x by linarith [hx.2])
  simp only [Admissible,WrongSignWeightPolynomial.middleA,WrongSignWeightPolynomial.middleB,
    map_add,map_mul,map_pow,aeval_C,aeval_X,mem_Icc]
  norm_num
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,?_⟩ <;> nlinarith [sq_nonneg x]

theorem middle_auxiliaries {x : ℝ} (hx : x∈Icc (-(1/10) : ℝ) (1/50)) :
    (4/5 : ℝ)<aeval x WrongSignWeightPolynomial.middleT1 ∧
      (4/5 : ℝ)<aeval x WrongSignWeightPolynomial.middleT2 ∧
      (4/5 : ℝ)<aeval x WrongSignWeightPolynomial.middleG1 ∧
      (4/5 : ℝ)<aeval x WrongSignWeightPolynomial.middleG2 := by
  have hx2 : x^2≤(1/100 : ℝ) := by
    have hh : |x|≤(1/10 : ℝ) := abs_le.mpr ⟨hx.1,by linarith [hx.2]⟩
    nlinarith [pow_le_pow_left₀ (abs_nonneg x) hh 2,sq_abs x]
  simp only [WrongSignWeightPolynomial.middleT1,WrongSignWeightPolynomial.middleT2,
    WrongSignWeightPolynomial.middleG1,WrongSignWeightPolynomial.middleG2,
    map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X]
  norm_num
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg x,hx.1,hx.2]

theorem middle_family {rho : ℝ} (hrho : rho∈Icc (7/20 : ℝ) (47/100)) :
    ∃ a b,Admissible a b ∧ U_T rho a b<(WrongSignWeightPolynomial.limit:ℝ) ∧
      U_G rho a b<(WrongSignWeightPolynomial.limit:ℝ) := by
  let x : ℝ := rho-9/20
  have hx : x∈Icc (-(1/10) : ℝ) (1/50) := by
    dsimp [x]
    constructor <;> linarith [hrho.1,hrho.2]
  have hadm := middle_admissible hx
  have haux := middle_auxiliaries hx
  have hz : aeval x WrongSignWeightPolynomial.middleRho=rho := by
    simp [WrongSignWeightPolynomial.middleRho,x]
  have hzdom : aeval x WrongSignWeightPolynomial.middleRho∈Icc 0 frameCap := by
    rw [hz]
    exact ⟨by linarith [hrho.1],by simp only [frameCap]; linarith [hrho.2]⟩
  have ha : 0<aeval x WrongSignWeightPolynomial.middleA := by linarith [hadm.1.1]
  have hb : 0<aeval x WrongSignWeightPolynomial.middleB := by linarith [hadm.2.1.1]
  have hT := T_transfer ha hb hzdom (by linarith [haux.1]) (by linarith [haux.2.1])
    (WrongSignWeightPolynomial.middleT_positive hx)
  have hG := G_transfer ha hb hzdom (by linarith [haux.2.2.1]) (by linarith [haux.2.2.2])
    (WrongSignWeightPolynomial.middleG_positive hx)
  rw [hz] at hT hG
  exact ⟨_,_,hadm,hT,hG⟩

theorem last_admissible {x : ℝ} (hx : x∈Icc 0 (23/100 : ℝ)) :
    Admissible 1 (aeval x WrongSignWeightPolynomial.lastB) := by
  refine ⟨⟨by norm_num,by norm_num⟩,⟨?_,?_⟩,?_⟩
  all_goals
    simp only [WrongSignWeightPolynomial.lastB,WrongSignWeightPolynomial.lastRho,
      map_add,map_mul,aeval_C,aeval_X]
    norm_num
    linarith [hx.1,hx.2]

theorem last_auxiliaries {x : ℝ} (hx : x∈Icc 0 (23/100 : ℝ)) :
    (4/5 : ℝ)<aeval x WrongSignWeightPolynomial.lastT1 ∧
      (4/5 : ℝ)<aeval x WrongSignWeightPolynomial.lastT2 := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hx3 := pow_le_pow_left₀ hx.1 hx.2 3
  simp only [WrongSignWeightPolynomial.lastT1,WrongSignWeightPolynomial.lastT2,
    map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X]
  norm_num
  constructor <;> nlinarith [sq_nonneg x,pow_nonneg hx.1 3,hx.1,hx.2]

theorem U_equal_at_one (rho b : ℝ) : U_G rho 1 b=U_T rho 1 b := by
  simp only [U_G,U_T]
  ring

theorem last_family {rho : ℝ} (hrho : rho∈Icc (47/100 : ℝ) frameCap) :
    ∃ a b,Admissible a b ∧ U_T rho a b<(WrongSignWeightPolynomial.limit:ℝ) ∧
      U_G rho a b<(WrongSignWeightPolynomial.limit:ℝ) := by
  let x : ℝ := rho-47/100
  have hx : x∈Icc 0 (23/100 : ℝ) := by
    dsimp [x,frameCap] at *
    constructor <;> linarith [hrho.1,hrho.2]
  have hadm := last_admissible hx
  have haux := last_auxiliaries hx
  have hz : aeval x WrongSignWeightPolynomial.lastRho=rho := by
    simp [WrongSignWeightPolynomial.lastRho,x]
  have hzdom : aeval x WrongSignWeightPolynomial.lastRho∈Icc 0 frameCap := by
    rw [hz]
    exact ⟨by linarith [hrho.1],hrho.2⟩
  have ha : 0<aeval x (1:ℚ[X]) := by simp
  have hb : 0<aeval x WrongSignWeightPolynomial.lastB := by linarith [hadm.2.1.1]
  have hT := T_transfer ha hb hzdom (by linarith [haux.1]) (by linarith [haux.2])
    (WrongSignWeightPolynomial.lastT_positive hx)
  rw [hz] at hT
  simp only [map_one] at hT
  refine ⟨1,_,hadm,hT,?_⟩
  rw [U_equal_at_one]
  exact hT

theorem first_norm_bounds :
    pairNorm (4/5) (13/20) 0<(1030777/1000000 : ℝ) ∧
      pairNorm 1 (13/20) 0<(1192687/1000000 : ℝ) ∧
      pairNorm (4/5) (13/20) (-(7/20))<(840171/1000000 : ℝ) ∧
      pairNorm 1 (13/20) (-(7/20))<(494149/500000 : ℝ) := by
  have hr : |-(7/20 : ℝ)|≤frameCap := by norm_num [frameCap]
  have h₃ := pairNorm_sq (show (0:ℝ)<4/5 by norm_num) (show (0:ℝ)<13/20 by norm_num) hr
  have h₄ := pairNorm_sq (show (0:ℝ)<1 by norm_num) (show (0:ℝ)<13/20 by norm_num) hr
  have hs := sin_lower_seven (show (0:ℝ)≤7/20 by norm_num)
  simp only [pairEnergy,pairProduct,Real.sin_neg] at h₃ h₄
  refine ⟨?_,?_,?_,?_⟩
  · rw [pairNorm_zero,Real.sqrt_lt' (by norm_num)]
    norm_num
  · rw [pairNorm_zero,Real.sqrt_lt' (by norm_num)]
    norm_num
  · apply lt_of_pow_lt_pow_left₀ 2 (by norm_num)
    rw [h₃]
    linarith
  · apply lt_of_pow_lt_pow_left₀ 2 (by norm_num)
    rw [h₄]
    linarith

theorem first_at_zero :
    U_T 0 (4/5) (13/20)<(WrongSignWeightPolynomial.limit:ℝ) ∧
      U_G 0 (4/5) (13/20)<(WrongSignWeightPolynomial.limit:ℝ) := by
  have hn : pairNorm (4/5) (13/20) 0+pairNorm 1 (13/20) 0≤
      (1030777/1000000 : ℝ)+1192687/1000000 := by
    linarith [first_norm_bounds.1,first_norm_bounds.2.1]
  have hm := mul_le_mul_of_nonneg_left hn R_nonneg
  have hr := mul_lt_mul_of_pos_right radius_reserves.1
    (show (0:ℝ)<1030777/1000000+1192687/1000000 by norm_num)
  have hlim : (WrongSignWeightPolynomial.limit:ℝ)=518907/1250000 := by
    norm_num [WrongSignWeightPolynomial.limit]
  have hRbar : (WrongSignWeightPolynomial.Rbar:ℝ)=494697/250000 := by
    norm_num [WrongSignWeightPolynomial.Rbar]
  rw [hRbar] at hr
  simp only [U_T,U_G,neg_zero,Real.cos_zero,mul_one,mul_zero,add_zero,hlim]
  constructor <;> linarith

theorem first_at_cap :
    U_T (7/20) (4/5) (13/20)<(WrongSignWeightPolynomial.limit:ℝ) ∧
      U_G (7/20) (4/5) (13/20)<(WrongSignWeightPolynomial.limit:ℝ) := by
  have hnT : pairNorm (4/5) (13/20) (-(7/20))+pairNorm 1 (13/20) 0≤
      (840171/1000000 : ℝ)+1192687/1000000 := by
    linarith [first_norm_bounds.2.2.1,first_norm_bounds.2.1]
  have hnG : pairNorm (4/5) (13/20) 0+pairNorm 1 (13/20) (-(7/20))≤
      (1030777/1000000 : ℝ)+494149/500000 := by
    linarith [first_norm_bounds.1,first_norm_bounds.2.2.2]
  have hmT := mul_le_mul_of_nonneg_left hnT R_nonneg
  have hmG := mul_le_mul_of_nonneg_left hnG R_nonneg
  have hrT := mul_lt_mul_of_pos_right radius_reserves.1
    (show (0:ℝ)<840171/1000000+1192687/1000000 by norm_num)
  have hrG := mul_lt_mul_of_pos_right radius_reserves.1
    (show (0:ℝ)<1030777/1000000+494149/500000 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤7/20 by norm_num)
  have hlim : (WrongSignWeightPolynomial.limit:ℝ)=518907/1250000 := by
    norm_num [WrongSignWeightPolynomial.limit]
  have hRbar : (WrongSignWeightPolynomial.Rbar:ℝ)=494697/250000 := by
    norm_num [WrongSignWeightPolynomial.Rbar]
  rw [hRbar] at hrT hrG
  simp only [U_T,U_G,charge,hlim]
  constructor <;> linarith

end SquaresInCircles.Eight.WrongSignCaptureScalars
