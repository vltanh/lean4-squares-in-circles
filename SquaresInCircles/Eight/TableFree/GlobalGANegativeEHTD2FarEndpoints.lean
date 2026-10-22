module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2SmallEndpoints

/-!
# The twenty-two actual far-EH / positive-TD2 endpoints

Uncompiled Sections 7--8 of the remaining-error companion. Every norm
uses the actual shifted surplus angle and the prescribed linear weight
family. Positive and negative B terms use their respective upper and
lower tilted coefficients. The far EH gain retains its multiplier and
constant H-support loss before the radical transfer.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Certificate
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds num4_transfer)

abbrev farActualK (r : FarCase) (θ : ℝ) := Explicit.k .far (farFamily r) θ
abbrev farActualL (r : FarCase) (θ : ℝ) := Explicit.l .far (farFamily r) θ
abbrev farActualC (r : FarCase) (θ : ℝ) := Explicit.c .far (farFamily r) θ
abbrev farActualM (r : FarCase) (e : Split) (θ : ℝ) := Explicit.splitM .far (farFamily r) e θ

def farArgument (r : FarCase) (θ : ℝ) : ℝ :=
  if r=.lowUH∨r=.lowUB then (v:ℝ)-θ else θ-(farS r:ℝ)
def farNorm (r : FarCase) (e : Split) (θ : ℝ) : Fin 4→ℝ :=
  ![pairNorm (farActualK r θ) 1
      (if r=.lowUH then farArgument r θ else if farNegativeH r then -farArgument r θ else 0),
    pairNorm (farActualK r θ) (farActualL r θ) (if farNegativeG r then -farArgument r θ else 0),
    pairNorm (farActualL r θ) (farActualM r e θ)
      (if r=.lowUB then farArgument r θ else if farNegativeB r then -farArgument r θ else 0),
    pairNorm 1 (farActualC r θ) 0]
def farActualExtra (r : FarCase) (e : Split) (θ : ℝ) : ℝ :=
  if r=.lowZero then 0
  else if r=.lowUH then farActualK r θ*(phi (farArgument r θ)-1)-(epsilon:ℝ)*farArgument r θ
  else if r=.lowUB then farActualL r θ*(phi (farArgument r θ)-1)-(epsilon:ℝ)*farArgument r θ
  else (if farNegativeG r then farActualL r θ
    else if farNegativeB r then max (farActualL r θ) (farActualM r e θ) else 1)*
      (Real.cos (farArgument r θ)-1)
def farActualA (r : FarCase) (e : Split) (θ : ℝ) : ℝ :=
  farNonradical (farFamily r) e θ+
    (if r=.lowZero then NegativeEH.G θ else NegativeEH.G (farS r:ℝ))+farActualExtra r e θ

def farIncrement (r : FarCase) (e : Split) (θ : ℝ) : ℝ :=
  if r=.lowZero then 0
  else if r=.lowUH then U R (farActualK r θ) 1 (farArgument r θ)-(epsilon:ℝ)*farArgument r θ
  else if r=.lowUB then U R (farActualL r θ) (farActualM r e θ) (farArgument r θ)-
    (epsilon:ℝ)*farArgument r θ
  else if farNegativeG r then V R (farActualK r θ) (farActualL r θ) (farArgument r θ)
  else if farNegativeB r then V R (min (farActualL r θ) (farActualM r e θ))
      (max (farActualL r θ) (farActualM r e θ)) (farArgument r θ)
  else V R (farActualK r θ) 1 (farArgument r θ)
def farValue (r : FarCase) (e : Split) (θ : ℝ) : ℝ :=
  Explicit.baseline .far (farFamily r) (Explicit.splitA e θ) (Explicit.splitT e θ)+
    (if r=.lowZero then NegativeEH.G θ else NegativeEH.G (farS r:ℝ))+farIncrement r e θ

@[simp] theorem far_delta_eval (r : FarCase) (θ : ℝ) : aeval θ (farDelta r)=farArgument r θ := by
  cases r <;> simp [farDelta,farArgument,farS]

theorem far_angle_domain (r : FarCase) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) : farArgument r θ∈Icc 0 frameCap := by
  cases r <;> norm_num [farArgument,farLeft,farRight,farS,v,u,PositiveTD.Certificate.h,frameCap] at hθ ⊢ <;>
    constructor <;> linarith [hθ.1,hθ.2]

theorem far_norm_nonnegative (r : FarCase) (e : Split) (θ : ℝ) (i : Fin 4) :
    0≤farNorm r e θ i := by
  fin_cases i <;> simp only [farNorm,Matrix.cons_val_succ,Matrix.cons_val_zero] <;>
    exact Real.sqrt_nonneg _

theorem far_norm_bounds (r : FarCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) (i : Fin 4) :
    (farNorm r e θ i)^2≤aeval θ (farP r e i) := by
  have hdom := far_domain r hθ
  have hp := split_positive .far (farFamily r) e hdom
  have hd := far_angle_domain r hθ
  have hm := far_tilted_bounds (farFamily r) e hdom
  have hH0 := zero_norm_upper hp.1 (by norm_num : (0:ℝ)<1) (le_rfl : (1:ℝ)≤1)
  have hG0 := zero_norm_upper hp.1 hp.2.1 (le_rfl : Explicit.l .far (farFamily r) θ≤_)
  have hB0 := zero_norm_upper hp.2.1 hp.2.2.2 hm.2.2
  have hD0 := zero_norm_upper (by norm_num : (0:ℝ)<1) hp.2.2.1
    (le_rfl : Explicit.c .far (farFamily r) θ≤_)
  have hHminus := negative_norm_upper hp.1 (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)≤1) le_rfl le_rfl hd
  have hGminus := negative_norm_upper hp.1 hp.2.1 hp.2.1.le le_rfl le_rfl hd
  have hBminus := negative_norm_upper hp.2.1 hp.2.2.2 hm.1.le hm.2.1 hm.2.2 hd
  have hHplus := positive_norm_upper hp.1 (by norm_num : (0:ℝ)<1) (le_rfl : (1:ℝ)≤1) hd
  have hBplus := positive_norm_upper hp.2.1 hp.2.2.2 hm.2.2 hd
  cases r <;> fin_cases i <;>
    simp only [farNorm,farP,farNegativeH,farNegativeG,farNegativeB,farFamily,
      farActualK,farActualL,farActualC,farActualM,farPH,farPG,farPB,farPD,
      if_true,if_false,reduceCtorEq,or_self,or_false,false_or,
      Matrix.cons_val_succ,Matrix.cons_val_zero,map_sub,map_add,map_mul,map_pow,map_zero,
      map_one,aeval_C,aeval_comp,far_delta_eval,farK_eval,farL_eval,farC_eval] at *
  all_goals first
    | simpa [add_comm] using hH0
    | exact hG0
    | simpa [add_comm] using hB0
    | simpa using hD0
    | simpa [add_comm] using hHminus
    | simpa using hGminus
    | simpa [add_comm] using hBminus
    | simpa [add_comm] using hHplus
    | simpa [add_comm] using hBplus

theorem far_nonradical_transfer (r : FarCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) :
    aeval θ (farNonradical r e)≤farActualA r e θ := by
  have hdom := far_domain r hθ
  have hp := split_positive .far (farFamily r) e hdom
  have hf := Explicit.family_frame_domain .far (farFamily r) hdom
  have hd := far_angle_domain r hθ
  have ht := taylor_bounds hd
  have hb := far_nonradical_lower (farFamily r) e hdom
  have hG := G_polynomial_lower hf
  have hGs := G_constant_lower (farS r)
    (by cases r <;> norm_num [farS,v,u,frameCap])
  have hcosK := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hp.1.le
  have hcosL := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hp.2.1.le
  have hphiK := mul_le_mul_of_nonneg_left
    (show aeval (farArgument r θ) C10+aeval (farArgument r θ) S11-1≤phi (farArgument r θ)-1 by
      dsimp [phi]; linarith [ht.2.1,ht.2.2.2.2.1]) hp.1.le
  have hphiL := mul_le_mul_of_nonneg_left
    (show aeval (farArgument r θ) C10+aeval (farArgument r θ) S11-1≤phi (farArgument r θ)-1 by
      dsimp [phi]; linarith [ht.2.1,ht.2.2.2.2.1]) hp.2.1.le
  have hB {r : FarCase} (hr : farNegativeB r=true)
      (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) :
      aeval θ farQStar*(aeval (farArgument r θ) C10-1)≤
        max (farActualL r θ) (farActualM r e θ)*(Real.cos (farArgument r θ)-1) := by
    have hhigh : farFamily r=.high := by cases r <;> norm_num [farNegativeB,farFamily] at hr ⊢
    have hθhigh : θ∈Icc (1/4:ℝ) (7/10) := by
      cases r <;> norm_num [farNegativeB] at hr <;> exact hθ
    have hq := far_qStar_lower e hθhigh
    have ht' := taylor_bounds (far_angle_domain r hθ)
    have hl := (split_positive .far .high e hθhigh).2.1
    have hq0 : 0≤aeval θ farQStar := (hl.le.trans (le_max_left _ _)).trans hq
    have h₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right ht'.2.2.2.2.1 1) hq0
    have h₂ := mul_le_mul_of_nonpos_right hq (sub_nonpos.mpr (Real.cos_le_one (farArgument r θ)))
    simp only [farActualL,farActualM,hhigh]
    linarith
  cases r
  all_goals
    simp only [farNonradical,farActualA,farActualExtra,farNegativeH,farNegativeG,farNegativeB,
      farFamily,farActualK,farActualL,farActualM,if_true,if_false,reduceCtorEq,or_self,
      or_false,false_or,map_add,map_sub,map_mul,map_one,aeval_C,aeval_comp,
      far_delta_eval,farK_eval,farL_eval] at hb hG hGs hcosK hcosL hphiK hphiL ⊢
  all_goals first
    | linarith [ht.2.2.2.2.1]
    | have hh := hB (r:=.highBv) (by decide) hθ; linarith
    | have hh := hB (r:=.highBu) (by decide) hθ; linarith

theorem far_scalar_identity (r : FarCase) (e : Split) (θ : ℝ) :
    farValue r e θ=farActualA r e θ-R*∑i,farNorm r e θ i := by
  rw [farValue,far_baseline_identity]
  cases r <;>
    simp only [farActualA,farActualExtra,farIncrement,farNorm,farFamily,
      farActualK,farActualL,farActualC,farActualM,farNegativeH,farNegativeG,farNegativeB,
      if_true,if_false,reduceCtorEq,or_self,or_false,false_or,
      Fin.sum_univ_succ,Matrix.cons_val_succ,Matrix.cons_val_zero,add_zero,U,V,
      TwoPositive.Certificate.sorted_pair_norm] <;> ring

theorem far_value_positive (r : FarCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) : 0<farValue r e θ := by
  have hm := far_mass_positive r e (θ:=θ)
  have hn := far_norm_nonnegative r e θ
  have hb := far_norm_bounds r e hθ
  have hp := num4_transfer (hm 0 hθ) (hm 1 hθ) (hm 2 hθ) (hm 3 hθ)
    (hn 0) (hn 1) (hn 2) (hn 3) (hb 0) (hb 1) (hb 2) (hb 3)
    (far_nonradical_transfer r e hθ) (far_numerator_positive r e hθ)
  rw [far_scalar_identity]
  simpa only [Fin.sum_univ_succ,add_zero,add_assoc] using hp

theorem far_low_positive_H (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/10)) :
    0<Explicit.baseline .far .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.G (1/10)+
      U R (Explicit.k .far .low θ) 1 (1/10-θ)-NegativeEH.epsilon*(1/10-θ) := by
  have hh := far_value_positive .lowUH e hθ
  simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,epsilon,
    NegativeEH.epsilon,v,add_assoc,sub_eq_add_neg] using hh

theorem far_low_positive_B (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/10)) :
    0<Explicit.baseline .far .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.G (1/10)+
      U R (Explicit.l .far .low θ) (Explicit.splitM .far .low e θ) (1/10-θ)-
        NegativeEH.epsilon*(1/10-θ) := by
  have hh := far_value_positive .lowUB e hθ
  simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualL,farActualM,epsilon,
    NegativeEH.epsilon,v,add_assoc,sub_eq_add_neg] using hh

theorem far_low_negative_H (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/10:ℝ) (1/4)) :
    0<Explicit.baseline .far .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.G (1/10)+
      V R (Explicit.k .far .low θ) 1 (θ-1/10) := by
  simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,farNegativeH,farNegativeG,
    farNegativeB,v,add_assoc] using far_value_positive .lowVH e hθ

theorem far_low_negative_G (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/10:ℝ) (1/4)) :
    0<Explicit.baseline .far .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.G (1/10)+
      V R (Explicit.k .far .low θ) (Explicit.l .far .low θ) (θ-1/10) := by
  simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,farActualL,farNegativeG,
    farNegativeB,v,add_assoc] using far_value_positive .lowVG e hθ

theorem far_low_equal_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/10:ℝ) (1/4)) :
    0<Explicit.baseline .far .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.G θ := by
  simpa [farValue,farIncrement,farFamily] using far_value_positive .lowZero e hθ

theorem far_high_negative_positive (atUpper : Bool) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (1/4:ℝ) (7/10)) (i : Fin 3) :
    0<Explicit.baseline .far .high (Explicit.splitA e θ) (Explicit.splitT e θ)+
      NegativeEH.G (if atUpper then (1/4:ℝ) else 1/10)+
      Explicit.V .far .high θ (Explicit.splitT e θ) i
        (θ-(if atUpper then (1/4:ℝ) else 1/10)) := by
  cases atUpper <;> fin_cases i
  · simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,farNegativeG,farNegativeB,
      Explicit.V,Explicit.p,Explicit.q,v] using far_value_positive .highHv e hθ
  · simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,farActualL,farNegativeG,farNegativeB,
      Explicit.V,Explicit.p,Explicit.q,v] using far_value_positive .highGv e hθ
  · simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualL,farActualM,farNegativeG,farNegativeB,
      Explicit.V,Explicit.p,Explicit.q,Explicit.splitM,v] using far_value_positive .highBv e hθ
  · simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,farNegativeG,farNegativeB,
      Explicit.V,Explicit.p,Explicit.q,u] using far_value_positive .highHu e hθ
  · simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,farActualL,farNegativeG,farNegativeB,
      Explicit.V,Explicit.p,Explicit.q,u] using far_value_positive .highGu e hθ
  · simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualL,farActualM,farNegativeG,farNegativeB,
      Explicit.V,Explicit.p,Explicit.q,Explicit.splitM,u] using far_value_positive .highBu e hθ

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Certificate
