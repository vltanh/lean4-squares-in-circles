module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2EndpointData
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveQuarterSplit

/-!
# Eight squares: far-low intrinsic reserves at every original A/TD split

The coefficients
are fixed at theta, and the actual split ranges over [0,theta]. Full D
support differs from the existing split model by a constant only. The
positive B alternative retains its moving m coefficient in the concave
function; the remaining four alternatives have fixed increments.
-/

section
/-!
## The twenty-two actual far-EH / positive-TD2 endpoints

Every norm
uses the actual shifted surplus angle and the prescribed linear weight
family. Positive and negative B terms use their respective upper and
lower tilted coefficients. The far EH gain retains its multiplier and
constant H-support loss before the radical transfer.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Certificate
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
  else if r=.lowUH then farActualK r θ*(PositiveAngularEnvelope.phi (farArgument r θ)-1)-(epsilon:ℝ)*farArgument r θ
  else if r=.lowUB then farActualL r θ*(PositiveAngularEnvelope.phi (farArgument r θ)-1)-(epsilon:ℝ)*farArgument r θ
  else (if farNegativeG r then farActualL r θ
    else if farNegativeB r then max (farActualL r θ) (farActualM r e θ) else 1)*
      (Real.cos (farArgument r θ)-1)
def farActualA (r : FarCase) (e : Split) (θ : ℝ) : ℝ :=
  farBaseActual (farFamily r) e θ+
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
  fin_cases i <;> simp only [farNorm] <;>
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
  fin_cases i
  · simp only [farNorm,farP,Fin.zero_eta,Fin.isValue,Matrix.cons_val_zero]
    split_ifs
    · simp only [farPH,map_add,map_mul,map_one,map_pow,aeval_C,eq_ratCast,aeval_comp,
        far_delta_eval,farK_eval]
      push_cast
      linarith [hHplus]
    · simp only [farPH,map_add,map_sub,map_mul,map_one,map_pow,aeval_C,eq_ratCast,aeval_comp,
        far_delta_eval,farK_eval]
      push_cast
      linarith [hHminus]
    · simp only [farPH,map_add,map_one,map_pow,farK_eval,sub_zero]
      linarith [hH0]
  · simp only [farNorm,farP,Fin.mk_one,Fin.isValue,Matrix.cons_val_one,Matrix.cons_val_zero]
    split_ifs
    · simp only [farPG,map_add,map_sub,map_mul,map_pow,aeval_C,eq_ratCast,aeval_comp,
        far_delta_eval,farK_eval,farL_eval]
      push_cast
      linarith [hGminus]
    · simp only [farPG,map_add,map_pow,farK_eval,farL_eval,sub_zero]
      linarith [hG0]
  · simp only [farNorm,farP,Fin.reduceFinMk,Matrix.cons_val_two,
      Matrix.tail_cons,Matrix.head_cons]
    split_ifs
    · simp only [farPB,map_add,map_mul,map_pow,aeval_C,eq_ratCast,aeval_comp,
        far_delta_eval,farL_eval]
      push_cast
      linarith [hBplus]
    · simp only [farPB,map_add,map_sub,map_mul,map_pow,aeval_C,eq_ratCast,aeval_comp,
        far_delta_eval,farL_eval]
      push_cast
      linarith [hBminus]
    · simp only [farPB,map_add,map_pow,farL_eval,sub_zero]
      linarith [hB0]
  · simp only [farNorm,farP,Fin.reduceFinMk,Matrix.cons_val_three,
      Matrix.tail_cons,Matrix.head_cons,
      farPD,map_add,map_one,map_pow,farC_eval]
    linarith [hD0]

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
    (show aeval (farArgument r θ) C10+aeval (farArgument r θ) S11-1≤
        PositiveAngularEnvelope.phi (farArgument r θ)-1 by
      dsimp only [PositiveAngularEnvelope.phi]; linarith [ht.2.1,ht.2.2.2.2.1]) hp.1.le
  have hphiL := mul_le_mul_of_nonneg_left
    (show aeval (farArgument r θ) C10+aeval (farArgument r θ) S11-1≤
        PositiveAngularEnvelope.phi (farArgument r θ)-1 by
      dsimp only [PositiveAngularEnvelope.phi]; linarith [ht.2.1,ht.2.2.2.2.1]) hp.2.1.le
  have hB {r : FarCase} (hr : farNegativeB r=true)
      (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) :
      aeval θ farQStar*(aeval (farArgument r θ) C10-1)≤
        max (farActualL r θ) (farActualM r e θ)*(Real.cos (farArgument r θ)-1) := by
    have hhigh : farFamily r=.high := by
      cases r <;> first | rfl | simp [farNegativeB] at hr
    have hθhigh : θ∈Icc (1/4:ℝ) (7/10) := by
      cases r <;> simp [farNegativeB] at hr <;>
        (norm_num [farLeft,farRight,u,PositiveTD.Certificate.h] at hθ; exact hθ)
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
    simp only [farNonradical,farActualA,farActualExtra,farNegativeG,farNegativeB,
      farFamily,farActualK,farActualL,farActualM,↓reduceIte,reduceCtorEq,or_self,
      or_false,false_or,decide_true,decide_false,Bool.false_eq_true,
      map_add,map_sub,map_mul,map_one,aeval_C,eq_ratCast,aeval_comp,
      far_delta_eval,farK_eval,farL_eval] at hb hG hGs hcosK hcosL hphiK hphiL ⊢
  all_goals first
    | linarith [ht.2.2.2.2.1]
    | have hh := hB (r:=.highBv) (by decide) hθ
      simp only [farActualL,farActualM,farFamily] at hh
      linarith
    | have hh := hB (r:=.highBu) (by decide) hθ
      simp only [farActualL,farActualM,farFamily] at hh
      linarith

theorem far_scalar_identity (r : FarCase) (e : Split) (θ : ℝ) :
    farValue r e θ=farActualA r e θ-R*∑i,farNorm r e θ i := by
  rw [farValue,far_baseline_identity]
  cases r <;>
    simp only [farActualA,farActualExtra,farIncrement,farNorm,farFamily,
      farActualK,farActualL,farActualC,farActualM,farNegativeH,farNegativeG,farNegativeB,
      ↓reduceIte,reduceCtorEq,or_self,or_false,false_or,decide_true,decide_false,
      Bool.false_eq_true,Fin.sum_univ_succ,Matrix.cons_val_succ,Matrix.cons_val_zero,add_zero,U,V,
      TwoPositive.Certificate.sorted_pair_norm] <;> ring

theorem far_value_positive (r : FarCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) : 0<farValue r e θ := by
  have hm := far_mass_positive r e (θ:=θ)
  have hn := far_norm_nonnegative r e θ
  have hb := far_norm_bounds r e hθ
  have hp := num4_transfer (hm 0 hθ) (hm 1 hθ) (hm 2 hθ) (hm 3 hθ)
    (hn 0) (hn 1) (hn 2) (hn 3) (hb 0) (hb 1) (hb 2) (hb 3)
    (far_nonradical_transfer r e hθ) (far_numerator_positive r e hθ)
  rw [far_scalar_identity,Fin.sum_univ_four]
  simpa only [add_assoc] using hp

private theorem r77_far_dom {r : FarCase} {a b θ : ℝ}
    (hab : (farLeft r:ℝ)=a ∧ (farRight r:ℝ)=b) (hθ : θ∈Icc a b) :
    θ∈Icc (farLeft r:ℝ) (farRight r:ℝ) := by
  rw [hab.1,hab.2]
  exact hθ

theorem far_low_positive_H (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/10)) :
    0<Explicit.baseline .far .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.G (1/10)+
      U R (Explicit.k .far .low θ) 1 (1/10-θ)-NegativeEH.epsilon*(1/10-θ) := by
  have hh := far_value_positive .lowUH e
    (r77_far_dom (by norm_num [farLeft,farRight,v,u,PositiveTD.Certificate.h]) hθ)
  simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,epsilon,
    NegativeEH.epsilon,v,add_assoc,sub_eq_add_neg] using hh

theorem far_low_positive_B (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/10)) :
    0<Explicit.baseline .far .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.G (1/10)+
      U R (Explicit.l .far .low θ) (Explicit.splitM .far .low e θ) (1/10-θ)-
        NegativeEH.epsilon*(1/10-θ) := by
  have hh := far_value_positive .lowUB e
    (r77_far_dom (by norm_num [farLeft,farRight,v,u,PositiveTD.Certificate.h]) hθ)
  simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualL,farActualM,epsilon,
    NegativeEH.epsilon,v,add_assoc,sub_eq_add_neg] using hh

theorem far_low_negative_H (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/10:ℝ) (1/4)) :
    0<Explicit.baseline .far .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.G (1/10)+
      V R (Explicit.k .far .low θ) 1 (θ-1/10) := by
  simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,farNegativeH,farNegativeG,
    farNegativeB,v,add_assoc] using
      far_value_positive .lowVH e
        (r77_far_dom (by norm_num [farLeft,farRight,v,u,PositiveTD.Certificate.h]) hθ)

theorem far_low_negative_G (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/10:ℝ) (1/4)) :
    0<Explicit.baseline .far .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.G (1/10)+
      V R (Explicit.k .far .low θ) (Explicit.l .far .low θ) (θ-1/10) := by
  simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,farActualL,farNegativeG,
    farNegativeB,v,add_assoc] using
      far_value_positive .lowVG e
        (r77_far_dom (by norm_num [farLeft,farRight,v,u,PositiveTD.Certificate.h]) hθ)

theorem far_low_equal_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/10:ℝ) (1/4)) :
    0<Explicit.baseline .far .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.G θ := by
  simpa [farValue,farIncrement,farFamily] using
      far_value_positive .lowZero e
        (r77_far_dom (by norm_num [farLeft,farRight,v,u,PositiveTD.Certificate.h]) hθ)

theorem far_high_negative_positive (atUpper : Bool) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (1/4:ℝ) (7/10)) (i : Fin 3) :
    0<Explicit.baseline .far .high (Explicit.splitA e θ) (Explicit.splitT e θ)+
      NegativeEH.G (if atUpper then (1/4:ℝ) else 1/10)+
      Explicit.V .far .high θ (Explicit.splitT e θ) i
        (θ-(if atUpper then (1/4:ℝ) else 1/10)) := by
  cases atUpper <;> fin_cases i
  · simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,farNegativeG,farNegativeB,
      Explicit.V,Explicit.p,Explicit.q,v] using
      far_value_positive .highHv e
        (r77_far_dom (by norm_num [farLeft,farRight,v,u,PositiveTD.Certificate.h]) hθ)
  · simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,farActualL,farNegativeG,farNegativeB,
      Explicit.V,Explicit.p,Explicit.q,v] using
      far_value_positive .highGv e
        (r77_far_dom (by norm_num [farLeft,farRight,v,u,PositiveTD.Certificate.h]) hθ)
  · simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualL,farActualM,farNegativeG,farNegativeB,
      Explicit.V,Explicit.p,Explicit.q,Explicit.splitM,v] using
      far_value_positive .highBv e
        (r77_far_dom (by norm_num [farLeft,farRight,v,u,PositiveTD.Certificate.h]) hθ)
  · simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,farNegativeG,farNegativeB,
      Explicit.V,Explicit.p,Explicit.q,u] using
      far_value_positive .highHu e
        (r77_far_dom (by norm_num [farLeft,farRight,v,u,PositiveTD.Certificate.h]) hθ)
  · simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualK,farActualL,farNegativeG,farNegativeB,
      Explicit.V,Explicit.p,Explicit.q,u] using
      far_value_positive .highGu e
        (r77_far_dom (by norm_num [farLeft,farRight,v,u,PositiveTD.Certificate.h]) hθ)
  · simpa [farValue,farIncrement,farFamily,farS,farArgument,farActualL,farActualM,farNegativeG,farNegativeB,
      Explicit.V,Explicit.p,Explicit.q,Explicit.splitM,u] using
      far_value_positive .highBu e
        (r77_far_dom (by norm_num [farLeft,farRight,v,u,PositiveTD.Certificate.h]) hθ)

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Certificate
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.FarLowSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def base (θ a : ℝ) : ℝ := Explicit.baseline .far .low a (θ-a)
def correction (θ : ℝ) : ℝ :=
  clippedSupport 1 (Explicit.c .far .low θ)-fullSupport 1 (Explicit.c .far .low θ)

theorem base_identity (θ a : ℝ) :
    base θ a=TwoPositive.splitBase (Explicit.k .far .low θ) (Explicit.l .far .low θ)
      (Explicit.c .far .low θ) θ a+correction θ := by
  simp only [base,Explicit.baseline,show a+(θ-a)=θ by ring,
    Explicit.sortedD,Bool.false_eq_true,ite_false,TwoPositive.splitBase,PositiveTD.baseline,correction]
  dsimp [Explicit.m,Explicit.eta,Explicit.sigma,NegativeDEPositiveTD.Explicit.eta,
    NegativeDEPositiveTD.Explicit.sigma,PositiveTD.tilted,PositiveTD.eta,PositiveTD.sigma]
  ring

theorem coefficients {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) :
    0<Explicit.c .far .low θ ∧ 0<Explicit.l .far .low θ ∧
    Explicit.c .far .low θ≤(3/2)*Explicit.l .far .low θ ∧
    (∀a∈Icc 0 θ,PositiveTD.tilted (Explicit.c .far .low θ) (θ-a)≤
      (3/2)*Explicit.l .far .low θ) := by
  have hr := Explicit.far_low_ranges hθ
  refine ⟨by linarith [hr.2.2.1.1],by linarith [hr.2.1.1],
    by linarith [hr.2.2.1.2,hr.2.1.1],?_⟩
  intro a ha
  have hm := Explicit.far_low_tilted hθ
    (show θ-a∈Icc 0 θ from ⟨by linarith [ha.2],by linarith [ha.1]⟩)
  change Explicit.m .far .low θ (θ-a)≤(3/2)*Explicit.l .far .low θ
  linarith [hm.2.2.2,hr.2.1.1]

theorem base_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) :
    ConcaveOn ℝ (Icc 0 θ) (base θ) := by
  obtain ⟨hc,hl,hcl,hm⟩ := coefficients hθ
  have hh := TwoPositive.QuarterSplit.increment_concave
    (k:=Explicit.k .far .low θ) (s:=0) (g:=0) (e:=0)
    hc hl hcl hθ (by norm_num [frameCap]) (by norm_num) (by norm_num)
    (by linarith [Real.cos_le_one frameCap]) (by simp) hm
  have hb : ConcaveOn ℝ (Icc 0 θ)
      (TwoPositive.splitBase (Explicit.k .far .low θ) (Explicit.l .far .low θ)
        (Explicit.c .far .low θ) θ) := by
    simpa only [TwoPositive.Split.increment_zero,add_zero] using hh
  apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant hb (correction θ))
  intro a _
  exact (base_identity θ a).symm

theorem B_positive_concave {θ d : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hd : d∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 θ) (fun a => base θ a+
      U R (Explicit.l .far .low θ) (Explicit.m .far .low θ (θ-a)) d) := by
  obtain ⟨hc,hl,hcl,hm⟩ := coefficients hθ
  have hh := TwoPositive.QuarterSplit.increment_concave
    (k:=Explicit.k .far .low θ) (s:=d) (g:=PositiveAngularEnvelope.phi d-1) (e:=0)
    hc hl hcl hθ (by rw [abs_of_nonneg hd.1]; exact hd.2)
    (sub_nonneg.mpr (TwoPositive.Split.phi_ge_one hd)) le_rfl
    (by linarith [Real.cos_le_one frameCap]) (by simp) hm
  apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant hh (correction θ))
  intro a ha
  have horder := (Explicit.far_low_tilted hθ
    (show θ-a∈Icc 0 θ from ⟨by linarith [ha.2],by linarith [ha.1]⟩)).2.2.1.le
  rw [TwoPositive.Split.increment_U,base_identity]
  change TwoPositive.splitBase _ _ _ θ a+
      U R (min (Explicit.l .far .low θ) (Explicit.m .far .low θ (θ-a)))
        (max (Explicit.l .far .low θ) (Explicit.m .far .low θ (θ-a))) d+correction θ=_
  rw [min_eq_left horder,max_eq_right horder]
  ring

theorem equal_positive {a z : ℝ} (hθ : a+z∈Icc (1/10:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (a+z) := by
  let θ := a+z
  have ht : θ∈Icc (0:ℝ) (1/4) := ⟨by linarith [hθ.1],hθ.2⟩
  have hc := TwoPositive.Split.add_constant (base_concave ht) (NegativeEH.G θ)
  have h0 := Certificate.far_low_equal_positive .atT hθ
  have h1 := Certificate.far_low_equal_positive .atA hθ
  have hh := concave_gt_of_endpoints (c:=0) hc
    (show a∈Icc 0 θ from ⟨ha,by dsimp [θ]; linarith⟩)
    (by simpa [base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,θ] using h0)
    (by simpa [base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,θ] using h1)
  simpa only [base,θ,show a+z-a=z by ring] using hh

theorem positive_H {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/10))
    (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (1/10)+
      U R (Explicit.k .far .low (a+z)) 1 (1/10-(a+z))-
        NegativeEH.epsilon*(1/10-(a+z)) := by
  let θ := a+z
  have ht : θ∈Icc (0:ℝ) (1/4) := ⟨hθ.1,by linarith [hθ.2]⟩
  have hc := TwoPositive.Split.add_constant (base_concave ht)
    (NegativeEH.G (1/10)+U R (Explicit.k .far .low θ) 1 (1/10-θ)-NegativeEH.epsilon*(1/10-θ))
  have hh := concave_gt_of_endpoints (c:=0) hc
    (show a∈Icc 0 θ from ⟨ha,by dsimp [θ]; linarith⟩)
    (by simpa [base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,θ,add_assoc,sub_eq_add_neg]
      using Certificate.far_low_positive_H .atT hθ)
    (by simpa [base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,θ,add_assoc,sub_eq_add_neg]
      using Certificate.far_low_positive_H .atA hθ)
  simpa [base,θ,show a+z-a=z by ring,add_assoc,sub_eq_add_neg] using hh

theorem positive_B {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/10))
    (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (1/10)+
      U R (Explicit.l .far .low (a+z)) (Explicit.m .far .low (a+z) z) (1/10-(a+z))-
        NegativeEH.epsilon*(1/10-(a+z)) := by
  let θ := a+z
  have ht : θ∈Icc (0:ℝ) (1/4) := ⟨hθ.1,by linarith [hθ.2]⟩
  have hd : 1/10-θ∈Icc 0 frameCap :=
    ⟨by linarith [hθ.2],by norm_num [frameCap]; linarith [hθ.1]⟩
  have hc := TwoPositive.Split.add_constant (B_positive_concave ht hd)
    (NegativeEH.G (1/10)-NegativeEH.epsilon*(1/10-θ))
  have hh := concave_gt_of_endpoints (c:=0) hc
    (show a∈Icc 0 θ from ⟨ha,by dsimp [θ]; linarith⟩)
    (by simpa [base,Explicit.splitM,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,θ,
        add_assoc,add_comm,add_left_comm,sub_eq_add_neg]
      using Certificate.far_low_positive_B .atT hθ)
    (by simpa [base,Explicit.splitM,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,θ,
        add_assoc,add_comm,add_left_comm,sub_eq_add_neg]
      using Certificate.far_low_positive_B .atA hθ)
  simpa [base,θ,show a+z-a=z by ring,add_assoc,add_comm,add_left_comm,sub_eq_add_neg] using hh

theorem negative_H {a z : ℝ} (hθ : a+z∈Icc (1/10:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (1/10)+
      V R (Explicit.k .far .low (a+z)) 1 (a+z-1/10) := by
  let θ := a+z
  have ht : θ∈Icc (0:ℝ) (1/4) := ⟨by linarith [hθ.1],hθ.2⟩
  have hc := TwoPositive.Split.add_constant (base_concave ht)
    (NegativeEH.G (1/10)+V R (Explicit.k .far .low θ) 1 (θ-1/10))
  have hh := concave_gt_of_endpoints (c:=0) hc
    (show a∈Icc 0 θ from ⟨ha,by dsimp [θ]; linarith⟩)
    (by simpa [base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,θ,add_assoc]
      using Certificate.far_low_negative_H .atT hθ)
    (by simpa [base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,θ,add_assoc]
      using Certificate.far_low_negative_H .atA hθ)
  simpa [base,θ,show a+z-a=z by ring,add_assoc] using hh

theorem negative_G {a z : ℝ} (hθ : a+z∈Icc (1/10:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (1/10)+
      V R (Explicit.k .far .low (a+z)) (Explicit.l .far .low (a+z)) (a+z-1/10) := by
  let θ := a+z
  have ht : θ∈Icc (0:ℝ) (1/4) := ⟨by linarith [hθ.1],hθ.2⟩
  have hc := TwoPositive.Split.add_constant (base_concave ht)
    (NegativeEH.G (1/10)+V R (Explicit.k .far .low θ) (Explicit.l .far .low θ) (θ-1/10))
  have hh := concave_gt_of_endpoints (c:=0) hc
    (show a∈Icc 0 θ from ⟨ha,by dsimp [θ]; linarith⟩)
    (by simpa [base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,θ,add_assoc]
      using Certificate.far_low_negative_G .atT hθ)
    (by simpa [base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,θ,add_assoc]
      using Certificate.far_low_negative_G .atA hθ)
  simpa [base,θ,show a+z-a=z by ring,add_assoc] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.FarLowSplit
end
end
end
