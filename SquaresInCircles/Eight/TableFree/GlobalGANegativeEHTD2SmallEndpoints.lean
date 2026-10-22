module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2EndpointData

/-!
# The ten actual small-EH / positive-TD2 endpoint inequalities

Uncompiled Section 5 of the small-error companion. Each original norm
is bounded at the shifted angle theta-v, not at theta. The low family
retains the diagonal D support, while the high family retains all four
circle norms. Positivity is transferred only after every mass and every
Taylor direction has been proved on the whole native interval.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Certificate
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds num3_transfer num4_transfer)

abbrev smallK (r : SmallCase) (θ : ℝ) := Explicit.k .small (smallFamily r) θ
abbrev smallL (r : SmallCase) (θ : ℝ) := Explicit.l .small (smallFamily r) θ
abbrev smallC (r : SmallCase) (θ : ℝ) := Explicit.c .small (smallFamily r) θ
abbrev smallM (r : SmallCase) (e : Split) (θ : ℝ) := Explicit.splitM .small (smallFamily r) e θ

def smallAngle (r : SmallCase) (θ : ℝ) : ℝ := if r=.lowZero then 0 else θ-(v:ℝ)
def smallActualBase (r : SmallCase) (e : Split) (θ : ℝ) : ℝ :=
  if smallFamily r=.low then NegativeDEPositiveTD.Certificate.lowNonradical e θ
  else NegativeDEPositiveTD.Certificate.highNonradical e θ
def smallActualA (r : SmallCase) (e : Split) (θ : ℝ) : ℝ :=
  smallActualBase r e θ+
    (if r=.lowZero then NegativeEH.g θ else NegativeEH.g (v:ℝ))+
    if r=.lowZero then 0 else
      (if r=.highG then smallL r θ else if r=.highB then max (smallL r θ) (smallM r e θ) else 1)*
        (Real.cos (smallAngle r θ)-1)
def smallNorm (r : SmallCase) (e : Split) (θ : ℝ) : Fin 4→ℝ :=
  ![pairNorm (smallK r θ) 1 (if r=.lowH∨r=.highH then -smallAngle r θ else 0),
    pairNorm (smallK r θ) (smallL r θ) (if r=.highG then -smallAngle r θ else 0),
    pairNorm (smallL r θ) (smallM r e θ) (if r=.highB then -smallAngle r θ else 0),
    if smallFamily r=.low then 0 else pairNorm 1 (smallC r θ) 0]
def smallValue (r : SmallCase) (e : Split) (θ : ℝ) : ℝ :=
  Explicit.baseline .small (smallFamily r) (Explicit.splitA e θ) (Explicit.splitT e θ)+
    if r=.lowZero then NegativeEH.g θ else NegativeEH.g (v:ℝ)+
      if r=.highG then V R (smallK r θ) (smallL r θ) (smallAngle r θ)
      else if r=.highB then V R (min (smallL r θ) (smallM r e θ))
        (max (smallL r θ) (smallM r e θ)) (smallAngle r θ)
      else V R (smallK r θ) 1 (smallAngle r θ)

theorem small_angle_domain (r : SmallCase) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) : smallAngle r θ∈Icc 0 frameCap := by
  cases r <;> norm_num [smallAngle,smallLeft,smallRight,v,PositiveTD.Certificate.L,
    PositiveTD.Certificate.h,frameCap] at hθ ⊢ <;> constructor <;> linarith [hθ.1,hθ.2]

theorem small_norm_nonnegative (r : SmallCase) (e : Split) (θ : ℝ) (i : Fin 4) :
    0≤smallNorm r e θ i := by
  cases r <;> fin_cases i <;> simp only [smallNorm,smallFamily,if_true,if_false,
    reduceCtorEq,or_self,or_false,false_or,Matrix.cons_val_succ,Matrix.cons_val_zero]
  all_goals first | exact le_rfl | exact Real.sqrt_nonneg _

theorem small_norm_bounds (r : SmallCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) (i : Fin 4) :
    (smallNorm r e θ i)^2≤aeval θ (smallP r e i) := by
  have hdom := small_domain r hθ
  have hp := split_positive .small (smallFamily r) e hdom
  have hd := small_angle_domain r hθ
  have hm := NegativeDEPositiveTD.Certificate.tilted_bounds (smallFamily r) e hdom
  have hz := NegativeDEPositiveTD.Certificate.ordinary_norm_bounds (smallFamily r) e hdom
  have hH := negative_norm_upper hp.1 (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)≤1) le_rfl le_rfl hd
  have hG := negative_norm_upper hp.1 hp.2.1 hp.2.1.le le_rfl le_rfl hd
  have hB := negative_norm_upper hp.2.1 hp.2.2.2 hm.1.le hm.2.1 hm.2.2 hd
  have hH0 := hz.1
  have hG0 := hz.2.1
  have hB0 := hz.2.2.1
  have hD0 := hz.2.2.2.1
  cases r <;> fin_cases i <;>
    simp only [smallNorm,smallP,smallFamily,smallK,smallL,smallC,smallM,smallAngle,
      smallDelta,if_true,if_false,reduceCtorEq,or_self,or_false,false_or,
      Matrix.cons_val_succ,Matrix.cons_val_zero,map_sub,map_mul,map_add,map_pow,
      map_zero,aeval_C,aeval_X,aeval_comp,NegativeDEPositiveTD.Certificate.k_eval,
      NegativeDEPositiveTD.Certificate.l_eval] at *
  all_goals first
    | norm_num
    | exact hH0
    | exact hG0
    | exact hB0
    | exact hD0
    | simpa [NegativeDEPositiveTD.Certificate.PH,add_comm] using hH
    | simpa [NegativeDEPositiveTD.Certificate.PG] using hG
    | simpa [NegativeDEPositiveTD.Certificate.PB,add_comm] using hB

theorem small_nonradical_lower (r : SmallCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) :
    aeval θ (smallNonradical r e)≤smallActualA r e θ := by
  have hdom := small_domain r hθ
  have hf := Explicit.family_frame_domain .small (smallFamily r) hdom
  have hd := small_angle_domain r hθ
  have hp := split_positive .small (smallFamily r) e hdom
  have ht := taylor_bounds hd
  have hg := g_polynomial_lower hf
  have hgv := g_constant_lower v (by norm_num [v,frameCap])
  have hb : aeval θ (if smallFamily r=.low then NegativeDEPositiveTD.Certificate.lowB e
      else NegativeDEPositiveTD.Certificate.highB e)≤smallActualBase r e θ := by
    cases r
    · exact NegativeDEPositiveTD.Certificate.low_nonradical_lower e hdom
    · exact NegativeDEPositiveTD.Certificate.low_nonradical_lower e hdom
    · exact NegativeDEPositiveTD.Certificate.high_nonradical_lower e hdom
    · exact NegativeDEPositiveTD.Certificate.high_nonradical_lower e hdom
    · exact NegativeDEPositiveTD.Certificate.high_nonradical_lower e hdom
  cases r
  · simpa only [smallNonradical,smallActualA,smallFamily,if_true,map_add,add_zero] using add_le_add hb hg
  · simp only [smallNonradical,smallActualA,smallFamily,smallAngle,smallDelta,
      if_true,if_false,reduceCtorEq,map_add,map_sub,map_one,map_mul,aeval_comp,aeval_C,aeval_X,one_mul] at hb ht ⊢
    linarith [ht.2.2.2.2.1]
  · simp only [smallNonradical,smallActualA,smallFamily,smallAngle,smallDelta,
      if_true,if_false,reduceCtorEq,map_add,map_sub,map_one,map_mul,aeval_comp,aeval_C,aeval_X,one_mul] at hb ht ⊢
    linarith [ht.2.2.2.2.1]
  · have hcos := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hp.2.1.le
    simp only [smallNonradical,smallActualA,smallFamily,smallAngle,smallDelta,smallL,
      if_true,if_false,reduceCtorEq,map_add,map_sub,map_one,map_mul,aeval_comp,aeval_C,aeval_X,
      NegativeDEPositiveTD.Certificate.l_eval] at hb hcos ⊢
    linarith
  · have hq := NegativeDEPositiveTD.Certificate.qStar_lower e hdom
    have hqpos : 0≤aeval θ NegativeDEPositiveTD.Certificate.qStar :=
      (hp.2.1.le.trans (le_max_left _ _)).trans hq
    have h₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hqpos
    have h₂ := mul_le_mul_of_nonpos_right hq (sub_nonpos.mpr (Real.cos_le_one (smallAngle .highB θ)))
    simp only [smallNonradical,smallActualA,smallFamily,smallAngle,smallDelta,smallL,smallM,
      if_true,if_false,reduceCtorEq,map_add,map_sub,map_one,map_mul,aeval_comp,aeval_C,aeval_X] at hb h₁ h₂ ⊢
    linarith

theorem small_baseline_low (e : Split) (θ : ℝ) :
    Explicit.baseline .small .low (Explicit.splitA e θ) (Explicit.splitT e θ)=
      NegativeDEPositiveTD.Certificate.lowBase e θ 0 := by
  simp only [Explicit.baseline,Explicit.sortedD,if_true,Explicit.k,Explicit.l,Explicit.c,
    Explicit.m,Explicit.sigma,Explicit.eta,Explicit.splitM,
    NegativeDEPositiveTD.Certificate.lowBase,NegativeDEPositiveTD.Explicit.baseline,
    NegativeDEPositiveTD.Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,sub_self,
    mul_zero,add_zero,sub_zero]
  ring

theorem small_baseline_high (e : Split) (θ : ℝ) :
    Explicit.baseline .small .high (Explicit.splitA e θ) (Explicit.splitT e θ)=
      NegativeDEPositiveTD.Certificate.highBase e θ 0 := by
  simp only [Explicit.baseline,Explicit.sortedD,Bool.false_eq_true,if_false,Explicit.k,Explicit.l,
    Explicit.c,Explicit.m,Explicit.sigma,Explicit.eta,
    NegativeDEPositiveTD.Certificate.highBase,NegativeDEPositiveTD.Explicit.fullBaseline,
    NegativeDEPositiveTD.Explicit.baseline,NegativeDEPositiveTD.Explicit.secant,
    Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,add_zero,sub_zero]
  ring

theorem small_scalar_identity (r : SmallCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) :
    smallValue r e θ=smallActualA r e θ-R*∑i,smallNorm r e θ i := by
  have hdom := small_domain r hθ
  cases r
  · rw [smallValue,if_pos rfl,small_baseline_low,
      NegativeDEPositiveTD.Certificate.low_baseline_identity e hdom ⟨le_rfl,hdom.1⟩]
    simp [smallActualA,smallActualBase,smallNorm,smallK,smallL,smallM,smallFamily,
      Fin.sum_univ_succ,NegativeDEPositiveTD.Explicit.secant]
    ring
  · have hid := NegativeDEPositiveTD.Certificate.low_H_identity e hdom (θ-(v:ℝ))
    simp only [smallValue,smallActualA,smallActualBase,smallNorm,smallFamily,smallAngle,
      smallK,smallL,smallM,small_baseline_low,if_true,if_false,reduceCtorEq,or_false,
      Fin.sum_univ_succ,Matrix.cons_val_succ,Matrix.cons_val_zero,add_zero,one_mul]
    linarith only [hid]
  · rw [smallValue,small_baseline_high,NegativeDEPositiveTD.Certificate.high_baseline_identity]
    simp [smallActualA,smallActualBase,smallNorm,smallK,smallL,smallC,smallM,smallFamily,
      smallAngle,Fin.sum_univ_succ,NegativeDEPositiveTD.Explicit.secant,V]
    ring
  · rw [smallValue,small_baseline_high,NegativeDEPositiveTD.Certificate.high_baseline_identity]
    simp [smallActualA,smallActualBase,smallNorm,smallK,smallL,smallC,smallM,smallFamily,
      smallAngle,Fin.sum_univ_succ,NegativeDEPositiveTD.Explicit.secant,V]
    ring
  · rw [smallValue,small_baseline_high,NegativeDEPositiveTD.Certificate.high_baseline_identity]
    simp [smallActualA,smallActualBase,smallNorm,smallK,smallL,smallC,smallM,smallFamily,
      smallAngle,Fin.sum_univ_succ,NegativeDEPositiveTD.Explicit.secant,V,
      TwoPositive.Certificate.sorted_pair_norm]
    ring

theorem small_value_positive (r : SmallCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) : 0<smallValue r e θ := by
  have hmass := small_mass_positive r e (θ:=θ)
  have hnorm := small_norm_nonnegative r e θ
  have hbound := small_norm_bounds r e hθ
  have hA := small_nonradical_lower r e hθ
  have hnum := small_numerator_positive r e hθ
  rw [small_scalar_identity r e hθ]
  cases hf : smallFamily r
  · have hp := num3_transfer (hmass 0 hθ) (hmass 1 hθ) (hmass 2 hθ)
      (hnorm 0) (hnorm 1) (hnorm 2) (hbound 0) (hbound 1) (hbound 2) hA
      (by simpa only [smallNumerator,hf,if_true] using hnum)
    have hD : smallNorm r e θ 3=0 := by simp [smallNorm,hf]
    simpa only [Fin.sum_univ_succ,hD,add_zero] using hp
  · have hp := num4_transfer (hmass 0 hθ) (hmass 1 hθ) (hmass 2 hθ) (hmass 3 hθ)
      (hnorm 0) (hnorm 1) (hnorm 2) (hnorm 3)
      (hbound 0) (hbound 1) (hbound 2) (hbound 3) hA
      (by simpa only [smallNumerator,hf,reduceCtorEq,if_false] using hnum)
    simpa only [Fin.sum_univ_succ,add_zero,add_assoc] using hp

/-- The low equal-angle EH endpoint, with its actual nonsecant gain. -/
theorem small_low_equal_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/10)) :
    0<Explicit.baseline .small .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.g θ := by
  simpa [smallValue,smallFamily] using small_value_positive .lowZero e hθ

theorem small_low_negative_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/10:ℝ) (1/6)) :
    0<Explicit.baseline .small .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.g (1/10)+
      V R (Explicit.k .small .low θ) 1 (θ-1/10) := by
  simpa [smallValue,smallFamily,smallAngle,v,add_assoc] using small_value_positive .lowH e hθ

theorem small_high_negative_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (i : Fin 3) :
    0<Explicit.baseline .small .high (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.g (1/10)+
      Explicit.V .small .high θ (Explicit.splitT e θ) i (θ-1/10) := by
  fin_cases i
  · simpa [smallValue,smallFamily,smallAngle,smallK,Explicit.V,Explicit.p,Explicit.q,v,add_assoc]
      using small_value_positive .highH e hθ
  · simpa [smallValue,smallFamily,smallAngle,smallK,smallL,Explicit.V,Explicit.p,Explicit.q,v,add_assoc]
      using small_value_positive .highG e hθ
  · simpa [smallValue,smallFamily,smallAngle,smallL,smallM,Explicit.V,Explicit.p,Explicit.q,
      Explicit.splitM,v,add_assoc] using small_value_positive .highB e hθ

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Certificate
