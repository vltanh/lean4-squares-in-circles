module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2EndpointData

/-!
# Eight squares: the ten actual small-EH / positive-TD2 endpoint inequalities

Each original norm
is bounded at the shifted angle theta-v, not at theta. The low family
retains the diagonal D support, while the high family retains all four
circle norms. Positivity is transferred only after every mass and every
Taylor direction has been proved on the whole native interval.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Certificate
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
    0≤ smallNorm r e θ i := by
  cases r <;> fin_cases i <;> simp only [smallNorm,smallFamily,ite_true,ite_false,
    reduceCtorEq,or_self,or_false,false_or]
  all_goals first | exact le_rfl | exact Real.sqrt_nonneg _

private theorem r78_cert_domain (r : SmallCase) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) :
    θ∈Icc (NegativeDEPositiveTD.Certificate.left (smallFamily r):ℝ)
      (NegativeDEPositiveTD.Certificate.right (smallFamily r):ℝ) := by
  cases r <;> norm_num [smallLeft,smallRight,smallFamily,v,NegativeDEPositiveTD.Certificate.left,
    NegativeDEPositiveTD.Certificate.right,PositiveTD.Certificate.L,PositiveTD.Certificate.h] at hθ ⊢ <;>
    constructor <;> linarith [hθ.1,hθ.2]

theorem small_norm_bounds (r : SmallCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) (i : Fin 4) :
    (smallNorm r e θ i)^2≤aeval θ (smallP r e i) := by
  have hdom := small_domain r hθ
  have hc := r78_cert_domain r hθ
  have hp := split_positive .small (smallFamily r) e hdom
  have hd := small_angle_domain r hθ
  have hm := NegativeDEPositiveTD.Certificate.tilted_bounds (smallFamily r) e hc
  have hz := NegativeDEPositiveTD.Certificate.ordinary_norm_bounds (smallFamily r) e hc
  have hH := negative_norm_upper (p:=NegativeDEPositiveTD.Explicit.k (smallFamily r) θ) hp.1 (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)≤1) le_rfl le_rfl hd
  have hG := negative_norm_upper (p:=NegativeDEPositiveTD.Explicit.k (smallFamily r) θ) (q:=NegativeDEPositiveTD.Explicit.l (smallFamily r) θ)
    hp.1 hp.2.1 hp.2.1.le le_rfl le_rfl hd
  have hB := negative_norm_upper (p:=NegativeDEPositiveTD.Explicit.l (smallFamily r) θ) (q:=NegativeDEPositiveTD.Explicit.splitM (smallFamily r) e θ)
    hp.2.1 hp.2.2.2 hm.1.le hm.2.1 hm.2.2 hd
  have hcomp (q : ℚ[X]) : aeval θ (q.comp smallDelta)=aeval (θ-(v:ℝ)) q := by
    rw [aeval_comp]; simp [smallDelta]
  have hPH (f : Family) : aeval θ (NegativeDEPositiveTD.Certificate.PH f)=1+(NegativeDEPositiveTD.Explicit.k f θ)^2 := by simp [NegativeDEPositiveTD.Certificate.PH]
  have hPG (f : Family) : aeval θ (NegativeDEPositiveTD.Certificate.PG f)=(NegativeDEPositiveTD.Explicit.k f θ)^2+(NegativeDEPositiveTD.Explicit.l f θ)^2 := by
    simp [NegativeDEPositiveTD.Certificate.PG]
  have hPB (f : Family) : aeval θ (NegativeDEPositiveTD.Certificate.PB f e)=(aeval θ (NegativeDEPositiveTD.Certificate.mHi f e))^2+(NegativeDEPositiveTD.Explicit.l f θ)^2 := by
    simp [NegativeDEPositiveTD.Certificate.PB]
  have hsub (a : ℚ[X]) : aeval θ (a-0)=aeval θ a := by rw [sub_zero]
  cases r <;> fin_cases i
  -- lowZero
  · change (pairNorm (NegativeDEPositiveTD.Explicit.k .low θ) 1 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PH .low-0)
    rw [hsub]; exact hz.1
  · change (pairNorm (NegativeDEPositiveTD.Explicit.k .low θ) (NegativeDEPositiveTD.Explicit.l .low θ) 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PG .low-0)
    rw [hsub]; exact hz.2.1
  · change (pairNorm (NegativeDEPositiveTD.Explicit.l .low θ) (NegativeDEPositiveTD.Explicit.splitM .low e θ) 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PB .low e-0)
    rw [hsub]; exact hz.2.2.1
  · change (0:ℝ)^2≤aeval θ (0:ℚ[X])
    simp
  -- lowH
  · change (pairNorm (NegativeDEPositiveTD.Explicit.k .low θ) 1 (-(θ-(v:ℝ))))^2≤
      aeval θ (NegativeDEPositiveTD.Certificate.PH .low-C 2*NegativeDEPositiveTD.Certificate.k .low*S11.comp smallDelta)
    rw [map_sub,map_mul,map_mul,hcomp,hPH]
    simp only [aeval_C,NegativeDEPositiveTD.Certificate.k_eval,eq_ratCast,Rat.cast_ofNat]
    change (pairNorm (NegativeDEPositiveTD.Explicit.k .low θ) 1 (-(θ-(v:ℝ))))^2≤(NegativeDEPositiveTD.Explicit.k .low θ)^2+1^2-
      2*NegativeDEPositiveTD.Explicit.k .low θ*1*aeval (θ-(v:ℝ)) S11 at hH
    linarith [hH]
  · change (pairNorm (NegativeDEPositiveTD.Explicit.k .low θ) (NegativeDEPositiveTD.Explicit.l .low θ) 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PG .low-0)
    rw [hsub]; exact hz.2.1
  · change (pairNorm (NegativeDEPositiveTD.Explicit.l .low θ) (NegativeDEPositiveTD.Explicit.splitM .low e θ) 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PB .low e-0)
    rw [hsub]; exact hz.2.2.1
  · change (0:ℝ)^2≤aeval θ (0:ℚ[X])
    simp
  -- highH
  · change (pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) 1 (-(θ-(v:ℝ))))^2≤
      aeval θ (NegativeDEPositiveTD.Certificate.PH .high-C 2*NegativeDEPositiveTD.Certificate.k .high*S11.comp smallDelta)
    rw [map_sub,map_mul,map_mul,hcomp,hPH]
    simp only [aeval_C,NegativeDEPositiveTD.Certificate.k_eval,eq_ratCast,Rat.cast_ofNat]
    change (pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) 1 (-(θ-(v:ℝ))))^2≤(NegativeDEPositiveTD.Explicit.k .high θ)^2+1^2-
      2*NegativeDEPositiveTD.Explicit.k .high θ*1*aeval (θ-(v:ℝ)) S11 at hH
    linarith [hH]
  · change (pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) (NegativeDEPositiveTD.Explicit.l .high θ) 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PG .high-0)
    rw [hsub]; exact hz.2.1
  · change (pairNorm (NegativeDEPositiveTD.Explicit.l .high θ) (NegativeDEPositiveTD.Explicit.splitM .high e θ) 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PB .high e-0)
    rw [hsub]; exact hz.2.2.1
  · change (pairNorm 1 (NegativeDEPositiveTD.Explicit.c .high θ) 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PD .high)
    exact hz.2.2.2.1
  -- highG
  · change (pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) 1 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PH .high-0)
    rw [hsub]; exact hz.1
  · change (pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) (NegativeDEPositiveTD.Explicit.l .high θ) (-(θ-(v:ℝ))))^2≤
      aeval θ (NegativeDEPositiveTD.Certificate.PG .high-C 2*NegativeDEPositiveTD.Certificate.k .high*NegativeDEPositiveTD.Certificate.l .high*S11.comp smallDelta)
    rw [map_sub,map_mul,map_mul,map_mul,hcomp,hPG]
    simp only [aeval_C,NegativeDEPositiveTD.Certificate.k_eval,NegativeDEPositiveTD.Certificate.l_eval,eq_ratCast,Rat.cast_ofNat]
    change (pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) (NegativeDEPositiveTD.Explicit.l .high θ) (-(θ-(v:ℝ))))^2≤(NegativeDEPositiveTD.Explicit.k .high θ)^2+
      (NegativeDEPositiveTD.Explicit.l .high θ)^2-2*NegativeDEPositiveTD.Explicit.k .high θ*NegativeDEPositiveTD.Explicit.l .high θ*aeval (θ-(v:ℝ)) S11 at hG
    linarith [hG]
  · change (pairNorm (NegativeDEPositiveTD.Explicit.l .high θ) (NegativeDEPositiveTD.Explicit.splitM .high e θ) 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PB .high e-0)
    rw [hsub]; exact hz.2.2.1
  · change (pairNorm 1 (NegativeDEPositiveTD.Explicit.c .high θ) 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PD .high)
    exact hz.2.2.2.1
  -- highB
  · change (pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) 1 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PH .high-0)
    rw [hsub]; exact hz.1
  · change (pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) (NegativeDEPositiveTD.Explicit.l .high θ) 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PG .high-0)
    rw [hsub]; exact hz.2.1
  · change (pairNorm (NegativeDEPositiveTD.Explicit.l .high θ) (NegativeDEPositiveTD.Explicit.splitM .high e θ) (-(θ-(v:ℝ))))^2≤
      aeval θ (NegativeDEPositiveTD.Certificate.PB .high e-C 2*NegativeDEPositiveTD.Certificate.l .high*NegativeDEPositiveTD.Certificate.mLo .high e*S11.comp smallDelta)
    rw [map_sub,map_mul,map_mul,map_mul,hcomp,hPB]
    simp only [aeval_C,NegativeDEPositiveTD.Certificate.l_eval,eq_ratCast,Rat.cast_ofNat]
    change (pairNorm (NegativeDEPositiveTD.Explicit.l .high θ) (NegativeDEPositiveTD.Explicit.splitM .high e θ) (-(θ-(v:ℝ))))^2≤(NegativeDEPositiveTD.Explicit.l .high θ)^2+
      (aeval θ (NegativeDEPositiveTD.Certificate.mHi .high e))^2-2*NegativeDEPositiveTD.Explicit.l .high θ*aeval θ (NegativeDEPositiveTD.Certificate.mLo .high e)*
        aeval (θ-(v:ℝ)) S11 at hB
    linarith [hB]
  · change (pairNorm 1 (NegativeDEPositiveTD.Explicit.c .high θ) 0)^2≤aeval θ (NegativeDEPositiveTD.Certificate.PD .high)
    exact hz.2.2.2.1

theorem small_nonradical_lower (r : SmallCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) :
    aeval θ (smallNonradical r e)≤ smallActualA r e θ := by
  have hdom := small_domain r hθ
  have hf := Explicit.family_frame_domain .small (smallFamily r) hdom
  have hd := small_angle_domain r hθ
  have hp := split_positive .small (smallFamily r) e hdom
  have hg := g_polynomial_lower hf
  have hgv := g_constant_lower v (by norm_num [v,frameCap])
  have hcomp (q : ℚ[X]) : aeval θ (q.comp smallDelta)=aeval (θ-(v:ℝ)) q := by
    rw [aeval_comp]; simp [smallDelta]
  cases r
  · have hb := NegativeDEPositiveTD.Certificate.low_nonradical_lower e hdom
    change aeval θ (NegativeDEPositiveTD.Certificate.lowB e+gPoly)≤NegativeDEPositiveTD.Certificate.lowNonradical e θ+NegativeEH.g θ+0
    rw [map_add]
    linarith
  · have hb := NegativeDEPositiveTD.Certificate.low_nonradical_lower e hdom
    have ht := taylor_bounds (show θ-(v:ℝ)∈Icc 0 frameCap from hd)
    change aeval θ (NegativeDEPositiveTD.Certificate.lowB e+C (gStar v)+C10.comp smallDelta-1)≤
      NegativeDEPositiveTD.Certificate.lowNonradical e θ+NegativeEH.g (v:ℝ)+1*(Real.cos (θ-(v:ℝ))-1)
    simp only [map_sub,map_add,aeval_C,eq_ratCast,map_one,hcomp]
    linarith [ht.2.2.2.2.1]
  · have hb := NegativeDEPositiveTD.Certificate.high_nonradical_lower e hdom
    have ht := taylor_bounds (show θ-(v:ℝ)∈Icc 0 frameCap from hd)
    change aeval θ (NegativeDEPositiveTD.Certificate.highB e+C (gStar v)+C10.comp smallDelta-1)≤
      NegativeDEPositiveTD.Certificate.highNonradical e θ+NegativeEH.g (v:ℝ)+1*(Real.cos (θ-(v:ℝ))-1)
    simp only [map_sub,map_add,aeval_C,eq_ratCast,map_one,hcomp]
    linarith [ht.2.2.2.2.1]
  · have hb := NegativeDEPositiveTD.Certificate.high_nonradical_lower e hdom
    have ht := taylor_bounds (show θ-(v:ℝ)∈Icc 0 frameCap from hd)
    have hl : 0<NegativeDEPositiveTD.Explicit.l .high θ := hp.2.1
    have hcos := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hl.le
    change aeval θ (NegativeDEPositiveTD.Certificate.highB e+C (gStar v)+NegativeDEPositiveTD.Certificate.l .high*(C10.comp smallDelta-1))≤
      NegativeDEPositiveTD.Certificate.highNonradical e θ+NegativeEH.g (v:ℝ)+NegativeDEPositiveTD.Explicit.l .high θ*(Real.cos (θ-(v:ℝ))-1)
    simp only [map_sub,map_add,map_mul,aeval_C,eq_ratCast,map_one,hcomp,NegativeDEPositiveTD.Certificate.l_eval]
    linarith
  · have hb := NegativeDEPositiveTD.Certificate.high_nonradical_lower e hdom
    have ht := taylor_bounds (show θ-(v:ℝ)∈Icc 0 frameCap from hd)
    have hl : 0<NegativeDEPositiveTD.Explicit.l .high θ := hp.2.1
    have hq := NegativeDEPositiveTD.Certificate.qStar_lower e hdom
    have hqpos : 0≤aeval θ NegativeDEPositiveTD.Certificate.qStar := (hl.le.trans (le_max_left _ _)).trans hq
    have h₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hqpos
    have h₂ := mul_le_mul_of_nonpos_right hq (sub_nonpos.mpr (Real.cos_le_one (θ-(v:ℝ))))
    change aeval θ (NegativeDEPositiveTD.Certificate.highB e+C (gStar v)+NegativeDEPositiveTD.Certificate.qStar*(C10.comp smallDelta-1))≤
      NegativeDEPositiveTD.Certificate.highNonradical e θ+NegativeEH.g (v:ℝ)+
        max (NegativeDEPositiveTD.Explicit.l .high θ) (NegativeDEPositiveTD.Explicit.splitM .high e θ)*(Real.cos (θ-(v:ℝ))-1)
    simp only [map_sub,map_add,map_mul,aeval_C,eq_ratCast,map_one,hcomp]
    linarith

theorem small_baseline_low (e : Split) (θ : ℝ) :
    Explicit.baseline .small .low (Explicit.splitA e θ) (Explicit.splitT e θ)=
      NegativeDEPositiveTD.Certificate.lowBase e θ 0 := by
  simp only [Explicit.baseline,Explicit.sortedD,ite_true,Explicit.k,Explicit.l,Explicit.c,
    Explicit.m,Explicit.sigma,Explicit.eta,
    NegativeDEPositiveTD.Certificate.lowBase,NegativeDEPositiveTD.Explicit.baseline,
    NegativeDEPositiveTD.Explicit.m,
    NegativeDEPositiveTD.Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,sub_self,
    mul_zero,add_zero]
  ring

theorem small_baseline_high (e : Split) (θ : ℝ) :
    Explicit.baseline .small .high (Explicit.splitA e θ) (Explicit.splitT e θ)=
      NegativeDEPositiveTD.Certificate.highBase e θ 0 := by
  simp only [Explicit.baseline,Explicit.sortedD,Bool.false_eq_true,ite_false,Explicit.k,Explicit.l,
    Explicit.c,Explicit.m,Explicit.sigma,Explicit.eta,
    NegativeDEPositiveTD.Certificate.highBase,NegativeDEPositiveTD.Explicit.fullBaseline,
    NegativeDEPositiveTD.Explicit.baseline,NegativeDEPositiveTD.Explicit.secant,
    NegativeDEPositiveTD.Explicit.m,
    Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,add_zero]
  ring

theorem small_scalar_identity (r : SmallCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) :
    smallValue r e θ=smallActualA r e θ-R*∑i,smallNorm r e θ i := by
  have hdom := small_domain r hθ
  rw [Fin.sum_univ_four]
  cases r
  · have hid := NegativeDEPositiveTD.Certificate.low_baseline_identity e (s:=0) hdom ⟨le_rfl,hdom.1⟩
    change Explicit.baseline .small .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.g θ=
      (NegativeDEPositiveTD.Certificate.lowNonradical e θ+NegativeEH.g θ+0)-R*(pairNorm (NegativeDEPositiveTD.Explicit.k .low θ) 1 0+
        pairNorm (NegativeDEPositiveTD.Explicit.k .low θ) (NegativeDEPositiveTD.Explicit.l .low θ) 0+
        pairNorm (NegativeDEPositiveTD.Explicit.l .low θ) (NegativeDEPositiveTD.Explicit.splitM .low e θ) 0+0)
    rw [small_baseline_low,hid]
    simp only [NegativeDEPositiveTD.Explicit.secant,Real.cos_zero,div_one,sub_self,mul_zero,Real.tan_zero,sub_zero]
    ring
  · have hid := NegativeDEPositiveTD.Certificate.low_H_identity e hdom (θ-(v:ℝ))
    change Explicit.baseline .small .low (Explicit.splitA e θ) (Explicit.splitT e θ)+
        (NegativeEH.g (v:ℝ)+V R (NegativeDEPositiveTD.Explicit.k .low θ) 1 (θ-(v:ℝ)))=
      (NegativeDEPositiveTD.Certificate.lowNonradical e θ+NegativeEH.g (v:ℝ)+1*(Real.cos (θ-(v:ℝ))-1))-
        R*(pairNorm (NegativeDEPositiveTD.Explicit.k .low θ) 1 (-(θ-(v:ℝ)))+
        pairNorm (NegativeDEPositiveTD.Explicit.k .low θ) (NegativeDEPositiveTD.Explicit.l .low θ) 0+
        pairNorm (NegativeDEPositiveTD.Explicit.l .low θ) (NegativeDEPositiveTD.Explicit.splitM .low e θ) 0+0)
    rw [small_baseline_low]
    linarith only [hid]
  · change Explicit.baseline .small .high (Explicit.splitA e θ) (Explicit.splitT e θ)+
        (NegativeEH.g (v:ℝ)+V R (NegativeDEPositiveTD.Explicit.k .high θ) 1 (θ-(v:ℝ)))=
      (NegativeDEPositiveTD.Certificate.highNonradical e θ+NegativeEH.g (v:ℝ)+1*(Real.cos (θ-(v:ℝ))-1))-
        R*(pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) 1 (-(θ-(v:ℝ)))+
        pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) (NegativeDEPositiveTD.Explicit.l .high θ) 0+
        pairNorm (NegativeDEPositiveTD.Explicit.l .high θ) (NegativeDEPositiveTD.Explicit.splitM .high e θ) 0+pairNorm 1 (NegativeDEPositiveTD.Explicit.c .high θ) 0)
    rw [small_baseline_high,NegativeDEPositiveTD.Certificate.high_baseline_identity]
    simp only [NegativeDEPositiveTD.Explicit.secant,Real.cos_zero,div_one,mul_zero,Real.tan_zero,add_zero,V]
    ring
  · change Explicit.baseline .small .high (Explicit.splitA e θ) (Explicit.splitT e θ)+
        (NegativeEH.g (v:ℝ)+V R (NegativeDEPositiveTD.Explicit.k .high θ) (NegativeDEPositiveTD.Explicit.l .high θ) (θ-(v:ℝ)))=
      (NegativeDEPositiveTD.Certificate.highNonradical e θ+NegativeEH.g (v:ℝ)+NegativeDEPositiveTD.Explicit.l .high θ*(Real.cos (θ-(v:ℝ))-1))-
        R*(pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) 1 0+
        pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) (NegativeDEPositiveTD.Explicit.l .high θ) (-(θ-(v:ℝ)))+
        pairNorm (NegativeDEPositiveTD.Explicit.l .high θ) (NegativeDEPositiveTD.Explicit.splitM .high e θ) 0+pairNorm 1 (NegativeDEPositiveTD.Explicit.c .high θ) 0)
    rw [small_baseline_high,NegativeDEPositiveTD.Certificate.high_baseline_identity]
    simp only [NegativeDEPositiveTD.Explicit.secant,Real.cos_zero,div_one,mul_zero,Real.tan_zero,add_zero,V]
    ring
  · change Explicit.baseline .small .high (Explicit.splitA e θ) (Explicit.splitT e θ)+
        (NegativeEH.g (v:ℝ)+V R (min (NegativeDEPositiveTD.Explicit.l .high θ) (NegativeDEPositiveTD.Explicit.splitM .high e θ))
          (max (NegativeDEPositiveTD.Explicit.l .high θ) (NegativeDEPositiveTD.Explicit.splitM .high e θ)) (θ-(v:ℝ)))=
      (NegativeDEPositiveTD.Certificate.highNonradical e θ+NegativeEH.g (v:ℝ)+
        max (NegativeDEPositiveTD.Explicit.l .high θ) (NegativeDEPositiveTD.Explicit.splitM .high e θ)*(Real.cos (θ-(v:ℝ))-1))-
        R*(pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) 1 0+
        pairNorm (NegativeDEPositiveTD.Explicit.k .high θ) (NegativeDEPositiveTD.Explicit.l .high θ) 0+
        pairNorm (NegativeDEPositiveTD.Explicit.l .high θ) (NegativeDEPositiveTD.Explicit.splitM .high e θ) (-(θ-(v:ℝ)))+pairNorm 1 (NegativeDEPositiveTD.Explicit.c .high θ) 0)
    rw [small_baseline_high,NegativeDEPositiveTD.Certificate.high_baseline_identity]
    simp only [NegativeDEPositiveTD.Explicit.secant,Real.cos_zero,div_one,mul_zero,Real.tan_zero,add_zero,V,
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
      (by simpa only [smallNumerator,hf,ite_true] using hnum)
    have hD : smallNorm r e θ 3=0 := by simp [smallNorm,hf]
    rw [Fin.sum_univ_four,hD,add_zero]
    exact hp
  · have hp := num4_transfer (hmass 0 hθ) (hmass 1 hθ) (hmass 2 hθ) (hmass 3 hθ)
      (hnorm 0) (hnorm 1) (hnorm 2) (hnorm 3)
      (hbound 0) (hbound 1) (hbound 2) (hbound 3) hA
      (by simpa only [smallNumerator,hf,reduceCtorEq,ite_false] using hnum)
    rw [Fin.sum_univ_four]
    exact hp

/-- The low equal-angle EH endpoint, with its actual nonsecant gain. -/
theorem small_low_equal_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/10)) :
    0<Explicit.baseline .small .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.g θ := by
  have hθ' : θ∈Icc (smallLeft .lowZero:ℝ) (smallRight .lowZero:ℝ) := by
    norm_num [smallLeft,smallRight,v]; exact hθ
  exact small_value_positive .lowZero e hθ'

theorem small_low_negative_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/10:ℝ) (1/6)) :
    0<Explicit.baseline .small .low (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.g (1/10)+
      V R (Explicit.k .small .low θ) 1 (θ-1/10) := by
  have hθ' : θ∈Icc (smallLeft .lowH:ℝ) (smallRight .lowH:ℝ) := by
    norm_num [smallLeft,smallRight,v,PositiveTD.Certificate.L]; exact hθ
  have h : 0<Explicit.baseline .small .low (Explicit.splitA e θ) (Explicit.splitT e θ)+
      (NegativeEH.g (v:ℝ)+V R (Explicit.k .small .low θ) 1 (θ-(v:ℝ))) :=
    small_value_positive .lowH e hθ'
  have hv : ((v:ℚ):ℝ)=1/10 := by norm_num [v]
  rw [hv] at h
  linarith

theorem small_high_negative_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (i : Fin 3) :
    0<Explicit.baseline .small .high (Explicit.splitA e θ) (Explicit.splitT e θ)+NegativeEH.g (1/10)+
      Explicit.V .small .high θ (Explicit.splitT e θ) i (θ-1/10) := by
  have hθ' (r : SmallCase) (hr : smallFamily r=.high) :
      θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ) := by
    cases r <;> simp [smallFamily] at hr <;>
      norm_num [smallLeft,smallRight,PositiveTD.Certificate.L,PositiveTD.Certificate.h] <;> exact hθ
  have hv : ((v:ℚ):ℝ)=1/10 := by norm_num [v]
  fin_cases i
  · have h : 0<Explicit.baseline .small .high (Explicit.splitA e θ) (Explicit.splitT e θ)+
        (NegativeEH.g (v:ℝ)+Explicit.V .small .high θ (Explicit.splitT e θ) 0 (θ-(v:ℝ))) :=
      small_value_positive .highH e (hθ' .highH rfl)
    rw [hv] at h
    change 0<_+_+Explicit.V .small .high θ (Explicit.splitT e θ) 0 (θ-1/10)
    linarith
  · have h : 0<Explicit.baseline .small .high (Explicit.splitA e θ) (Explicit.splitT e θ)+
        (NegativeEH.g (v:ℝ)+Explicit.V .small .high θ (Explicit.splitT e θ) 1 (θ-(v:ℝ))) :=
      small_value_positive .highG e (hθ' .highG rfl)
    rw [hv] at h
    change 0<_+_+Explicit.V .small .high θ (Explicit.splitT e θ) 1 (θ-1/10)
    linarith
  · have h : 0<Explicit.baseline .small .high (Explicit.splitA e θ) (Explicit.splitT e θ)+
        (NegativeEH.g (v:ℝ)+Explicit.V .small .high θ (Explicit.splitT e θ) 2 (θ-(v:ℝ))) :=
      small_value_positive .highB e (hθ' .highB rfl)
    rw [hv] at h
    change 0<_+_+Explicit.V .small .high θ (Explicit.splitT e θ) 2 (θ-1/10)
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Certificate
