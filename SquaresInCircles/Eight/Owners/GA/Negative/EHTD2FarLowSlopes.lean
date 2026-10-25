module

public import SquaresInCircles.Eight.Frames.Ordinary.ShortSecantGrowth
public import SquaresInCircles.Eight.Owners.ChargedOrdinaryConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighSplit
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowPositiveCoefficients
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2EndpointData
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLowSplit
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts

/-!
# Eight squares: far-low signed-mass comparisons on the complete original intervals

The only new scalar reference is the
left endpoint .45 of the full remaining-negative interval [.45,.6].
The negative derivative decreases, so that reference controls the entire
interval for both original H and G coefficients. Positive mass retains
its .005 EH charge. The original B negative mass is dominated by H.
-/

section
/-!
## The negative-EH TD2 four-block scalar model

The fourth block is the DE2 singleton: its negative part has the H minorant, while its positive
part keeps the diagonal-support cost. The far-EH charge is subtracted from the total positive mass
(`concentrate`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Blocks
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

abbrev dCost : ℝ := GlobalGA.Secondary.diagonal-1/2

def p (r : Regime) (f : Family) (θ z : ℝ) : Fin 4→ℝ :=
  ![Explicit.k r f θ,Explicit.k r f θ,min (Explicit.l r f θ) (Explicit.m r f θ z),Explicit.k r f θ]
def q (r : Regime) (f : Family) (θ z : ℝ) : Fin 4→ℝ :=
  ![1,Explicit.l r f θ,max (Explicit.l r f θ) (Explicit.m r f θ z),1]
def positive (r : Regime) (f : Family) (θ z t : ℝ) (i : Fin 4) : ℝ :=
  ChargedHybridConcentration.positive R dCost (Explicit.errorCharge r) (p r f θ z) (q r f θ z) 3 i t
def negative (r : Regime) (f : Family) (θ z t : ℝ) (i : Fin 4) : ℝ :=
  V R (p r f θ z i) (q r f θ z i) t
def block (r : Regime) (f : Family) (θ z P N : ℝ) (i : Fin 4) : ℝ :=
  ChargedHybridConcentration.block R dCost (Explicit.errorCharge r) (p r f θ z) (q r f θ z) 3 i P N
def pure (r : Regime) (f : Family) (θ z s : ℝ) (i j : Fin 4) : ℝ :=
  ChargedHybridConcentration.pure R dCost (Explicit.errorCharge r) (p r f θ z) (q r f θ z) 3 i j s θ
def saturated (r : Regime) (f : Family) (θ z s : ℝ) (i j : Fin 4) : ℝ :=
  ChargedHybridConcentration.saturated R dCost (Explicit.errorCharge r) (p r f θ z) (q r f θ z) 3 i j s θ

def ordinaryIndex (i : Fin 4) : Fin 3 := if h : i.val<3 then ⟨i.val,h⟩ else 0

@[simp] theorem p_ordinary (r : Regime) (f : Family) (θ z : ℝ) (i : Fin 3) :
    p r f θ z i.castSucc=Explicit.p r f θ z i := by fin_cases i <;> rfl
@[simp] theorem q_ordinary (r : Regime) (f : Family) (θ z : ℝ) (i : Fin 3) :
    q r f θ z i.castSucc=Explicit.q r f θ z i := by fin_cases i <;> rfl
@[simp] theorem negative_ordinary (r : Regime) (f : Family) (θ z t : ℝ) (i : Fin 3) :
    negative r f θ z t i.castSucc=Explicit.V r f θ z i t := by
  simp only [negative,p_ordinary,q_ordinary,Explicit.V]
@[simp] theorem positive_ordinary (r : Regime) (f : Family) (θ z t : ℝ) (i : Fin 3) :
    positive r f θ z t i.castSucc=Explicit.U r f θ z i t-Explicit.errorCharge r*t := by
  have hi : i.castSucc≠(3:Fin 4) := by fin_cases i <;> decide
  simp only [positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,
    ite_eq_right hi,p_ordinary,q_ordinary,Explicit.U]
@[simp] theorem block_ordinary (r : Regime) (f : Family) (θ z P N : ℝ) (i : Fin 3) :
    block r f θ z P N i.castSucc=mixedBlock R (Explicit.p r f θ z i)
      (Explicit.q r f θ z i) P N-Explicit.errorCharge r*P := by
  have hi : i.castSucc≠(3:Fin 4) := by fin_cases i <;> decide
  simp only [block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
    ite_eq_right hi,p_ordinary,q_ordinary]
@[simp] theorem positive_D (r : Regime) (f : Family) (θ z t : ℝ) :
    positive r f θ z t 3= -(dCost+Explicit.errorCharge r)*t := by
  simp [positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive]
  ring
@[simp] theorem negative_D (r : Regime) (f : Family) (θ z t : ℝ) :
    negative r f θ z t 3=Explicit.V r f θ z 0 t := rfl
@[simp] theorem block_D (r : Regime) (f : Family) (θ z P N : ℝ) :
    block r f θ z P N 3=positive r f θ z P 3+negative r f θ z N 3 := by
  simp [block,positive,negative,ChargedHybridConcentration.block,
    ChargedHybridConcentration.positive,PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive]
  ring

theorem negative_to_ordinary (r : Regime) (f : Family) (θ z t : ℝ) (i : Fin 4) :
    negative r f θ z t i=Explicit.V r f θ z (ordinaryIndex i) t := by
  fin_cases i <;> rfl

theorem original_pair (r : Regime) (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (Explicit.left r f) (Explicit.right r f)) (hz : z∈Icc 0 θ) (i : Fin 4) :
    0<p r f θ z i ∧ p r f θ z i≤q r f θ z i ∧ q r f θ z i≤2*p r f θ z i := by
  have hh := Explicit.family_pairs r f hθ hz
  fin_cases i
  · exact hh 0
  · exact hh 1
  · exact hh 2
  · exact hh 0

theorem far_pair (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (Explicit.left .far f) (Explicit.right .far f)) (hz : z∈Icc 0 θ) (i : Fin 4) :
    (3/5:ℝ)≤p .far f θ z i ∧ p .far f θ z i≤q .far f θ z i ∧
      q .far f θ z i≤(5/3)*p .far f θ z i := by
  have hh := Explicit.far_pairs f hθ hz
  fin_cases i
  · exact hh 0
  · exact hh 1
  · exact hh 2
  · exact hh 0

theorem concentrate (r : Regime) (f : Family) {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (Explicit.left r f) (Explicit.right r f)) (hz : z∈Icc 0 θ)
    (hs : s∈Icc (Explicit.eLeft r) (Explicit.eRight r))
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,min (pure r f θ z s i j) (saturated r f θ z s i j)≤∑k,block r f θ z (P k) (N k) k := by
  have hp := original_pair r f hθ hz
  exact ChargedHybridConcentration.concentrate R dCost (Explicit.errorCharge r)
    (p r f θ z) (q r f θ z) P N 3 (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hp i).1) (fun i => (hp i).2.1) (fun i => (hp i).2.2) hP hN
    (Explicit.e_frame_domain r hs) (Explicit.family_frame_domain r f hθ) hPb hNb hbalance

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Blocks
end
end
end

section
/-!
## The ten actual small-EH / positive-TD2 endpoint inequalities

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
end
end
end

section
/-!
## High-total negative-EH endpoints at every A/TD split

The E magnitude is fixed before the A/TD split varies. All D supports of the high family stay
full-circle lower bounds, and the B pair keeps its ordered coefficients (`coefficient_ratios`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.HighSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def base (r : Regime) (θ a : ℝ) : ℝ := Explicit.baseline r .high a (θ-a)
def correction (r : Regime) (θ : ℝ) : ℝ :=
  clippedSupport 1 (Explicit.c r .high θ)-fullSupport 1 (Explicit.c r .high θ)
def negative (r : Regime) (θ d : ℝ) (i : Fin 3) (a : ℝ) : ℝ :=
  base r θ a+Explicit.V r .high θ (θ-a) i d

theorem base_identity (r : Regime) (θ a : ℝ) :
    base r θ a=TwoPositive.splitBase (Explicit.k r .high θ) (Explicit.l r .high θ)
      (Explicit.c r .high θ) θ a+correction r θ := by
  simp only [base,Explicit.baseline,show a+(θ-a)=θ by ring,
    Explicit.sortedD,Bool.false_eq_true,ite_false,TwoPositive.splitBase,PositiveTD.baseline,correction]
  dsimp [Explicit.m,Explicit.eta,Explicit.sigma,NegativeDEPositiveTD.Explicit.eta,
    NegativeDEPositiveTD.Explicit.sigma,PositiveTD.tilted,PositiveTD.eta,PositiveTD.sigma]
  ring

theorem coefficient_ratios (r : Regime) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left r .high) (Explicit.right r .high)) :
    0<Explicit.l r .high θ ∧ 0<Explicit.c r .high θ ∧
      (9/10)*Explicit.l r .high θ≤Explicit.c r .high θ ∧
      Explicit.c r .high θ≤(11/10)*Explicit.l r .high θ := by
  cases r
  · have hr := NegativeDEPositiveTD.Explicit.high_ranges hθ
    have hc := NegativeDEPositiveTD.Explicit.high_ratios hθ
    simp only [Explicit.l,Explicit.c]
    exact ⟨by linarith [hr.2.2.1],by linarith [hr.2.2.2.2.1],hc.1.le,by linarith [hc.2,hr.2.2.1]⟩
  · have hr := Explicit.far_high_ranges hθ
    exact ⟨by linarith [hr.2.1.1],by linarith [hr.2.2.1.1],
      by linarith [hr.2.1.1,hr.2.2.2.1],by linarith [hr.2.1.1,hr.2.2.2.2]⟩

theorem coefficient_range (r : Regime) {θ a : ℝ}
    (hθ : θ∈Icc (Explicit.left r .high) (Explicit.right r .high)) (ha : a∈Icc 0 θ) :
    PositiveTD.tilted (Explicit.c r .high θ) (θ-a)∈
      Icc (Explicit.c r .high θ/2) ((23/20)*Explicit.l r .high θ) := by
  have hz : θ-a∈Icc 0 θ := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  cases r
  · exact NegativeDEPositiveTD.HighSplit.coefficient_range hθ ha
  · have hr := Explicit.far_high_ranges hθ
    have hm := Explicit.far_high_tilted hθ hz
    change Explicit.m .far .high θ (θ-a)∈Icc _ _
    exact ⟨by linarith [hm.1,hr.2.2.1.1],hm.2.2.2.2.le⟩

theorem base_concave (r : Regime) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left r .high) (Explicit.right r .high)) :
    ConcaveOn ℝ (Icc 0 θ) (base r θ) := by
  obtain ⟨hl,hc,hlo,hhi⟩ := coefficient_ratios r hθ
  have ht := Explicit.family_frame_domain r .high hθ
  have hh := TwoPositive.Split.high_increment_concave
    (k:=Explicit.k r .high θ) (s:=0) (g:=0) (e:=0)
    hl hlo hhi ht (by norm_num [frameCap])
    (show 0<Explicit.c r .high θ/2 by positivity) le_rfl le_rfl (by simp)
    (fun a ha => coefficient_range r hθ ha)
  have hb : ConcaveOn ℝ (Icc 0 θ)
      (TwoPositive.splitBase (Explicit.k r .high θ) (Explicit.l r .high θ) (Explicit.c r .high θ) θ) := by
    simpa only [neg_zero,TwoPositive.Split.increment_zero,add_zero] using hh
  apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant hb (correction r θ))
  intro a _
  exact (base_identity r θ a).symm

theorem negative_concave (r : Regime) {θ d : ℝ}
    (hθ : θ∈Icc (Explicit.left r .high) (Explicit.right r .high))
    (hd : d∈Icc 0 frameCap) (i : Fin 3) :
    ConcaveOn ℝ (Icc 0 θ) (negative r θ d i) := by
  obtain ⟨hl,hc,hlo,hhi⟩ := coefficient_ratios r hθ
  have ht := Explicit.family_frame_domain r .high hθ
  fin_cases i
  · exact TwoPositive.Split.add_constant (base_concave r hθ) (V R (Explicit.k r .high θ) 1 d)
  · exact TwoPositive.Split.add_constant (base_concave r hθ)
        (V R (Explicit.k r .high θ) (Explicit.l r .high θ) d)
  · have hh := TwoPositive.Split.high_increment_concave
      (k:=Explicit.k r .high θ) (s:=d) (g:=0) (e:=Real.cos d-1)
      hl hlo hhi ht hd (show 0<Explicit.c r .high θ/2 by positivity)
      le_rfl (sub_nonpos.mpr (Real.cos_le_one d)) le_rfl (fun a ha => coefficient_range r hθ ha)
    apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant hh (correction r θ))
    intro a _
    rw [negative,base_identity,TwoPositive.Split.increment_V]
    dsimp [Explicit.V,Explicit.p,Explicit.q,Explicit.m,Explicit.eta,
      NegativeDEPositiveTD.Explicit.eta,PositiveTD.tilted,PositiveTD.eta]
    ring

theorem small_baseline (a z : ℝ) :
    Explicit.baseline .small .high a z=NegativeDEPositiveTD.Explicit.fullBaseline .high a z 0 := by
  simp only [Explicit.baseline,Explicit.sortedD,Bool.false_eq_true,ite_false,Explicit.k,Explicit.l,
    Explicit.c,Explicit.m,Explicit.eta,Explicit.sigma,NegativeDEPositiveTD.Explicit.fullBaseline,
    NegativeDEPositiveTD.Explicit.baseline,NegativeDEPositiveTD.Explicit.secant,
    NegativeDEPositiveTD.Explicit.m,
    Real.cos_zero,Real.tan_zero,div_one,mul_zero,sub_self,add_zero]
  ring

theorem small_zero_positive {a z : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 3) :
    0<Explicit.baseline .small .high a z+Explicit.V .small .high (a+z) z i (a+z) := by
  rw [small_baseline]
  exact NegativeDEPositiveTD.HighSplit.original_pure_at_zero_positive hθ ha hz i

theorem small_v_positive {a z : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 3) :
    0<Explicit.baseline .small .high a z+NegativeEH.g (1/10)+
      Explicit.V .small .high (a+z) z i (a+z-1/10) := by
  have hd : a+z-1/10∈Icc 0 frameCap := by
    norm_num [frameCap]
    exact ⟨by linarith [hθ.1],by linarith [hθ.2]⟩
  have hc := TwoPositive.Split.add_constant (negative_concave .small hθ hd i) (NegativeEH.g (1/10))
  have h0 := Certificate.small_high_negative_positive .atT hθ i
  have h1 := Certificate.small_high_negative_positive .atA hθ i
  have hh := concave_gt_of_endpoints (c:=0) hc (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa [negative,base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,add_assoc,add_comm,add_left_comm] using h0)
    (by simpa [negative,base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,add_assoc,add_comm,add_left_comm] using h1)
  simpa [negative,base,show a+z-a=z by ring,add_assoc,add_comm,add_left_comm] using hh

theorem far_cut_positive (atUpper : Bool) {a z : ℝ}
    (hθ : a+z∈Icc (1/4:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z) (i : Fin 3) :
    0<Explicit.baseline .far .high a z+NegativeEH.G (if atUpper then (1/4:ℝ) else 1/10)+
      Explicit.V .far .high (a+z) z i (a+z-(if atUpper then (1/4:ℝ) else 1/10)) := by
  have hd : a+z-(if atUpper then (1/4:ℝ) else 1/10)∈Icc 0 frameCap := by
    cases atUpper <;> norm_num [frameCap] at * <;> constructor <;> linarith [hθ.1,hθ.2]
  have hc := TwoPositive.Split.add_constant (negative_concave .far hθ hd i)
    (NegativeEH.G (if atUpper then (1/4:ℝ) else 1/10))
  have h0 := Certificate.far_high_negative_positive atUpper .atT hθ i
  have h1 := Certificate.far_high_negative_positive atUpper .atA hθ i
  have hh := concave_gt_of_endpoints (c:=0) hc (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa [negative,base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,add_assoc,add_comm,add_left_comm] using h0)
    (by simpa [negative,base,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,add_assoc,add_comm,add_left_comm] using h1)
  simpa [negative,base,show a+z-a=z by ring,add_assoc,add_comm,add_left_comm] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.HighSplit
end
end
end

section
/-!
## Complete far-EH high-total scalar exclusion

The actual
negative mass is at most .6, since the original EH magnitude is at
least .1. The short-angle growth theorem pays every separated common
mass. The same-block reserve pays the .005 charge without discarding
opposite signed arguments. DE2 is kept as the fourth, distinguished
block throughout. The final negative surplus is concave in the actual
EH magnitude and uses both already proved intrinsic endpoints.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.FarHigh
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryAngleConcentration

lemma pair_data {θ z : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 4) :
    (3/5:ℝ)≤Blocks.p .far .high θ z i ∧
      Blocks.p .far .high θ z i≤Blocks.q .far .high θ z i ∧
      Blocks.q .far .high θ z i≤(5/3)*Blocks.p .far .high θ z i :=
  Blocks.far_pair .high hθ hz i

lemma q_upper {θ z : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 4) : Blocks.q .far .high θ z i≤1 := by
  have hh := Explicit.far_high_q_le_one hθ hz (Blocks.ordinaryIndex i)
  fin_cases i <;> exact hh

lemma positive_lower {θ z P : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : P∈Icc 0 frameCap) (i : Fin 4) :
    -(11/20)*P≤Blocks.positive .far .high θ z P i := by
  have hp := pair_data hθ hz i
  by_cases hi : i=3
  · subst i
    rw [Blocks.positive_D]
    have hh := mul_le_mul_of_nonneg_right
      (show Blocks.dCost+Explicit.errorCharge .far≤(11/20:ℝ) by
        dsimp [Blocks.dCost,Explicit.errorCharge,NegativeEH.epsilon]
        linarith [diagonal_bounds.2]) hP.1
    linarith
  · have hh := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
      (show 0<Blocks.p .far .high θ z i by linarith [hp.1]) hp.2.1
      (show Blocks.q .far .high θ z i≤2*Blocks.p .far .high θ z i by linarith [hp.1,hp.2.2]) hP
    have hq := mul_le_mul_of_nonneg_right (q_upper hθ hz i) hP.1
    simp only [Blocks.positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,ite_eq_right hi]
    dsimp [Explicit.errorCharge,NegativeEH.epsilon]
    nlinarith

lemma separated_lower {θ z P N : ℝ}
    (hθ : θ∈Icc (1/4:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) (i j : Fin 4) :
    Blocks.negative .far .high θ z (N-P) j≤
      Blocks.positive .far .high θ z P i+Blocks.negative .far .high θ z N j := by
  have hj := pair_data hθ hz j
  have hu := positive_lower hθ hz
    (show P∈Icc 0 frameCap from ⟨hP,by norm_num [frameCap]; linarith⟩) i
  have hv := OrdinaryNegativeShortSlope.V_growth
    (show 0<Blocks.p .far .high θ z j by linarith [hj.1]) hj.2.1
    (show (3/5)*Blocks.q .far .high θ z j≤Blocks.p .far .high θ z j by linarith [hj.2.2])
    (show N-P∈OrdinaryNegativeShortSlope.domain from ⟨by linarith,by linarith⟩)
    (show N∈OrdinaryNegativeShortSlope.domain from ⟨hP.trans hPN,hN⟩)
    (by linarith : N-P≤N)
  have hpay := mul_nonneg (show 0≤Blocks.p .far .high θ z j-3/5 by linarith [hj.1]) hP
  dsimp [Blocks.negative]
  nlinarith

lemma same_lower {θ z P N : ℝ}
    (hθ : θ∈Icc (1/4:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) (i : Fin 4) :
    Blocks.negative .far .high θ z (N-P) i≤Blocks.block .far .high θ z P N i := by
  by_cases hi : i=3
  · subst i
    rw [Blocks.block_D]
    exact separated_lower hθ hz hP hPN hN 3 3
  · have hp := pair_data hθ hz i
    have hh := OrdinaryNegativeShortSlope.same_reserve (R:=R) hp.1 hp.2.2 hP hPN hN
    simp only [Blocks.block,Blocks.negative,ChargedHybridConcentration.block,
      PositiveTD.Hybrid.block,ite_eq_right hi]
    dsimp [Explicit.errorCharge,NegativeEH.epsilon]
    linarith

lemma sum_to_negative {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (1/4:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (hs : s∈Icc (1/10:ℝ) (1/4))
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃j : Fin 3,Explicit.V .far .high θ z j (θ-s)≤
      ∑i,Blocks.block .far .high θ z (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .far .high P N hθ hz hs hP hN hPb hNb hbalance
  have horder : s≤θ := by linarith [hθ.1,hs.2]
  have hPcap : 0≤frameCap-θ := by norm_num [frameCap]; linarith [hθ.2]
  have hPN : frameCap-θ≤frameCap-s := by linarith
  have hNcap : frameCap-s≤3/5 := by norm_num [frameCap]; linarith [hs.1]
  have hsat : Blocks.negative .far .high θ z (θ-s) j≤Blocks.saturated .far .high θ z s i j := by
    by_cases hsame : i=j
    · subst j
      have hh := same_lower hθ hz hPcap hPN hNcap i
      simpa only [Blocks.saturated,ChargedHybridConcentration.saturated,↓reduceIte,
        Blocks.block,show frameCap-s-(frameCap-θ)=θ-s by ring] using hh
    · have hh := separated_lower hθ hz hPcap hPN hNcap i j
      simpa only [Blocks.saturated,ChargedHybridConcentration.saturated,ite_eq_right hsame,
        Blocks.positive,Blocks.negative,show frameCap-s-(frameCap-θ)=θ-s by ring] using hh
  have hpure : Blocks.pure .far .high θ z s i j=Blocks.negative .far .high θ z (θ-s) j := by
    simp [Blocks.pure,ChargedHybridConcentration.pure,horder,Blocks.negative]
  rw [hpure,min_eq_left hsat,Blocks.negative_to_ordinary] at hij
  exact ⟨Blocks.ordinaryIndex j,hij⟩

lemma negative_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/4:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (i : Fin 3) :
    0<Explicit.baseline .far .high a z+NegativeEH.G s+
      Explicit.V .far .high (a+z) z i (a+z-s) := by
  have hp := Explicit.family_pairs .far .high hθ ⟨hz,by linarith⟩ i
  have hg := NegativeEH.G_concave.subset
    (Icc_subset_Icc (by norm_num : (0:ℝ)≤1/10)
      (by norm_num [frameCap] : (1/4:ℝ)≤frameCap)) (convex_Icc (1/10:ℝ) (1/4))
  have hv := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hp.1 hp.2.1 hp.2.2)
    (a:=-1) (b:=a+z) (l:=1/10) (u:=1/4)
    (fun s hs => ⟨by linarith [hs.2,hθ.1],by norm_num [frameCap]; linarith [hs.1,hθ.2]⟩)
  have hc := OrdinaryMixedShortReserve.constant_add (hg.add hv) (Explicit.baseline .far .high a z)
  have hc' : ConcaveOn ℝ (Icc (1/10:ℝ) (1/4)) (fun t => Explicit.baseline .far .high a z+
      NegativeEH.G t+Explicit.V .far .high (a+z) z i (a+z-t)) :=
    hc.congr (fun t _ => by
      simp only [Pi.add_apply,Explicit.V]
      rw [show -1*t+(a+z)=a+z-t by ring]
      ring)
  have h0 := HighSplit.far_cut_positive false hθ ha hz i
  have h1 := HighSplit.far_cut_positive true hθ ha hz i
  simp only [Bool.false_eq_true,↓reduceIte] at h0 h1
  have hh := concave_gt_of_endpoints (c:=0) hc' hs h0 h1
  exact hh

theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (1/4:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.stressBase .far .high a z s+
      ∑i,Blocks.block .far .high (a+z) z (P i) (N i) i := by
  obtain ⟨i,hi⟩ := sum_to_negative P N hθ ⟨hz,by linarith⟩ hs hP hN hPb hNb hbalance
  have hh := negative_positive hθ ha hz hs i
  dsimp [Explicit.stressBase,Explicit.gain]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.FarHigh
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.FarLowSlopes
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope OrdinaryNegativeSlope
open NegativeAPositiveTD.PositiveSlope Arithmetic SecondWord.ReferenceTrig

theorem pair_data {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) (hz : z∈Icc 0 θ) (i : Fin 4) :
    (3/5:ℝ)≤Blocks.p .far .low θ z i ∧
    Blocks.p .far .low θ z i≤Blocks.q .far .low θ z i ∧
    Blocks.q .far .low θ z i≤(5/3)*Blocks.p .far .low θ z i :=
  Blocks.far_pair .low hθ hz i

theorem ordinary_q_upper {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (i : Fin 3) : Explicit.q .far .low θ z i≤111/100 := by
  have hr := Explicit.far_low_ranges hθ
  have hm := Explicit.far_low_tilted hθ hz
  fin_cases i
  · show (1:ℝ)≤111/100
    norm_num
  · show Explicit.l .far .low θ≤111/100
    linarith [hr.2.1.2]
  · show max (Explicit.l .far .low θ) (Explicit.m .far .low θ z)≤111/100
    exact max_le (by linarith [hr.2.1.2]) hm.2.1

theorem q_upper {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (i : Fin 4) : Blocks.q .far .low θ z i≤111/100 := by
  have hh := ordinary_q_upper hθ hz (Blocks.ordinaryIndex i)
  fin_cases i <;> exact hh

theorem positive_lower {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) (i : Fin 4) :
    -(12199/20000)*t≤Blocks.positive .far .low θ z t i := by
  have hp := pair_data hθ hz i
  by_cases hi : i=3
  · subst i
    rw [Blocks.positive_D]
    have hh := mul_le_mul_of_nonneg_right
      (show Blocks.dCost+Explicit.errorCharge .far≤(12199/20000:ℝ) by
        dsimp [Blocks.dCost,Explicit.errorCharge,NegativeEH.epsilon]
        linarith [diagonal_bounds.2]) ht.1
    linarith
  · have hh := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
      (show 0<Blocks.p .far .low θ z i by linarith [hp.1]) hp.2.1
      (show Blocks.q .far .low θ z i≤2*Blocks.p .far .low θ z i by linarith [hp.1,hp.2.2]) ht
    have hq := mul_le_mul_of_nonneg_right (q_upper hθ hz i) ht.1
    simp only [Blocks.positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,ite_eq_right hi]
    dsimp [Explicit.errorCharge,NegativeEH.epsilon]
    nlinarith

theorem U_larger_comparison {p q Q t : ℝ} (hp : 0<p) (hq : 0<q)
    (hqQ : q≤Q) (ht : t∈Icc 0 frameCap) : U R p Q t≤U R p q t := by
  have hQ := hq.trans_le hqQ
  have hd {x : ℝ} (hx : x∈Icc 0 frameCap) :=
    (U_hasDerivAt hp hq hx).sub (U_hasDerivAt hp hQ hx)
  have hm : MonotoneOn (fun x => U R p q x-U R p Q x) (Icc 0 frameCap) :=
    monoOn_of_hasDeriv_nonneg
      (fun x hx => (hd hx).continuousAt.continuousWithinAt)
      (fun x hx => hd (Ioo_subset_Icc_self hx))
      (fun x hx => sub_nonneg.mpr
        (NegativeDEPositiveTD.LowPositive.larger_comparison hp hq hqQ (Ioo_subset_Icc_self hx)))
  have hh := hm (by norm_num [frameCap]) ht ht.1
  simp only [U_zero,sub_self] at hh
  linarith

theorem H_le_G {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (_hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) :
    Explicit.U .far .low θ z 0 t≤Explicit.U .far .low θ z 1 t := by
  have hl := (Explicit.far_low_ranges hθ).2.1
  show U R (121/200) 1 t≤U R (121/200) (Explicit.l .far .low θ) t
  exact U_larger_comparison (by norm_num) (by linarith [hl.1]) hl.2 ht

theorem slope_formula (p q t : ℝ) :
    Vd R p q t= -q*Real.sin t+R*p*q*Real.cos t/pairNorm p q (-t) := by
  dsimp [Vd,mixedNDerivative,normD1,pairProduct]
  rw [zero_sub,Real.cos_neg]
  ring

theorem H_initial_slope : Vd R (121/200) 1 0<(41/40:ℝ) := by
  have hn := pairNorm_pos (by norm_num : (0:ℝ)<121/200)
    (by norm_num : (0:ℝ)<1) (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hn2 := pairNorm_sq (by norm_num : (0:ℝ)<121/200)
    (by norm_num : (0:ℝ)<1) (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  rw [Real.sin_zero,mul_zero,add_zero] at hn2
  simp only [pairEnergy] at hn2
  have hN : (11687/10000:ℝ)<pairNorm (121/200) 1 0 := by nlinarith
  rw [slope_formula]
  norm_num only [Real.sin_zero,Real.cos_zero,neg_zero,mul_zero,zero_add,mul_one]
  apply (div_lt_iff₀ hn).2
  nlinarith [radius_bounds.2]

theorem H_upper {θ z t : ℝ} (ht : t∈Icc 0 frameCap) :
    Explicit.V .far .low θ z 0 t≤(41/40)*t := by
  have hh := V_tangent_zero (p:=(121/200:ℝ)) (q:=1)
    (by norm_num) (by norm_num) (by norm_num) ht
  have hp := mul_le_mul_of_nonneg_right H_initial_slope.le ht.1
  exact hh.trans hp

theorem H_le_B {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) :
    Explicit.V .far .low θ z 0 t≤Explicit.V .far .low θ z 2 t := by
  have hr := Explicit.far_low_ranges hθ
  have hm := Explicit.far_low_tilted hθ hz
  have hp := Explicit.family_pairs .far .low hθ hz 2
  have hh := V_chord_lower hp.1 hp.2.1 hp.2.2 ht
  have hlo : (91/100:ℝ)≤Explicit.p .far .low θ z 2 := by
    simpa [Explicit.p,min_eq_left hm.2.2.1.le] using hr.2.1.1
  have hpaid := mul_le_mul_of_nonneg_right hlo ht.1
  have hH := H_upper (θ:=θ) (z:=z) ht
  change (87/70)*Explicit.p .far .low θ z 2*t≤Explicit.V .far .low θ z 2 t at hh
  linarith [ht.1]

theorem left_trig :
    (4349/10000:ℝ)<Real.sin (9/20) ∧ Real.sin (9/20)<87/200 ∧
      Real.cos (9/20)<18009/20000 := by
  have hs := sin11_le_sin (show (0:ℝ)≤9/20 by norm_num)
  have hu := sin_le_sin9 (show (0:ℝ)≤9/20 by norm_num)
  have hc := cos_le_cos12 (show (0:ℝ)≤9/20 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hu hc
  exact ⟨by linarith,by linarith,by linarith⟩

theorem left_negative_slope {q : ℝ} (hq : q∈Icc (91/100:ℝ) 1) :
    Vd R (121/200) q (9/20)<(881/1000:ℝ) := by
  have hq0 : 0<q := by linarith [hq.1]
  have ht : (9/20:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have htr := transport_trig ht
  have hn := pairNorm_pos (by norm_num : (0:ℝ)<121/200) hq0
    (show |-(9/20:ℝ)|≤frameCap by norm_num [frameCap])
  have hn2 := pairNorm_sq (by norm_num : (0:ℝ)<121/200) hq0
    (show |-(9/20:ℝ)|≤frameCap by norm_num [frameCap])
  norm_num only [pairEnergy,pairProduct,Real.sin_neg] at hn2
  have hsprod := mul_le_mul_of_nonneg_left left_trig.2.1.le hq0.le
  have hquad := mul_nonneg (sub_nonneg.mpr hq.1)
    (show 0≤q+91/100-2*(121/200)*(87/200) by linarith [hq.1])
  have hN : (169/200:ℝ)<pairNorm (121/200) q (-(9/20)) := by nlinarith
  have hR : R<(1979/1000:ℝ) := by linarith [radius_bounds.2]
  have hc0 : 0<Real.cos (9/20) := by linarith [htr.1]
  have hRc := mul_lt_mul hR left_trig.2.2.le hc0 (by norm_num : (0:ℝ)≤1979/1000)
  have hnum := mul_lt_mul_of_pos_right hRc (by norm_num : (0:ℝ)<121/200)
  have hqnum := mul_le_mul_of_nonneg_right hq.2
    (show 0≤R*(121/200)*Real.cos (9/20) by positivity)
  have hquot : R*(121/200)*q*Real.cos (9/20)/pairNorm (121/200) q (-(9/20))<
      ((1979/1000)*(121/200)*(18009/20000))/(169/200) := by
    apply (div_lt_iff₀ hn).2
    have hden := mul_lt_mul_of_pos_left hN
      (by norm_num : (0:ℝ)<((1979/1000)*(121/200)*(18009/20000))/(169/200))
    nlinarith
  have hsin := mul_le_mul hq.1 left_trig.1.le
    (by norm_num : (0:ℝ)≤4349/10000) hq0.le
  rw [slope_formula]
  linarith

theorem negative_slope {q t : ℝ} (hq : q∈Icc (91/100:ℝ) 1)
    (ht : t∈Icc (9/20:ℝ) (3/5)) : Vd R (121/200) q t<(881/1000:ℝ) := by
  have hm := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le
    (by norm_num : (0:ℝ)<121/200)
    (by linarith [hq.1] : (121/200:ℝ)≤q)
    (by linarith [hq.2] : q≤2*(121/200))
    (show (9/20:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show t∈Icc 0 frameCap from ⟨by linarith [ht.1],by norm_num [frameCap]; linarith [ht.2]⟩) ht.1
  exact hm.trans_lt (left_negative_slope hq)

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.FarLowSlopes
end
end
end
