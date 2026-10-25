module

public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3LowScalar
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowSeparated
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3Endpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.EHSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2EndpointData
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowEnvelope
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowSplit

/-!
# Eight squares: whole-interval slope comparisons for the small EH1/BT3 low family

The separated negative slope is bounded on the
entire coefficient interval by one concave quadratic, then on the whole
remaining-angle interval by the ordinary concavity theorem. The H/G
same-block estimate retains both original masses and uses the signed
norm tangent, not an independently weakened positive/negative split.
-/

section
/-!
## The small-total EH1/BT3 sorted-D scalar model

The sorted-D support is kept, with its positive penalty and the negative minorant of H
(`H_le_negative`). All ordinary coefficients are those of the low positive-BT family. The two
endpoint families of this model are joined over the A/BT split (`concentrate`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.SmallLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryAngleConcentration

abbrev k := PositiveBT3.lowK
abbrev m := PositiveBT3.lowM
abbrev p := PositiveBT3.LowEnvelope.p
abbrev q := PositiveBT3.LowEnvelope.q
abbrev dCost : ℝ := 13/20

def positive (θ P : ℝ) (i : Fin 4) : ℝ :=
  PositiveTD.Hybrid.positive R dCost (p θ) (q θ) 3 i P
def negative (θ N : ℝ) (i : Fin 4) : ℝ := V R (p θ i) (q θ i) N
def block (θ P N : ℝ) (i : Fin 4) : ℝ :=
  PositiveTD.Hybrid.block R dCost (p θ) (q θ) 3 i P N
def pure (θ s : ℝ) (i j : Fin 4) : ℝ :=
  ChargedHybridConcentration.pure R dCost 0 (p θ) (q θ) 3 i j s θ
def saturated (θ s : ℝ) (i j : Fin 4) : ℝ :=
  ChargedHybridConcentration.saturated R dCost 0 (p θ) (q θ) 3 i j s θ

def base (θ a : ℝ) : ℝ := baseline .smallLow θ a (θ-a)

lemma base_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    ConcaveOn ℝ (Icc 0 θ) (base θ) := by
  have hh := TwoPositive.Split.add_constant (PositiveBT3.Analytic.lowScalar_concave hθ)
    (-V R (k θ) 1 θ)
  apply TwoPositive.Split.congr_on hh
  intro a _
  simp [base,baseline,Explicit.k,Explicit.l,Explicit.m,k,
    PositiveBT3.Analytic.lowScalar,PositiveBT3.lowK,PositiveBT3.lowM]

lemma equal_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/10))
    (ha : 0≤a) (hz : 0≤z) : 0<baseline .smallLow (a+z) a z+gain (a+z) := by
  have ht : a+z∈Icc (0:ℝ) (1/6) := ⟨hθ.1,by linarith [hθ.2]⟩
  have hc := TwoPositive.Split.add_constant (base_concave ht) (gain (a+z))
  have hh := concave_gt_of_endpoints hc (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa [base,EndpointInputs.aAt,EndpointInputs.zAt] using Endpoints.small_low_equal .atT hθ)
    (by simpa [base,EndpointInputs.aAt,EndpointInputs.zAt] using Endpoints.small_low_equal .atA hθ)
  simpa [base,show a+z-a=z by ring] using hh

lemma negative_at_v_positive {a z : ℝ} (hθ : a+z∈Icc (1/10:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) :
    0<baseline .smallLow (a+z) a z+gain (1/10)+V R (k (a+z)) 1 (a+z-1/10) := by
  have ht : a+z∈Icc (0:ℝ) (1/6) := ⟨by linarith [hθ.1],hθ.2⟩
  have hc := TwoPositive.Split.add_constant (base_concave ht)
    (gain (1/10)+V R (k (a+z)) 1 (a+z-1/10))
  have hh := concave_gt_of_endpoints hc (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa [base,EndpointInputs.aAt,EndpointInputs.zAt,Explicit.k,k,PositiveBT3.lowK,add_assoc]
      using Endpoints.small_low_negative .atT hθ)
    (by simpa [base,EndpointInputs.aAt,EndpointInputs.zAt,Explicit.k,k,PositiveBT3.lowK,add_assoc]
      using Endpoints.small_low_negative .atA hθ)
  simpa [base,show a+z-a=z by ring,add_assoc] using hh

lemma zero_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z) :
    0<baseline .smallLow (a+z) a z+V R (k (a+z)) 1 (a+z) := by
  have hh := PositiveBT3.Analytic.low_scalar_positive hθ
    (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
  simpa [baseline,PositiveBT3.Analytic.lowScalar,Explicit.k,Explicit.l,Explicit.m,k,
    PositiveBT3.lowK,PositiveBT3.lowM,show a+z-a=z by ring] using hh

@[simp] lemma gain_eq (s : ℝ) : gain s=NegativeEH.g s := by
  dsimp [gain,NegativeEH.g,NegativeEH.K,NegativeEH.beta]

lemma coefficients {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (i : Fin 4) :
    0<p θ i ∧ p θ i≤q θ i ∧ q θ i≤2*p θ i ∧ q θ i≤5821/5000 :=
  PositiveBT3.LowEnvelope.coefficient_ranges hθ i

lemma H_le_negative {θ t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (ht : t∈Icc 0 frameCap) (i : Fin 4) : V R (k θ) 1 t≤negative θ t i := by
  fin_cases i
  · exact le_rfl
  · exact le_rfl
  · exact NegativeDEPositiveBT.LowNegative.H_le_B hθ ht
  · exact le_rfl

lemma zero_same_lower {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (i : Fin 4) :
    V R (k θ) 1 θ≤block θ (frameCap-θ) frameCap i := by
  have hh := PositiveBT3.LowEnvelope.saturated_lower hθ i
  have e : block θ (frameCap-θ) frameCap i=
      PositiveTD.Hybrid.saturated R PositiveBT3.slope (p θ) (q θ) 3 i θ := by
    simp only [block,PositiveTD.Hybrid.block,PositiveTD.Hybrid.saturated,dCost,PositiveBT3.slope]
    split_ifs
    · rfl
    · simp only [mixedBlock,M,show frameCap-θ-frameCap=-θ by ring]
  rw [e]
  exact hh

lemma zero_separated_lower {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (i j : Fin 4) :
    V R (k θ) 1 θ≤positive θ (frameCap-θ) i+negative θ frameCap j := by
  have hu := PositiveBT3.LowEnvelope.positive_lower hθ i
  have hv := PositiveBT3.LowEnvelope.far_lower hθ j
  have hlen : 0≤frameCap-θ := by norm_num [frameCap]; linarith [hθ.2]
  change -dCost*(frameCap-θ)≤positive θ (frameCap-θ) i at hu
  change V R (k θ) 1 θ+(3/4)*(frameCap-θ)≤negative θ frameCap j at hv
  dsimp [dCost] at hu
  simp only [frameCap] at hu hv hlen ⊢
  linarith only [hu,hv,hlen]

lemma concentrate {θ s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc (0:ℝ) (1/10))
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,min (pure θ s i j) (saturated θ s i j)≤∑i,block θ (P i) (N i) i := by
  have hh := ChargedHybridConcentration.concentrate R dCost 0 (p θ) (q θ) P N 3
    (Real.sqrt_nonneg qCap) radius_sq.le (fun i => (coefficients hθ i).1)
    (fun i => (coefficients hθ i).2.1) (fun i => (coefficients hθ i).2.2.1) hP hN
    (show s∈Icc 0 frameCap from ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩)
    (show θ∈Icc 0 frameCap from ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩)
    hPb hNb hbalance
  simpa only [pure,saturated,block,ChargedHybridConcentration.block,zero_mul,sub_zero] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.SmallLow
end
end
end

section
/-!
## Small-EH low-total ordinary slope comparisons

The G same-block
term retains its actual two signed masses. The separated H/G terms use
the already derived fixed-coefficient cubic on the whole remaining-angle
interval [.6,.7]. These are derivative comparisons, not angle samples.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.SmallLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryCurvatureBounds OrdinaryNegativeSlope

theorem G_ratio_constants :
    shapeC0q R (17/25)<259/500 ∧ NegativeAPositiveTD.Curvature.shapeD0q (17/25)<1113/1000 := by
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  constructor
  · unfold shapeC0q
    apply quotient_lt_of_square (pow_pos (shape_pos _) 3) (by norm_num)
    rw [show ((shape (17/25:ℝ))^3)^2=((shape (17/25:ℝ))^2)^3 by ring,shape_sq,mul_pow,hR2]
    norm_num [qCap]
  · unfold NegativeAPositiveTD.Curvature.shapeD0q
    apply quotient_lt_of_square (shape_pos _) (by norm_num)
    rw [mul_pow,hR2,shape_sq]
    norm_num [qCap]

theorem G_constants {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    curvatureZero R (Explicit.k .small .low θ) (Explicit.l .small .low θ)<
      (259/500)*Explicit.l .small .low θ ∧
    NegativeAPositiveTD.Curvature.slopeZero (Explicit.k .small .low θ) (Explicit.l .small .low θ)<
      (1113/1000)*Explicit.l .small .low θ := by
  have hr := NegativeDEPositiveTD.Explicit.low_ranges hθ
  have hk : 0<Explicit.k .small .low θ := by
    change 0<NegativeDEPositiveTD.Explicit.k .low θ; linarith [hr.1]
  have hl : 0<Explicit.l .small .low θ := by
    change 0<NegativeDEPositiveTD.Explicit.l .low θ; linarith [hr.2.2.1]
  have hratio := Explicit.small_low_ratio hθ
  have hquot : Explicit.k .small .low θ/Explicit.l .small .low θ∈Icc (0:ℝ) 1 :=
    ⟨div_nonneg hk.le hl.le,(div_le_one hl).2 (by linarith)⟩
  have hbound := (div_le_iff₀ hl).2 hratio.le
  obtain ⟨_,_,hC,_⟩ := curvature_constants_normalize (R:=R) hk hl
  obtain ⟨_,hD⟩ := NegativeAPositiveTD.Curvature.constants_normalize hk hl
  have hC' := (NegativeAPositiveTD.Curvature.shapeC0q_monotone hquot
    (by norm_num : (17/25:ℝ)∈Icc 0 1) hbound).trans_lt G_ratio_constants.1
  have hD' := (NegativeAPositiveTD.Curvature.shapeD0q_monotone hquot
    (by norm_num : (17/25:ℝ)∈Icc 0 1) hbound).trans_lt G_ratio_constants.2
  rw [hC,hD]
  exact ⟨by linarith [mul_lt_mul_of_pos_left hC' hl],by linarith [mul_lt_mul_of_pos_left hD' hl]⟩

theorem G_same_derivative {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc (0:ℝ) (1/10)) :
    (153/1000:ℝ)<NegativeEH.gD s+NegativeDEPositiveTD.LowSame.ordinaryFirst θ s := by
  have hr := NegativeDEPositiveTD.Explicit.low_ranges hθ
  have hk : 0<Explicit.k .small .low θ := by
    change 0<NegativeDEPositiveTD.Explicit.k .low θ; linarith [hr.1]
  have hl : 0<Explicit.l .small .low θ := by
    change 0<NegativeDEPositiveTD.Explicit.l .low θ; linarith [hr.2.2.1]
  have ht : |s-θ|≤frameCap := by
    rw [abs_le]
    norm_num [frameCap]
    constructor <;> linarith [hs.1,hs.2,hθ.1,hθ.2]
  have hn := NegativeAPositiveTD.Curvature.norm_slope_signed_tangent hk hl ht
  have hc := G_constants hθ
  have hC0 : 0≤curvatureZero R (Explicit.k .small .low θ) (Explicit.l .small .low θ) := by
    dsimp [curvatureZero,pairNorm]; positivity
  have hshift := mul_le_mul_of_nonneg_left
    (show -(s-θ)≤1/6 by linarith [hs.1,hθ.2]) hC0
  have hCscaled := mul_le_mul_of_nonneg_right hc.1.le (by norm_num : (0:ℝ)≤1/6)
  have hsin : (141/250:ℝ)<Real.sin (frameCap-s) := by
    have hh := trig_bracket (l:=(3/5:ℝ)) (u:=frameCap) (x:=frameCap-s) (by norm_num)
      (by norm_num [frameCap]; linarith [Real.pi_gt_three])
      (by norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2])
    norm_num at hh
    linarith [hh.1]
  have hsinL := mul_lt_mul_of_pos_left hsin hl
  have hg := NegativeEH.small_slope hs
  have hl2 : Explicit.l .small .low θ<1352/1000 := hr.2.2.2.1
  dsimp only [NegativeDEPositiveTD.LowSame.ordinaryFirst]
  change (153/1000:ℝ)<NegativeEH.gD s+
    (Explicit.l .small .low θ*Real.sin (frameCap-s)-
      R*normD1 (Explicit.k .small .low θ) (Explicit.l .small .low θ) (s-θ))
  linarith

theorem G_same_monotone {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    MonotoneOn (fun s => NegativeEH.g s+NegativeDEPositiveTD.LowSame.ordinary θ s)
      (Icc (0:ℝ) (1/10)) := by
  have hd (s : ℝ) (hs : s∈Icc (0:ℝ) (1/10)) :=
    (NegativeEH.g_hasDerivAt s).add (NegativeDEPositiveTD.LowSame.ordinary_hasDerivAt hθ
      (show s∈Icc 0 frameCap from ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩))
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  intro s hs
  linarith [G_same_derivative hθ (Ioo_subset_Icc_self hs)]

theorem late_cubic_bound {d : ℝ} (hd : d∈Icc (3/5:ℝ) frameCap) :
    NegativeDEPositiveTD.LowSeparated.lateCubic d<931/1000 := by
  have hm : AntitoneOn NegativeDEPositiveTD.LowSeparated.lateCubic
      (Icc (3/5:ℝ) frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun d _ => (NegativeDEPositiveTD.LowSeparated.lateCubic_derivative d).continuousAt.continuousWithinAt)
      (fun d _ => NegativeDEPositiveTD.LowSeparated.lateCubic_derivative d)
    intro d hd
    have hd2 := pow_le_pow_left₀ (show 0≤d by linarith [hd.1]) hd.2.le 2
    norm_num [frameCap] at hd2
    nlinarith [hd.1]
  have hh := hm (by norm_num [frameCap]) hd hd.1
  have h35 : NegativeDEPositiveTD.LowSeparated.lateCubic (3/5)<931/1000 := by
    norm_num [NegativeDEPositiveTD.LowSeparated.lateCubic]
  linarith

theorem separated_negative_slope (atH : Bool) {θ s : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc (0:ℝ) (1/10)) :
    Vd R (Explicit.k .small .low θ) (NegativeDEPositiveTD.LowSeparated.larger atH θ)
      (frameCap-s)<931/1000 := by
  have hp := NegativeDEPositiveTD.LowSeparated.actual_pair_domain atH hθ
  have hd : frameCap-s∈Icc (3/5:ℝ) frameCap := by
    simp only [frameCap,mem_Icc]
    exact ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hm := NegativeDEPositiveTD.LowSeparated.quadratic_model hp.1 hp.2.1 hp.2.2
    (show frameCap-s∈Icc 0 frameCap from ⟨by simp only [frameCap]; linarith [hs.2],hd.2⟩)
  have hA := NegativeDEPositiveTD.LowSeparated.A_late_upper
    (show frameCap-s∈Icc (9/25:ℝ) frameCap from ⟨by linarith [hd.1],hd.2⟩)
  have hproduct := mul_nonpos_of_nonpos_of_nonneg
    (show NegativeDEPositiveTD.LowSeparated.A (frameCap-s)+389/4000≤0 by linarith)
    (sub_nonneg.mpr hp.2.2.1)
  have he (d q : ℝ) : NegativeDEPositiveTD.LowSeparated.B d+
      NegativeDEPositiveTD.LowSeparated.A d*(q-NegativeDEPositiveTD.LowSeparated.q0)-
      (389/2000)*(q-NegativeDEPositiveTD.LowSeparated.q0)^2=
      NegativeDEPositiveTD.LowSeparated.lateCubic d+
        (NegativeDEPositiveTD.LowSeparated.A d+389/4000)*(q-1)-(389/2000)*(q-1)^2 := by
    dsimp [NegativeDEPositiveTD.LowSeparated.A,NegativeDEPositiveTD.LowSeparated.B,
      NegativeDEPositiveTD.LowSeparated.lateCubic,NegativeDEPositiveTD.LowSeparated.q0]
    ring
  rw [he] at hm
  have hc := late_cubic_bound hd
  change Vd R (NegativeDEPositiveTD.Explicit.k .low θ) _ _<_
  nlinarith [sq_nonneg (NegativeDEPositiveTD.LowSeparated.larger atH θ-1)]

theorem separated_monotone (atH : Bool) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    MonotoneOn (fun s => NegativeEH.g s+
      V R (Explicit.k .small .low θ) (NegativeDEPositiveTD.LowSeparated.larger atH θ) (frameCap-s))
      (Icc (0:ℝ) (1/10)) := by
  have hp := NegativeDEPositiveTD.LowSeparated.actual_pair_domain atH hθ
  have hq : 0<NegativeDEPositiveTD.LowSeparated.larger atH θ := by linarith [hp.2.2.1]
  have hd (s : ℝ) (hs : s∈Icc (0:ℝ) (1/10)) :
      HasDerivAt (fun s => NegativeEH.g s+
        V R (Explicit.k .small .low θ) (NegativeDEPositiveTD.LowSeparated.larger atH θ) (frameCap-s))
        (NegativeEH.gD s+Vd R (Explicit.k .small .low θ)
          (NegativeDEPositiveTD.LowSeparated.larger atH θ) (frameCap-s)*(-1)) s :=
    (NegativeEH.g_hasDerivAt s).add
      ((V_hasDerivAt (R:=R) hp.1 hq (show frameCap-s∈Icc 0 frameCap by
        simp only [frameCap,mem_Icc]; constructor <;> linarith [hs.1,hs.2])).comp s
          ((hasDerivAt_id s).const_sub frameCap))
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  intro s hs
  have hg := NegativeEH.small_slope (Ioo_subset_Icc_self hs)
  have hv := separated_negative_slope atH hθ (Ioo_subset_Icc_self hs)
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.SmallLow
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.SmallLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryCurvatureBounds OrdinaryNegativeSlope

open NegativeAPositiveTD.PositiveSlope
open Arithmetic SecondWord.ReferenceTrig

lemma low_k_range {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    k θ∈Icc (2933/5000:ℝ) (1673/2500) := PositiveBT3.Analytic.low_ranges hθ |>.1

lemma at_six_trig :
    (56464/100000:ℝ)<Real.sin (3/5) ∧ Real.sin (3/5)<56465/100000 ∧
      Real.cos (3/5)<82534/100000 := by
  have hlo := sin11_le_sin (show (0:ℝ)≤3/5 by norm_num)
  have hhi := sin_le_sin9 (show (0:ℝ)≤3/5 by norm_num)
  have hcos := cos_le_cos12 (show (0:ℝ)≤3/5 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hlo hhi hcos
  exact ⟨by linarith,by linarith,by linarith⟩

lemma negative_slope_at_six {κ : ℝ} (hk : κ∈Icc (2933/5000:ℝ) (1673/2500)) :
    Vd R κ 1 (3/5)<(3/4:ℝ) := by
  have hk0 : 0<κ := by linarith [hk.1]
  have ht : (3/5:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos hk0 (by norm_num : (0:ℝ)<1)
    (show |-(3/5:ℝ)|≤frameCap by norm_num [frameCap])
  have hn2 := pairNorm_sq hk0 (by norm_num : (0:ℝ)<1)
    (show |-(3/5:ℝ)|≤frameCap by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,one_pow,mul_one,Real.sin_neg] at hn2
  let b : ℝ := 1+κ^2-2*κ*(56465/100000)
  have hb : 0<b := by dsimp [b]; nlinarith [sq_nonneg (κ-56465/100000)]
  have hbN : b≤(pairNorm κ 1 (-(3/5)))^2 := by
    have hh := mul_le_mul_of_nonneg_left at_six_trig.2.1.le (show 0≤2*κ by positivity)
    dsimp [b]
    nlinarith only [hn2,hh]
  have hlin : (3/4:ℝ)+56464/100000≤3/4+Real.sin (3/5) := by linarith [at_six_trig.1]
  have hsquare := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/4+56464/100000) hlin 2
  have hden := mul_le_mul hsquare hbN hb.le (sq_nonneg _)
  have hc0 : 0≤Real.cos (3/5) := by linarith [(transport_trig ht).1]
  have hc2 := pow_le_pow_left₀ hc0 at_six_trig.2.2.le 2
  have hnum := mul_le_mul_of_nonneg_left hc2 (show 0≤R^2*κ^2 by positivity)
  have hpoly : 0<(3/4+(56464/100000:ℝ))^2*b-qCap*κ^2*(82534/100000)^2 := by
    have hchord := mul_nonneg (sub_nonneg.mpr hk.1) (sub_nonneg.mpr hk.2)
    dsimp [b,qCap]
    nlinarith [hk.1,hk.2]
  have hsq : (R*κ*Real.cos (3/5))^2<
      (3/4+Real.sin (3/5))^2*(pairNorm κ 1 (-(3/5)))^2 := by
    rw [mul_pow,mul_pow]
    rw [radius_sq] at hnum ⊢
    nlinarith only [hnum,hden,hpoly]
  have hh := quotient_lt_of_square hn
    (show 0<3/4+Real.sin (3/5) by linarith [at_six_trig.1]) hsq
  have he : Vd R κ 1 (3/5)= -Real.sin (3/5)+R*κ*Real.cos (3/5)/pairNorm κ 1 (-(3/5)) := by
    dsimp [Vd,mixedNDerivative,normD1,pairProduct]
    rw [zero_sub,Real.cos_neg]
    ring
  rw [he]
  linarith only [hh]

lemma late_negative_slope {θ t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (ht : t∈Icc (3/5:ℝ) frameCap) : Vd R (k θ) 1 t<(3/4:ℝ) := by
  have hk := low_k_range hθ
  have hm := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le
    (show 0<k θ by linarith [hk.1]) (show k θ≤1 by linarith [hk.2])
    (show (1:ℝ)≤2*k θ by linarith [hk.1])
    (show (3/5:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show t∈Icc 0 frameCap from ⟨by linarith [ht.1],ht.2⟩) ht.1
  exact hm.trans_lt (negative_slope_at_six hk)

lemma HG_constants {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    curvatureZero R (k θ) 1<259/500 ∧ NegativeAPositiveTD.Curvature.slopeZero (k θ) 1<1113/1000 := by
  have hk := low_k_range hθ
  have hk0 : 0<k θ := by linarith [hk.1]
  have hkI : k θ∈Icc (0:ℝ) 1 := ⟨hk0.le,by linarith [hk.2]⟩
  have hkm : k θ≤17/25 := by linarith [hk.2]
  obtain ⟨_,_,hC,_⟩ := curvature_constants_normalize (R:=R) hk0 (by norm_num : (0:ℝ)<1)
  obtain ⟨_,hD⟩ := NegativeAPositiveTD.Curvature.constants_normalize hk0 (by norm_num : (0:ℝ)<1)
  have hCm := NegativeAPositiveTD.Curvature.shapeC0q_monotone hkI (by norm_num : (17/25:ℝ)∈Icc 0 1) hkm
  have hDm := NegativeAPositiveTD.Curvature.shapeD0q_monotone hkI (by norm_num : (17/25:ℝ)∈Icc 0 1) hkm
  have href := NegativeEHPositiveTD.SmallLow.G_ratio_constants
  simp only [div_one,one_mul] at hC hD
  rw [hC,hD]
  exact ⟨hCm.trans_lt href.1,hDm.trans_lt href.2⟩

def HG_same (θ s : ℝ) : ℝ := gain s+mixedBlock R (k θ) 1 (frameCap-θ) (frameCap-s)
def HG_same_slope (θ s : ℝ) : ℝ :=
  NegativeEH.gD s+Real.sin (frameCap-s)-R*normD1 (k θ) 1 (s-θ)

lemma HG_same_derivative {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc (0:ℝ) (1/10)) : HasDerivAt (HG_same θ) (HG_same_slope θ s) s := by
  have hk := low_k_range hθ
  have ht : |s-θ|≤frameCap := by
    rw [abs_le]; norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2,hθ.1,hθ.2]
  have hN := (pairNorm_hasDerivAt (show 0<k θ by linarith [hk.1])
    (by norm_num : (0:ℝ)<1) ht).comp s ((hasDerivAt_id s).sub_const θ)
  have hc := (Real.hasDerivAt_cos (frameCap-s)).comp s ((hasDerivAt_id s).const_sub frameCap)
  have hh := (NegativeEH.g_hasDerivAt s).add
    (((hasDerivAt_const s ((k θ)*(PositiveAngularEnvelope.phi (frameCap-θ)-1))).add (hc.sub_const 1)).sub
      ((hN.sub_const (pairNorm (k θ) 1 0)).const_mul R))
  convert hh using 1
  · funext x
    rw [HG_same,gain_eq]
    dsimp [mixedBlock]
    rw [show frameCap-θ-(frameCap-x)=x-θ by ring]
    ring
  · dsimp [HG_same_slope]
    ring

lemma HG_same_slope_positive {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc (0:ℝ) (1/10)) : 0<HG_same_slope θ s := by
  have hk := low_k_range hθ
  have hk0 : 0<k θ := by linarith [hk.1]
  have ht : |s-θ|≤frameCap := by
    rw [abs_le]; norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2,hθ.1,hθ.2]
  have hn := NegativeAPositiveTD.Curvature.norm_slope_signed_tangent hk0
    (by norm_num : (0:ℝ)<1) ht
  have hc := HG_constants hθ
  have hC0 : 0≤curvatureZero R (k θ) 1 := by dsimp [curvatureZero,pairNorm]; positivity
  have hshift := mul_le_mul_of_nonneg_left
    (show -(s-θ)≤1/6 by linarith [hs.1,hθ.2]) hC0
  have hC := mul_le_mul_of_nonneg_right hc.1.le (by norm_num : (0:ℝ)≤1/6)
  have hsin : (141/250:ℝ)<Real.sin (frameCap-s) := by
    have hh := trig_bracket (l:=(3/5:ℝ)) (u:=frameCap) (x:=frameCap-s) (by norm_num)
      (by norm_num [frameCap]; linarith [Real.pi_gt_three])
      (by norm_num [frameCap]; constructor <;> linarith [hs.1,hs.2])
    norm_num at hh
    linarith [hh.1]
  have hg := NegativeEH.small_slope hs
  dsimp only [HG_same_slope]
  nlinarith only [hn,hc.2,hshift,hC,hsin,hg]

lemma HG_same_monotone {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    MonotoneOn (HG_same θ) (Icc (0:ℝ) (1/10)) := by
  exact monoOn_of_hasDeriv_nonneg
    (fun s hs => (HG_same_derivative hθ hs).continuousAt.continuousWithinAt)
    (fun s hs => HG_same_derivative hθ (Ioo_subset_Icc_self hs))
    (fun s hs => (HG_same_slope_positive hθ (Ioo_subset_Icc_self hs)).le)

lemma separated_monotone {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    MonotoneOn (fun s => gain s+V R (k θ) 1 (frameCap-s)) (Icc (0:ℝ) (1/10)) := by
  have hk := low_k_range hθ
  have hd (s : ℝ) (hs : s∈Icc (0:ℝ) (1/10)) :
      HasDerivAt (fun s => NegativeEH.g s+V R (k θ) 1 (frameCap-s))
        (NegativeEH.gD s+Vd R (k θ) 1 (frameCap-s)*(-1)) s :=
    (NegativeEH.g_hasDerivAt s).add
      ((V_hasDerivAt (R:=R) (show 0<k θ by linarith [hk.1]) (by norm_num : (0:ℝ)<1)
        (show frameCap-s∈Icc 0 frameCap by
          simp only [frameCap,mem_Icc]; constructor <;> linarith [hs.1,hs.2])).comp s
            ((hasDerivAt_id s).const_sub frameCap))
  simp only [gain_eq]
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  intro s hs
  have hh := Ioo_subset_Icc_self hs
  have hg := NegativeEH.small_slope hh
  have hv := late_negative_slope hθ
    (show frameCap-s∈Icc (3/5:ℝ) frameCap by
      norm_num [frameCap]; constructor <;> linarith [hh.1,hh.2])
  linarith

lemma positive_monotone {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (i : Fin 4) :
    MonotoneOn (fun s => gain s+positive θ (s-θ) i) (Icc θ (1/10:ℝ)) := by
  have hp := coefficients hθ i
  by_cases hi : i=3
  · subst i
    have e : (fun s => gain s+positive θ (s-θ) 3)=fun s => NegativeEH.g s-dCost*(s-θ) := by
      funext x
      simp only [gain_eq,positive,PositiveTD.Hybrid.positive,↓reduceIte]
      ring
    have hd (s : ℝ) : HasDerivAt (fun s => NegativeEH.g s-dCost*(s-θ))
        (NegativeEH.gD s-dCost*1) s :=
      (NegativeEH.g_hasDerivAt s).sub (((hasDerivAt_id s).sub_const θ).const_mul dCost)
    rw [e]
    apply monoOn_of_hasDeriv_nonneg
      (fun s _ => (hd s).continuousAt.continuousWithinAt) (fun s _ => hd s)
    intro s hs
    have hg := NegativeEH.small_slope
      (show s∈Icc (0:ℝ) (1/10) from ⟨by linarith [hθ.1,hs.1],hs.2.le⟩)
    dsimp [dCost]
    linarith
  · have e : (fun s => gain s+positive θ (s-θ) i)=
        fun s => NegativeEH.g s+U R (p θ i) (q θ i) (s-θ) := by
      funext x
      simp only [gain_eq,positive,PositiveTD.Hybrid.positive,hi,↓reduceIte]
    have hd (s : ℝ) (hs : s∈Icc θ (1/10:ℝ)) :
        HasDerivAt (fun s => NegativeEH.g s+U R (p θ i) (q θ i) (s-θ))
          (NegativeEH.gD s+Ud (p θ i) (q θ i) (s-θ)*1) s := by
      have hU : HasDerivAt (U R (p θ i) (q θ i)) (Ud (p θ i) (q θ i) (s-θ)) (s-θ) :=
        U_hasDerivAt hp.1 (hp.1.trans_le hp.2.1)
          (show s-θ∈Icc 0 frameCap from ⟨by linarith [hs.1],
            by norm_num [frameCap]; linarith [hs.2,hθ.1]⟩)
      have h := (NegativeEH.g_hasDerivAt s).add (hU.comp s ((hasDerivAt_id' s).sub_const θ))
      exact h
    rw [e]
    apply monoOn_of_hasDeriv_nonneg
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => hd s (Ioo_subset_Icc_self hs))
    intro s hs
    have hg := NegativeEH.small_slope
      (show s∈Icc (0:ℝ) (1/10) from ⟨by linarith [hθ.1,hs.1],hs.2.le⟩)
    have hu := NegativeEH.Slopes.small_positive hp.1 hp.2.1 hp.2.2.1
      (show s-θ∈Icc (0:ℝ) (1/10) from ⟨by linarith [hs.1],by linarith [hs.2,hθ.1]⟩)
    linarith [hp.2.2.2]

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.SmallLow
end
end
end
