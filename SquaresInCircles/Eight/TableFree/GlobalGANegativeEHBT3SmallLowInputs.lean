module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3HighScalar
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2SmallLowSlopes
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3LowNegative

/-!
# The small-total EH1/BT3 sorted-D scalar model

Uncompiled Section 4. The original sorted-D support is retained, with
its proved positive penalty and H negative minorant. All ordinary
coefficients are the existing low positive-BT family. The two new
endpoint families are joined over the original A/BT split.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.SmallLow
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
  simp [base,baseline,Explicit.k,Explicit.l,Explicit.m,k,m,
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.SmallLow
