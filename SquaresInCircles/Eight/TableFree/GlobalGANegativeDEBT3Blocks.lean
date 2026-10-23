module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3Ranges
public import SquaresInCircles.Eight.TableFree.ChargedHybridConcentration

/-!
# The complete four-block negative-DE / positive-BT3 scalar model

Uncompiled equations (13)--(16). The fourth block is the original TD0
singleton. Its positive slope is the actual secant-dependent gamma, not
an ordinary circle coefficient. All coefficients are fixed while the
two signed totals are concentrated, and both original mass budgets are
retained through the intrinsic endpoint reduction.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Blocks
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def p (f : Family) (θ : ℝ) : Fin 4→ℝ :=
  ![Explicit.k f θ,Explicit.k f θ,min (Explicit.l f θ) (Explicit.m f θ),Explicit.k f θ]
def q (f : Family) (θ : ℝ) : Fin 4→ℝ :=
  ![1,Explicit.l f θ,max (Explicit.l f θ) (Explicit.m f θ),1]
def positive (f : Family) (θ z s t : ℝ) (i : Fin 4) : ℝ :=
  ChargedHybridConcentration.positive R (Explicit.gamma f θ z s) 0 (p f θ) (q f θ) 3 i t
def negative (f : Family) (θ t : ℝ) (i : Fin 4) : ℝ := V R (p f θ i) (q f θ i) t
def block (f : Family) (θ z s P N : ℝ) (i : Fin 4) : ℝ :=
  ChargedHybridConcentration.block R (Explicit.gamma f θ z s) 0 (p f θ) (q f θ) 3 i P N
def pure (f : Family) (θ z s : ℝ) (i j : Fin 4) : ℝ :=
  ChargedHybridConcentration.pure R (Explicit.gamma f θ z s) 0 (p f θ) (q f θ) 3 i j s θ
def saturated (f : Family) (θ z s : ℝ) (i j : Fin 4) : ℝ :=
  ChargedHybridConcentration.saturated R (Explicit.gamma f θ z s) 0 (p f θ) (q f θ) 3 i j s θ

def ordinaryIndex (i : Fin 4) : Fin 3 := if h : i.val<3 then ⟨i.val,h⟩ else 0

@[simp] theorem positive_ordinary (f : Family) (θ z s t : ℝ) (i : Fin 3) :
    positive f θ z s t i.castSucc=Explicit.U f θ i t := by
  have hi : i.castSucc≠(3:Fin 4) := by fin_cases i <;> decide
  simp only [positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,
    if_neg hi,zero_mul,sub_zero,Explicit.U]
  fin_cases i <;> rfl

@[simp] theorem negative_ordinary (f : Family) (θ t : ℝ) (i : Fin 3) :
    negative f θ t i.castSucc=Explicit.V f θ i t := by fin_cases i <;> rfl

@[simp] theorem block_ordinary (f : Family) (θ z s P N : ℝ) (i : Fin 3) :
    block f θ z s P N i.castSucc=mixedBlock R (Explicit.p f θ i) (Explicit.q f θ i) P N := by
  have hi : i.castSucc≠(3:Fin 4) := by fin_cases i <;> decide
  simp only [block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
    if_neg hi,zero_mul,sub_zero]
  fin_cases i <;> rfl

@[simp] theorem positive_D (f : Family) (θ z s t : ℝ) :
    positive f θ z s t 3= -Explicit.gamma f θ z s*t := by
  simp [positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive]

@[simp] theorem negative_D (f : Family) (θ t : ℝ) :
    negative f θ t 3=Explicit.V f θ 0 t := rfl

@[simp] theorem block_D (f : Family) (θ z s P N : ℝ) :
    block f θ z s P N 3=positive f θ z s P 3+negative f θ N 3 := by
  simp [block,positive,negative,ChargedHybridConcentration.block,
    ChargedHybridConcentration.positive,PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive]

@[simp] theorem positive_zero (f : Family) (θ z s : ℝ) (i : Fin 4) :
    positive f θ z s 0 i=0 := by
  by_cases hi : i=3 <;>
    simp [positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,hi,U_zero]

@[simp] theorem negative_zero (f : Family) (θ : ℝ) (i : Fin 4) : negative f θ 0 i=0 := by
  simp [negative,V_zero]

theorem negative_to_ordinary (f : Family) (θ t : ℝ) (i : Fin 4) :
    negative f θ t i=Explicit.V f θ (ordinaryIndex i) t := by fin_cases i <;> rfl

theorem family_pairs (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f)) (i : Fin 4) :
    0<p f θ i ∧ p f θ i≤q f θ i ∧ q f θ i≤2*p f θ i := by
  have hh := Explicit.family_pairs f hθ (ordinaryIndex i)
  fin_cases i <;> exact hh

theorem concentrate (f : Family) {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f)) (hs : s∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,min (pure f θ z s i j) (saturated f θ z s i j)≤∑k,block f θ z s (P k) (N k) k := by
  have hp := family_pairs f hθ
  exact ChargedHybridConcentration.concentrate R (Explicit.gamma f θ z s) 0
    (p f θ) (q f θ) P N 3 (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hp i).1) (fun i => (hp i).2.1) (fun i => (hp i).2.2)
    hP hN hs (Explicit.frame_domain f hθ) hPb hNb hbalance

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Blocks
