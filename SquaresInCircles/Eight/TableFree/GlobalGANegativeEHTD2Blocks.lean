module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2FarEndpoints
public import SquaresInCircles.Eight.TableFree.ChargedHybridConcentration

/-!
# The genuine-EH TD2 four-block scalar model

Uncompiled data for the small and far EH concentration proofs. The
fourth block is the original DE2 singleton: its negative part has the
H minorant, while its positive part retains the diagonal-support cost.
The far-EH charge is subtracted from the actual total positive mass.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Blocks
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
    if_neg hi,p_ordinary,q_ordinary,Explicit.U]
@[simp] theorem block_ordinary (r : Regime) (f : Family) (θ z P N : ℝ) (i : Fin 3) :
    block r f θ z P N i.castSucc=mixedBlock R (Explicit.p r f θ z i)
      (Explicit.q r f θ z i) P N-Explicit.errorCharge r*P := by
  have hi : i.castSucc≠(3:Fin 4) := by fin_cases i <;> decide
  simp only [block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
    if_neg hi,p_ordinary,q_ordinary]
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Blocks
