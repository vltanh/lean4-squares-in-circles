module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowSameBlock
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowSecants

/-!
# Eight squares: the low-total positive-BT3 angular envelope

Both signed budgets are kept through the two simplex reductions. The pure, same-block and separated
saturation alternatives all dominate the same ordinary negative increment. The distinguished D block
keeps its whole signed minorant, with the fixed coefficient `K` (`lower`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.LowEnvelope
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryAngleConcentration

def p (t : ℝ) : Fin 4 → ℝ := ![lowK t,lowK t,1,lowK t]
def q (t : ℝ) : Fin 4 → ℝ := ![1,1,lowM t,1]
def block (t : ℝ) (i : Fin 4) (P N : ℝ) : ℝ :=
  if i=3 then -slope*P+vstar N else mixedBlock R (p t i) (q t i) P N

theorem coefficient_ranges {t : ℝ} (ht : t∈Icc 0 L) (i : Fin 4) :
    0<p t i ∧ p t i≤q t i ∧ q t i≤2*p t i ∧ q t i≤Cmax := by
  have hr := Analytic.low_ranges ht
  have hk : 0<lowK t ∧ lowK t≤1 ∧ 1≤2*lowK t ∧ (1:ℝ)≤Cmax := by
    refine ⟨?_,?_,?_,?_⟩ <;> dsimp [K,Cmax] at * <;>
      linarith [hr.1.1,hr.1.2]
  have hm : (0:ℝ)<1 ∧ 1≤lowM t ∧ lowM t≤2*1 ∧ lowM t≤Cmax := by
    refine ⟨by norm_num,?_,?_,hr.2.2⟩ <;> dsimp [Cmax] at * <;>
      linarith [hr.2.1,hr.2.2]
  fin_cases i
  · simpa [p,q] using hk
  · simpa [p,q] using hk
  · simpa [p,q] using hm
  · simpa [p,q] using hk

theorem pure_lower {t : ℝ} (ht : t∈Icc 0 L) (i : Fin 4) :
    V R (lowK t) 1 t≤V R (p t i) (q t i) t := by
  fin_cases i
  · simp [p,q]
  · simp [p,q]
  · simpa [p,q] using LowSecants.B_small ht
  · simp [p,q]

theorem far_lower {t : ℝ} (ht : t∈Icc 0 L) (i : Fin 4) :
    V R (lowK t) 1 t+(3/4)*(frameCap-t)≤V R (p t i) (q t i) frameCap := by
  fin_cases i
  · simpa [p,q] using (LowSecants.H_secant ht).le
  · simpa [p,q] using (LowSecants.H_secant ht).le
  · simpa [p,q] using (LowSecants.B_secant ht).le
  · simpa [p,q] using (LowSecants.H_secant ht).le

theorem positive_lower {t : ℝ} (ht : t∈Icc 0 L) (i : Fin 4) :
    -slope*(frameCap-t)≤
      PositiveTD.Hybrid.positive R slope (p t) (q t) 3 i (frameCap-t) := by
  by_cases hi : i=3
  · simp [PositiveTD.Hybrid.positive,hi]
  · have hc := coefficient_ranges ht i
    have hspan : frameCap-t∈Icc 0 frameCap :=
      ⟨by dsimp [frameCap,L] at *; linarith [ht.2],by linarith [ht.1]⟩
    have hU := OrdinaryPositiveEnvelope.U_lower
      (Real.sqrt_nonneg qCap) radius_sq.le
      hc.1 hc.2.1 hc.2.2.1 hspan
    have hcoef : (109/200)*q t i≤ slope := by
      dsimp [Cmax,slope] at *
      linarith [hc.2.2.2]
    have hprod := mul_le_mul_of_nonneg_right hcoef hspan.1
    have hU' : -(109/200)*q t i*(frameCap-t)≤U R (p t i) (q t i) (frameCap-t) := hU
    simp only [PositiveTD.Hybrid.positive,hi,↓reduceIte]
    simp only [frameCap,slope] at hprod hU' ⊢
    linarith

theorem saturated_lower {t : ℝ} (ht : t∈Icc 0 L) (i : Fin 4) :
    V R (lowK t) 1 t≤PositiveTD.Hybrid.saturated R slope (p t) (q t) 3 i t := by
  have hspan : 0≤frameCap-t := by dsimp [frameCap,L] at *; linarith [ht.2]
  fin_cases i
  · simpa [PositiveTD.Hybrid.saturated,p,q] using H_same_block ht
  · simpa [PositiveTD.Hybrid.saturated,p,q] using H_same_block ht
  · simpa [PositiveTD.Hybrid.saturated,p,q] using
      (LowSecants.B_small ht).trans (B_same_block ht)
  · have hh := far_lower ht 3
    simp only [PositiveTD.Hybrid.saturated]
    dsimp [p,q,slope] at *
    simp only [frameCap] at hh hspan ⊢
    linarith

theorem hybrid_lower {t : ℝ} (ht : t∈Icc 0 L) (P N : Fin 4 → ℝ)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hbalance : (∑i,N i)=t+∑i,P i)
    (hbudget : (∑i,P i)≤frameCap-t) :
    V R (lowK t) 1 t≤
      ∑i,PositiveTD.Hybrid.block R slope (p t) (q t) 3 i (P i) (N i) := by
  have htf : t∈Icc 0 frameCap := PositiveTD.Certificate.low_frame_domain ht
  obtain ⟨i,j,hij⟩ := PositiveTD.Hybrid.concentrate R slope (p t) (q t) P N 3
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (coefficient_ranges ht i).1)
    (fun i => (coefficient_ranges ht i).2.1)
    (fun i => (coefficient_ranges ht i).2.2.1)
    hP hN htf hbudget hbalance
  refine (le_min (pure_lower ht j) ?_).trans hij
  by_cases he : i=j
  · simp only [he,↓reduceIte]
    exact saturated_lower ht j
  · simp only [he,↓reduceIte]
    have hp := positive_lower ht i
    have hn := far_lower ht j
    have hspan : 0≤frameCap-t := by linarith [htf.2]
    simp only [slope,frameCap] at hp hn hspan ⊢
    linarith

/-- The signed ordinary budgets of the cycle imply the low-total envelope; this scalar
concentration moves no angle of the cycle. -/
theorem lower {t : ℝ} (ht : t∈Icc 0 L) (P N : Fin 4 → ℝ)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hbalance : (∑i,N i)=t+∑i,P i)
    (hbudget : (∑i,P i)≤frameCap-t) :
    V R (lowK t) 1 t≤∑i,block t i (P i) (N i) := by
  have hbase := hybrid_lower ht P N hP hN hbalance hbudget
  have hNt : (∑i,N i)≤frameCap := by rw [hbalance]; linarith
  have hr := (Analytic.low_ranges ht).1
  have hchange (i : Fin 4) :
      PositiveTD.Hybrid.block R slope (p t) (q t) 3 i (P i) (N i)≤
        block t i (P i) (N i) := by
    by_cases hi : i=3
    · subst i
      have hNi : N 3∈Icc 0 frameCap :=
        ⟨hN 3,(Finset.single_le_sum (fun j _ => hN j) (Finset.mem_univ 3)).trans hNt⟩
      have hmono := OrdinaryNegativeEnvelope.V_monotone_smaller
        (Real.sqrt_nonneg qCap) (show (0:ℝ)<1 by norm_num) hNi
        (show lowK t∈Icc ((1:ℝ)/2) 1 by dsimp [K] at hr; constructor <;> linarith [hr.1,hr.2])
        (show K∈Icc ((1:ℝ)/2) 1 by norm_num [K]) hr.2
      simpa [PositiveTD.Hybrid.block,block,p,q,vstar] using
        add_le_add_left hmono (-slope*P 3)
    · simp [PositiveTD.Hybrid.block,block,hi]
  exact hbase.trans (Finset.sum_le_sum (fun i _ => hchange i))

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.LowEnvelope
