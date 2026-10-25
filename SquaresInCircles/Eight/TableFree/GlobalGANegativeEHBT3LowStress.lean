module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3OriginalStress
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3LowEnvelope

/-!
# Original sorted-D necessity in the small-EH small-total sector

Uncompiled Section 4. The distinguished D block is bounded on its
original two signed arguments. The fixed-K negative reserve from the
sorted-D theorem dominates the current k reserve by an explicit
coefficient comparison. No E nonnegative-total hypothesis is imported
from the positive-BT source theorem.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

abbrev lowP := PositiveBT3.LowEnvelope.p
abbrev lowQ := PositiveBT3.LowEnvelope.q

def lowBlock (t : ℝ) (i : Fin 4) (P N : ℝ) : ℝ :=
  PositiveTD.Hybrid.block R PositiveBT3.slope (lowP t) (lowQ t) 3 i P N

def sortedBlocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k m : ℝ) : Fin 4→ℝ :=
  ![actualBlocks C hg ga ab k 1 m 1 0,actualBlocks C hg ga ab k 1 m 1 1,
    actualBlocks C hg ga ab k 1 m 1 2,PositiveBT3.Source.sortedD C false m]

theorem sorted_decomposition (C : SignedCycle) {hg : Fin 4} (ga ab : Bool)
    (hhg : hg=0∨hg=2) (k m : ℝ) :
    stress C hg ga ab k 1 m 1=
      PositiveBT3.Analytic.lowBaseline k m (delta C.theta B)+
        (∑i,sortedBlocks C hg ga ab k m i)+
        PairedE.primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
        PositiveBT3.Source.tReserve C m+ehGain C k 1 := by
  rw [decomposition C ga ab hhg]
  have hD := PositiveBT3.Source.sortedD_identity C hg ga ab false true k 1 m
  have hsame : PositiveBT3.Source.actualBlocks C hg ga ab false true k 1 m 3=
      actualBlocks C hg ga ab k 1 m 1 3 := rfl
  rw [hsame] at hD
  simp only [sortedBlocks,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.reduceFinMk,Fin.sum_univ_zero,add_zero]
  rw [hD]
  have hk : fullSupport 1 k=fullSupport k 1 := by simp [fullSupport,add_comm]
  have hm : fullSupport m 1=fullSupport 1 m := by simp [fullSupport,add_comm]
  dsimp [PositiveBT3.Analytic.fullBaseline,PositiveBT3.Analytic.lowBaseline]
  rw [hk,hm]
  ring

theorem low_blocks_lower {Q : ℝ} {C : SignedCycle} (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0)
    (ht : total C ga ab∈Icc 0 (1/6:ℝ)) (i : Fin 4) :
    lowBlock (total C ga ab) i
      (blocks C hg ga ab (PositiveBT3.lowK (total C ga ab)) 1
        (PositiveBT3.lowM (total C ga ab)) i).P
      (blocks C hg ga ab (PositiveBT3.lowK (total C ga ab)) 1
        (PositiveBT3.lowM (total C ga ab)) i).N≤
      sortedBlocks C hg ga ab (PositiveBT3.lowK (total C ga ab))
        (PositiveBT3.lowM (total C ga ab)) i := by
  let t := total C ga ab
  let k := PositiveBT3.lowK t
  let m := PositiveBT3.lowM t
  have hr := PositiveBT3.Analytic.low_ranges ht
  have hbud := budgets hg ga ab k 1 m hvar ha hz hs
  have hrot := PositiveBT3.Analytic.low_tilted_ranges ht hbud.bt_domain
  have hk : k∈Icc (1/2:ℝ) (17/20) := by
    dsimp [k,PositiveBT3.K] at *
    exact ⟨by linarith [hr.1.1],by linarith [hr.1.2]⟩
  have hm : 0< m := by dsimp [m,t]; linarith [hr.2.1]
  have hm1 : 1≤ m := by dsimp [m,t]; linarith [hr.2.1]
  have hc1 : 1≤PositiveBT3.tilted m (delta C.theta B) := hm1.trans hrot.1
  have hfull (j : Fin 4) : fullBlock .small k 1 m (delta C.theta B) j
      (blocks C hg ga ab k 1 m j).P (blocks C hg ga ab k 1 m j).N≤
        actualBlocks C hg ga ab k 1 m 1 j :=
    actual_blocks_lower .small hg ga ab hcontained hQ
      hHy hGy hBy hDy hvar ha hz hs hk (by linarith [hk.2] : k≤1) hm (by simp) j
  have hzero : errorCharge .small=0 := rfl
  have h0 : lowBlock t 0 (blocks C hg ga ab k 1 m 0).P (blocks C hg ga ab k 1 m 0).N≤
      sortedBlocks C hg ga ab k m 0 := by
    have hh := hfull 0
    simp only [fullBlock,hzero,zero_mul,sub_zero] at hh
    simpa [lowBlock,PositiveTD.Hybrid.block,lowP,lowQ,PositiveBT3.LowEnvelope.p,
      PositiveBT3.LowEnvelope.q,sortedBlocks,PositiveBT3.pWeights,PositiveBT3.qWeights,k] using hh
  have h1 : lowBlock t 1 (blocks C hg ga ab k 1 m 1).P (blocks C hg ga ab k 1 m 1).N≤
      sortedBlocks C hg ga ab k m 1 := by
    have hh := hfull 1
    simp only [fullBlock,hzero,zero_mul,sub_zero] at hh
    simpa [lowBlock,PositiveTD.Hybrid.block,lowP,lowQ,PositiveBT3.LowEnvelope.p,
      PositiveBT3.LowEnvelope.q,sortedBlocks,PositiveBT3.pWeights,PositiveBT3.qWeights,k] using hh
  have h2 : lowBlock t 2 (blocks C hg ga ab k 1 m 2).P (blocks C hg ga ab k 1 m 2).N≤
      sortedBlocks C hg ga ab k m 2 := by
    have hh := hfull 2
    simp only [fullBlock,hzero,zero_mul,sub_zero] at hh
    simpa [lowBlock,PositiveTD.Hybrid.block,lowP,lowQ,PositiveBT3.LowEnvelope.p,
      PositiveBT3.LowEnvelope.q,sortedBlocks,PositiveBT3.pWeights,PositiveBT3.qWeights,
      min_eq_left hm1,max_eq_right hm1,m] using hh
  have h3 : lowBlock t 3 (blocks C hg ga ab k 1 m 3).P (blocks C hg ga ab k 1 m 3).N≤
      sortedBlocks C hg ga ab k m 3 := by
    have hb3 : blocks C hg ga ab k 1 m 3=
        ⟨PositiveBT3.tilted m (delta C.theta B),1,delta C.theta T,delta C.theta Candidate.D⟩ :=
      rfl
    have hbn := block_budgets hg ga ab k 1 m hvar ha hz hs 3
    rw [hb3] at hbn
    have hdom : PositiveBT3.SignedDomain (delta C.theta T) (delta C.theta Candidate.D) := hbn
    have hcoef : PositiveBT3.tilted m (delta C.theta B)∈Icc 1 PositiveBT3.Cmax := ⟨hc1,hrot.2⟩
    have hminor := PositiveBT3.signed_minorant hcoef hdom
    have hactual : PositiveBT3.D (PositiveBT3.tilted m (delta C.theta B)) (delta C.theta T)
        (delta C.theta Candidate.D)≤PositiveBT3.Source.sortedD C false m :=
      PositiveBT3.Source.sortedD_lower false (hsorted Candidate.D)
        (hcontained Candidate.D) hQ hDy hcoef hdom
    have hN : negativePart (delta C.theta T)+negativePart (delta C.theta Candidate.D)∈
        Icc 0 frameCap :=
      ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hbn.2⟩
    have hmono := OrdinaryNegativeEnvelope.V_monotone_smaller (Real.sqrt_nonneg qCap)
      (by norm_num : (0:ℝ)<1) hN
      (show k∈Icc ((1:ℝ)/2) 1 from ⟨hk.1,by linarith [hk.2]⟩)
      (show PositiveBT3.K∈Icc ((1:ℝ)/2) 1 by norm_num [PositiveBT3.K]) hr.1.2
    simp only [PositiveBT3.positiveTotal,PositiveBT3.negativeTotal,PositiveBT3.vstar] at hminor
    have hl : lowBlock t 3 (blocks C hg ga ab k 1 m 3).P (blocks C hg ga ab k 1 m 3).N=
        -PositiveBT3.slope*(positivePart (delta C.theta T)+
          positivePart (delta C.theta Candidate.D))+
        V R k 1 (negativePart (delta C.theta T)+negativePart (delta C.theta Candidate.D)) := by
      rw [hb3]
      simp [lowBlock,PositiveTD.Hybrid.block,lowP,lowQ,PositiveBT3.LowEnvelope.p,
        PositiveBT3.LowEnvelope.q,Block.P,Block.N,k]
    have hs3 : sortedBlocks C hg ga ab k m 3=PositiveBT3.Source.sortedD C false m := rfl
    rw [hl,hs3]
    linarith
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem low_scalar_nonpositive {Q : ℝ} {C : SignedCycle} {hg : Fin 4} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0)
    (ht : total C ga ab∈Icc 0 (1/6:ℝ))
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (he : magnitude C∈Icc (0:ℝ) (1/10))
    (hhg : hg=0∨hg=2) (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) :
    PositiveBT3.Analytic.lowBaseline (PositiveBT3.lowK (total C ga ab))
      (PositiveBT3.lowM (total C ga ab)) (delta C.theta B)+
      TwoPositive.ASupport.charge (aTotal C ga ab)+NegativeEH.g (magnitude C)+
      (∑i,lowBlock (total C ga ab) i
        (blocks C hg ga ab (PositiveBT3.lowK (total C ga ab)) 1
          (PositiveBT3.lowM (total C ga ab)) i).P
        (blocks C hg ga ab (PositiveBT3.lowK (total C ga ab)) 1
          (PositiveBT3.lowM (total C ga ab)) i).N)≤0 := by
  let k := PositiveBT3.lowK (total C ga ab)
  let m := PositiveBT3.lowM (total C ga ab)
  have hbud := budgets hg ga ab k 1 m hvar ha hz hs
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hA := PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
    (original_error_bound hvar hn G) (original_error_bound hvar hn A)
    (show aTotal C ga ab∈Icc 0 frameCap from ⟨ha,hbud.a_domain.2.trans hbud.total_domain.2⟩)
  have hr := PositiveBT3.Analytic.low_ranges ht
  have hm : 0< m := by dsimp [m]; linarith [hr.2.1]
  have hzframe : delta C.theta B∈Icc 0 frameCap :=
    ⟨hz,hbud.bt_domain.2.trans hbud.total_domain.2⟩
  have hT := PositiveBT3.Source.tReserve_nonnegative (hsorted T) (hcontained T) hQ hm.le hzframe
  have hE := eh_gain_lower .small (k:=k) hflat hb he (by simp)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    low_blocks_lower hg ga ab hsorted hcontained hQ hHy hGy hBy hDy hvar ha hz hs ht i)
  have hid := sorted_decomposition C ga ab hhg k m
  have hupper := stress_nonpositive hg ga ab (show 0≤k by dsimp [k]; linarith [hr.1.1])
    (by norm_num : (0:ℝ)≤1) hm (by norm_num : (0:ℝ)≤1) hzframe hfeasible
  change TwoPositive.ASupport.charge (aTotal C ga ab)≤
    PairedE.primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A) at hA
  change NegativeEH.g (magnitude C)≤ehGain C k 1 at hE
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
