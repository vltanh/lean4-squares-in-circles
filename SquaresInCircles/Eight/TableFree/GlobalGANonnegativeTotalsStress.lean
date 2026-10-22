module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsSourceData

/-!
# The nonnegative A/E stress on the unchanged original points

Uncompiled transcription of equations (12)--(16). Both A primary
contributions and both E primary contributions are collected before
their support charges are applied. The original T point supplies its
own support reserve. Every remaining block uses its unchanged H/G/B/D
point and the original signed variation bounds.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NegativePrimary (erase)

def actualStress (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (k l c : ℝ) : ℝ :=
  demand C (PositiveTD.weights k l c (delta C.theta T))-
    ∑i,work (force C (owners hg ga ab de eh) (PositiveTD.weights k l c (delta C.theta T)) i) (C.point i)

def actualBlocks (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (k l c : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l c 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l c 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l c 2) (C.point B).reflect,
    PositiveTD.actualDIncrement c (erase de (delta C.theta D)) (C.point D).reflect]

def aReserve (C : SignedCycle) (ga ab : Bool) (l : ℝ) : ℝ :=
  l*(PairedE.primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)-
    TwoPositive.ASupport.charge (aTotal C ga ab))
def eReserve (C : SignedCycle) (de eh : Bool) : ℝ :=
  PairedE.primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E)-
    TwoPositive.ASupport.charge (eTotal C de eh)

theorem primary_reserves {q l : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hsmall : ∀i,|delta C.theta i|≤frameCap) (hl : 0≤l)
    (ha : aTotal C ga ab∈Icc 0 frameCap) (he : eTotal C de eh∈Icc 0 frameCap) :
    0≤aReserve C ga ab l ∧ 0≤eReserve C de eh := by
  have hA := PairedE.selected_charge ga ab (hs A) (hc A) hq (hsmall G) (hsmall A) ha
  have hE := PairedE.selected_charge de eh (hs E) (hc E) hq (hsmall D) (hsmall E) he
  exact ⟨mul_nonneg hl (sub_nonneg.mpr hA),sub_nonneg.mpr hE⟩

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab de eh : Bool)
    (hhg : hg=0∨hg=2) (k l c : ℝ) :
    actualStress C hg ga ab de eh k l c=
      PositiveTD.baseline k l c (delta C.theta T)+
        l*TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh)+
        (∑i,actualBlocks C hg ga ab de eh k l c i)+
        PositiveTD.tReserve C c+aReserve C ga ab l+eReserve C de eh := by
  cases ga <;> cases ab <;> cases de <;> cases eh <;> rcases hhg with rfl|rfl <;>
    simp [actualStress,demand,force,source,target,work,add,scale,previous,
      owners,PositiveTD.weights,blocks,actualBlocks,PositiveTD.actualPairIncrement,
      PositiveTD.actualDIncrement,pairF,pairG,PositiveTD.tReserve,PositiveTD.baseline,
      PositiveTD.tilted,aReserve,eReserve,aTotal,eTotal,PairedE.total,PairedE.selected,
      PairedE.primaryGain,erase,Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,
      SignedPoint.reflect,edgeWidth,pairWidth] <;> ring

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool) {k l c : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hz : delta C.theta T∈Icc 0 frameCap)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) :
    actualStress C hg ga ab de eh k l c≤0 := by
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation (PositiveTD.weights_nonneg hk hl hc hz) hf)

theorem block_family_lower {q k l c : ℝ} {C : SignedCycle} {hg : Fin 4}
    (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (he : 0≤eTotal C de eh)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*PositiveTD.tilted c (delta C.theta T) ∧ PositiveTD.tilted c (delta C.theta T)≤2*l)
    (i : Fin 4) :
    PositiveTD.Hybrid.block R (diagonal-1/2)
      (PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)))
      (PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T))) 3 i
      (blocks C hg ga ab de eh k l c i).P (blocks C hg ga ab de eh k l c i).N≤
        actualBlocks C hg ga ab de eh k l c i := by
  have hb := budgets hg ga ab de eh k l c hvar ha hz he
  have hw := PositiveTD.coefficient_domain hk hl hcoef hb.2.2.1 hratio
  have hordinary (i : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R
        (PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)) i)
        (PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T)) i)
        (blocks C hg ga ab de eh k l c i).P (blocks C hg ga ab de eh k l c i).N≤
          PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l c i) P := by
    have hco := block_coefficients (C:=C) (hg:=hg) (c:=c) ga ab de eh
      (show k≤1 by linarith [hk.2]) hl.1 i
    have hp : 0≤(blocks C hg ga ab de eh k l c i).p := by rw [hco.1]; exact (hw i).1.le
    have hbud := block_budgets hg ga ab de eh k l c hvar ha hz he i
    have hh := PositiveTD.actual_block_minorant hy hP hq hp hbud.1 hbud.2
    rwa [hco.1,hco.2] at hh
  fin_cases i
  · simpa [PositiveTD.Hybrid.block,actualBlocks] using hordinary 0 hHy (hc H)
  · simpa [PositiveTD.Hybrid.block,actualBlocks] using hordinary 1
      (P:=(C.point G).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G)
  · simpa [PositiveTD.Hybrid.block,actualBlocks] using hordinary 2
      (P:=(C.point B).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hc B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
    have hsmall := NegativePrimary.erase_abs_bound de (original_error_bound hvar hn D)
    have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect)
      (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc D) hq hk hcoef hsmall
    simpa [PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,
      PositiveTD.pWeights,PositiveTD.qWeights] using hh

theorem stress_lower {q k l c : ℝ} {C : SignedCycle} {hg : Fin 4}
    (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (he : 0≤eTotal C de eh)
    (hhg : hg=0∨hg=2)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*PositiveTD.tilted c (delta C.theta T) ∧ PositiveTD.tilted c (delta C.theta T)≤2*l) :
    PositiveTD.baseline k l c (delta C.theta T)+
      l*TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh)+
      (∑i,PositiveTD.Hybrid.block R (diagonal-1/2)
        (PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)))
        (PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T))) 3 i
        (blocks C hg ga ab de eh k l c i).P (blocks C hg ga ab de eh k l c i).N)≤
      actualStress C hg ga ab de eh k l c := by
  have hb := budgets hg ga ab de eh k l c hvar ha hz he
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsum := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => block_family_lower ga ab de eh hs hc hq hHy hGy hBy hDy
      hvar ha hz he hk hl hcoef hratio i)
  have hT := PositiveTD.tReserve_nonneg (hs T) (hc T) hq
    (show 0≤c by linarith [hk.1,hcoef.1]) hb.2.2.1
  have hprimary := primary_reserves ga ab de eh hs hc hq
    (original_error_bound hvar hn) (show 0≤l by linarith [hk.1,hl.1]) hb.2.1 hb.2.2.2.1
  rw [decomposition C ga ab de eh hhg k l c]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Source
