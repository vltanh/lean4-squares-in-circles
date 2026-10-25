module

public import SquaresInCircles.Eight.Owners.GA.Negative.ALongESourceData

/-!
# Eight squares: the longer-E stress on the unchanged original cycle

The A gain is bounded on its original point, the two E
primaries are charged together, and every ordinary block keeps its
original signed angular budgets.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeA.LongE.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NegativePrimary (erase)

theorem decomposition (C : SignedCycle) {hg : Fin 4} (atG de eh : Bool)
    (hhg : hg=0∨hg=2) (k l c s : ℝ) :
    actualStress C hg atG de eh k l c=
      PositiveTD.baseline k l c (delta C.theta T)+l*gain s+
        TwoPositive.ASupport.charge (eTotal C de eh)+
        (∑i,actualBlocks C hg atG de eh k l c i)+PositiveTD.tReserve C c+
        l*(PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A)-gain s)+
        NonnegativeTotals.Source.eReserve C de eh := by
  have hh := NonnegativeTotals.Source.decomposition C atG (!atG) de eh hhg k l c
  dsimp [actualStress,actualBlocks,eTotal,PairedE.cycleTotal,
    NonnegativeTotals.Source.aReserve,NonnegativeTotals.Source.eTotal] at ⊢ hh
  linarith

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (atG de eh : Bool) {k l c : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hz : delta C.theta T∈Icc 0 frameCap)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) :
    actualStress C hg atG de eh k l c≤0 := by
  have hAB' : C.Feasible A (if !atG then 2 else 0) := by
    cases atG <;> simpa using hAB
  exact NonnegativeTotals.Source.stress_nonpositive atG (!atG) de eh
    hk hl hc hz hHG hGA hAB' hBT hTD hDE hEH

theorem block_family_lower {q k l c s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs0 : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta T) (he : s≤eTotal C de eh)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*PositiveTD.tilted c (delta C.theta T) ∧ PositiveTD.tilted c (delta C.theta T)≤2*l)
    (i : Fin 4) :
    PositiveTD.Hybrid.block R (GlobalGA.Secondary.diagonal-1/2)
      (PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)))
      (PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T))) 3 i
      (blocks C hg atG de eh k l c i).P (blocks C hg atG de eh k l c i).N≤
        actualBlocks C hg atG de eh k l c i := by
  have hb := budgets hg atG de eh k l c hvar hs0 ha hz he
  have hw := PositiveTD.coefficient_domain hk hl hcoef hb.td_domain hratio
  have hordinary (i : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R
        (PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)) i)
        (PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T)) i)
        (blocks C hg atG de eh k l c i).P (blocks C hg atG de eh k l c i).N≤
          PositiveTD.actualPairIncrement (blocks C hg atG de eh k l c i) P := by
    have hco := NonnegativeTotals.Source.block_coefficients (C:=C) (hg:=hg) (c:=c)
      atG (!atG) de eh (show k≤1 by linarith [hk.2]) hl.1 i
    change (blocks C hg atG de eh k l c i).p=_ ∧
      (blocks C hg atG de eh k l c i).q=_ at hco
    have hp : 0≤(blocks C hg atG de eh k l c i).p := by rw [hco.1]; exact (hw i).1.le
    have hbud := block_budgets hg atG de eh k l c hvar hs0 ha hz he i
    have hh := PositiveTD.actual_block_minorant hy hP hq hp hbud.1 hbud.2
    rwa [hco.1,hco.2] at hh
  fin_cases i
  · simpa [PositiveTD.Hybrid.block,actualBlocks,NonnegativeTotals.Source.actualBlocks,blocks]
      using hordinary 0 hHy (hc H)
  · simpa [PositiveTD.Hybrid.block,actualBlocks,NonnegativeTotals.Source.actualBlocks,blocks]
      using hordinary 1 (P:=(C.point G).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hc G)
  · simpa [PositiveTD.Hybrid.block,actualBlocks,NonnegativeTotals.Source.actualBlocks,blocks]
      using hordinary 2 (P:=(C.point B).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hc B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
    have hsmall := NegativePrimary.erase_abs_bound de (original_error_bound hvar hn D)
    have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect)
      (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc D) hq hk hcoef hsmall
    simpa [PositiveTD.Hybrid.block,actualBlocks,NonnegativeTotals.Source.actualBlocks,
      blocks,NonnegativeTotals.Source.blocks,Block.P,Block.N,
      PositiveTD.pWeights,PositiveTD.qWeights] using hh

theorem stress_lower {q k l c s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs0 : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta T) (he : s≤eTotal C de eh)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A))
    (hhg : hg=0∨hg=2)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*PositiveTD.tilted c (delta C.theta T) ∧ PositiveTD.tilted c (delta C.theta T)≤2*l) :
    PositiveTD.baseline k l c (delta C.theta T)+l*gain s+
      TwoPositive.ASupport.charge (eTotal C de eh)+
      (∑i,PositiveTD.Hybrid.block R (GlobalGA.Secondary.diagonal-1/2)
        (PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)))
        (PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T))) 3 i
        (blocks C hg atG de eh k l c i).P (blocks C hg atG de eh k l c i).N)≤
      actualStress C hg atG de eh k l c := by
  have hb := budgets hg atG de eh k l c hvar hs0 ha hz he
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsum := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => block_family_lower (hg:=hg) atG de eh hs hc hq hHy hGy hBy hDy
      hvar hs0 ha hz he hk hl hcoef hratio i)
  have hT := PositiveTD.tReserve_nonneg (hs T) (hc T) hq
    (show 0≤c by linarith [hk.1,hcoef.1]) hb.td_domain
  have hA := mul_nonneg (show 0≤l by linarith [hk.1,hl.1]) (sub_nonneg.mpr hgain)
  have hE := PairedE.selected_charge de eh (hs E) (hc E) hq
    (original_error_bound hvar hn D) (original_error_bound hvar hn E) hb.e_domain
  have hE' : 0≤NonnegativeTotals.Source.eReserve C de eh := by
    exact sub_nonneg.mpr hE
  rw [decomposition C atG de eh hhg k l c s]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeA.LongE.Source
