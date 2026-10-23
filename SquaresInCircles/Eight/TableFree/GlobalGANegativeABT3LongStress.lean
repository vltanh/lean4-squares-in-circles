module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3LongSourceData

/-!
# Original BT3 stress with the common negative-A gain

Uncompiled Sections 10--12. The equal A multipliers keep the original
primary gain exactly. The actual T support is valid for both tangent
signs. Each full or sorted-D block is bounded on its own original
point, after both signed budgets have been proved from the cycle.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LongE.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NegativePrimary (erase)

theorem decomposition (C : SignedCycle) {hg : Fin 4} (atG de eh : Bool)
    (hhg : hg=0∨hg=2) (k l m s : ℝ) :
    actualStress C hg atG de eh k l m=
      PositiveBT3.Analytic.fullBaseline k l m (delta C.theta B)+l*gain s+
        TwoPositive.ASupport.charge (eTotal C de eh)+
        (∑i,actualBlocks C hg atG de eh k l m i)+PositiveBT3.Source.tReserve C m+
        l*(PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A)-gain s)+
        NonnegativeTotals.Source.eReserve C de eh := by
  have hh := PositiveBT3.Source.decomposition C atG (!atG) de eh hhg k l m
  dsimp [actualStress,actualBlocks,eTotal,PairedE.cycleTotal,
    PositiveBT3.Source.aReserve,PositiveBT3.Source.eReserve,
    NonnegativeTotals.Source.aReserve,PositiveBT3.Source.aTotal,
    NonnegativeTotals.Source.aTotal,PositiveBT3.Source.eTotal] at ⊢ hh
  linarith

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (atG de eh : Bool) {k l m : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0<m) (hz : delta C.theta B∈Icc 0 frameCap)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) :
    actualStress C hg atG de eh k l m≤0 := by
  have hAB' : C.Feasible A (if !atG then 2 else 0) := by
    cases atG <;> simpa using hAB
  exact PositiveBT3.Source.stress_nonpositive atG (!atG) de eh
    hk hl hm hz hHG hGA hAB' hBT hTD hDE hEH

theorem full_blocks_lower {q k l m s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : 0≤s) (ha : aError C atG= -s) (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (hk : k≤1) (hl : k≤l)
    (hp : ∀i,0<PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i)
    (i : Fin 4) :
    mixedBlock R (PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i)
      (PositiveBT3.qWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i)
      (blocks C hg atG de eh k l m i).P (blocks C hg atG de eh k l m i).N≤
        actualBlocks C hg atG de eh k l m i := by
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R (PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)) j)
        (PositiveBT3.qWeights k l m (PositiveBT3.tilted m (delta C.theta B)) j)
        (blocks C hg atG de eh k l m j).P (blocks C hg atG de eh k l m j).N≤
          PositiveTD.actualPairIncrement (blocks C hg atG de eh k l m j) P := by
    have hd := PositiveBT3.Source.block_coefficients (C:=C) (hg:=hg) (m:=m)
      atG (!atG) de eh hk hl j
    change (blocks C hg atG de eh k l m j).p=_ ∧
      (blocks C hg atG de eh k l m j).q=_ at hd
    have hpn : 0≤(blocks C hg atG de eh k l m j).p := by rw [hd.1]; exact (hp j).le
    have hb := block_budgets hg atG de eh k l m hvar hs ha hz he j
    have hh := PositiveTD.actual_block_minorant hy hP hq hpn hb.1 hb.2
    rwa [hd.1,hd.2] at hh
  fin_cases i
  · simpa [actualBlocks,PositiveBT3.Source.actualBlocks] using hordinary 0 hHy (hc H)
  · simpa [actualBlocks,PositiveBT3.Source.actualBlocks] using
      hordinary 1 (P:=(C.point G).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hc G)
  · simpa [actualBlocks,PositiveBT3.Source.actualBlocks] using
      hordinary 2 (P:=(C.point B).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hc B)
  · simpa [actualBlocks,PositiveBT3.Source.actualBlocks] using
      hordinary 3 (P:=(C.point D).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy) (by simpa using hc D)

theorem reserves_nonnegative {q l m s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hvar : positiveVariation C.theta≤frameCap) (hs : 0≤s)
    (ha : aError C atG= -s) (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (hl : 0≤l) (hm : 0≤m)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A)) :
    0≤PositiveBT3.Source.tReserve C m ∧
    0≤l*(PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A)-gain s) ∧
    0≤NonnegativeTotals.Source.eReserve C de eh := by
  have hb := budgets hg atG de eh 1 l m hvar hs ha hz he
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hT := PositiveBT3.Source.tReserve_nonnegative (hsorted T) (hcontained T) hq hm hb.bt_domain
  have hE := PairedE.selected_charge de eh (hsorted E) (hcontained E) hq
    (original_error_bound hvar hn D) (original_error_bound hvar hn E) hb.e_domain
  exact ⟨hT,mul_nonneg hl (sub_nonneg.mpr hgain),sub_nonneg.mpr hE⟩

theorem full_stress_lower {q k l m s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : 0≤s) (ha : aError C atG= -s) (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A))
    (hhg : hg=0∨hg=2) (hk : k≤1) (hl : k≤l) (hl0 : 0≤l) (hm : 0≤m)
    (hp : ∀i,0<PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i) :
    PositiveBT3.Analytic.fullBaseline k l m (delta C.theta B)+l*gain s+
      TwoPositive.ASupport.charge (eTotal C de eh)+
      (∑i,mixedBlock R (PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i)
        (PositiveBT3.qWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i)
        (blocks C hg atG de eh k l m i).P (blocks C hg atG de eh k l m i).N)≤
      actualStress C hg atG de eh k l m := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    full_blocks_lower atG de eh hcontained hq hHy hGy hBy hDy hvar hs ha hz he hk hl hp i)
  have hres := reserves_nonnegative atG de eh hsorted hcontained hq
    hvar hs ha hz he hl0 hm hgain (hg:=hg)
  rw [decomposition C atG de eh hhg k l m s]
  linarith [hres.1,hres.2.1,hres.2.2]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LongE.Source
