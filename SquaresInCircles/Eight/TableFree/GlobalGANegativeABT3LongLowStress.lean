module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3LongStress

/-!
# The small-total longer-E comparison on the original BT3 cycle

Uncompiled Section 10 at z+e≤1/6. The low family is evaluated at
z+e-s. Both A multipliers are one. The full signed sorted-D bound
is applied to the original TD0 and unselected DE arguments, and the
common negative-A gain pays the virtual reduction of E from e to e-s.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LongE.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NegativePrimary (erase)

theorem sorted_decomposition (C : SignedCycle) {hg : Fin 4} (atG de eh : Bool)
    (hhg : hg=0∨hg=2) (k m s : ℝ) :
    actualStress C hg atG de eh k 1 m=
      PositiveBT3.Analytic.lowBaseline k m (delta C.theta B)+gain s+
        TwoPositive.ASupport.charge (eTotal C de eh)+
        (∑i,PositiveBT3.Source.sortedBlocks C hg atG (!atG) de eh k m i)+
        PositiveBT3.Source.tReserve C m+
        (PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A)-gain s)+
        NonnegativeTotals.Source.eReserve C de eh := by
  have hh := PositiveBT3.Source.sorted_decomposition C atG (!atG) de eh hhg k m
  dsimp [actualStress,eTotal,PairedE.cycleTotal,
    PositiveBT3.Source.aReserve,PositiveBT3.Source.eReserve,
    NonnegativeTotals.Source.aReserve,PositiveBT3.Source.aTotal,
    NonnegativeTotals.Source.aTotal,PositiveBT3.Source.eTotal] at ⊢ hh
  linarith

theorem low_blocks_lower {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (ht : effective C de eh s∈Icc 0 (1/6:ℝ)) (i : Fin 4) :
    PositiveBT3.LowEnvelope.block (effective C de eh s) i
      (blocks C hg atG de eh (PositiveBT3.lowK (effective C de eh s)) 1
        (PositiveBT3.lowM (effective C de eh s)) i).P
      (blocks C hg atG de eh (PositiveBT3.lowK (effective C de eh s)) 1
        (PositiveBT3.lowM (effective C de eh s)) i).N≤
      PositiveBT3.Source.sortedBlocks C hg atG (!atG) de eh
        (PositiveBT3.lowK (effective C de eh s)) (PositiveBT3.lowM (effective C de eh s)) i := by
  let t := effective C de eh s
  have hr := PositiveBT3.Analytic.low_ranges ht
  have hzT : delta C.theta B∈Icc 0 t := ⟨hz,by dsimp [t,effective]; linarith⟩
  have hrot := PositiveBT3.Analytic.low_tilted_ranges ht hzT
  have hk : 0<PositiveBT3.lowK t := by dsimp [t]; linarith [hr.1.1]
  have hk1 : PositiveBT3.lowK t≤1 := by dsimp [t,PositiveBT3.K] at *; linarith [hr.1.2]
  have hm1 : 1≤PositiveBT3.lowM t := by dsimp [t] at *; linarith [hr.2.1]
  have hc1 : 1≤PositiveBT3.tilted (PositiveBT3.lowM t) (delta C.theta B) := hm1.trans hrot.1
  have hp (j : Fin 4) : 0<PositiveBT3.pWeights (PositiveBT3.lowK t) 1 (PositiveBT3.lowM t)
      (PositiveBT3.tilted (PositiveBT3.lowM t) (delta C.theta B)) j := by
    fin_cases j <;> simp [PositiveBT3.pWeights,min_eq_left hm1,min_eq_left hc1] <;> linarith
  have hfull (j : Fin 4) := full_blocks_lower atG de eh hcontained hq hHy hGy hBy hDy
    hvar hs ha hz he hk1 hk1 hp j (hg:=hg)
  fin_cases i
  · simpa [PositiveBT3.LowEnvelope.block,PositiveBT3.LowEnvelope.p,PositiveBT3.LowEnvelope.q,
      PositiveBT3.Source.sortedBlocks,actualBlocks,PositiveBT3.pWeights,PositiveBT3.qWeights,t]
      using hfull 0
  · simpa [PositiveBT3.LowEnvelope.block,PositiveBT3.LowEnvelope.p,PositiveBT3.LowEnvelope.q,
      PositiveBT3.Source.sortedBlocks,actualBlocks,PositiveBT3.pWeights,PositiveBT3.qWeights,t]
      using hfull 1
  · simpa [PositiveBT3.LowEnvelope.block,PositiveBT3.LowEnvelope.p,PositiveBT3.LowEnvelope.q,
      PositiveBT3.Source.sortedBlocks,actualBlocks,PositiveBT3.pWeights,PositiveBT3.qWeights,
      min_eq_left hm1,max_eq_right hm1,t] using hfull 2
  · have hb := block_budgets hg atG de eh (PositiveBT3.lowK t) 1 (PositiveBT3.lowM t)
      hvar hs ha hz he 3
    have hdom : PositiveBT3.SignedDomain (delta C.theta T) (erase de (delta C.theta D)) := by
      simpa [blocks,PositiveBT3.Source.blocks,Block.P,Block.N,PositiveBT3.SignedDomain,
        PositiveBT3.positiveTotal,PositiveBT3.negativeTotal] using hb
    have hcoef : PositiveBT3.tilted (PositiveBT3.lowM t) (delta C.theta B)∈Icc 1 PositiveBT3.Cmax :=
      ⟨hc1,hrot.2⟩
    have hD := PositiveBT3.signed_minorant hcoef hdom
    have hactual := PositiveBT3.Source.sortedD_lower de (hsorted D) (hcontained D) hq hDy hcoef hdom
    simpa [PositiveBT3.LowEnvelope.block,PositiveBT3.Source.sortedBlocks,blocks,
      PositiveBT3.Source.blocks,Block.P,Block.N,PositiveBT3.positiveTotal,PositiveBT3.negativeTotal,t]
      using hD.trans hactual

theorem low_stress_lower {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A))
    (hhg : hg=0∨hg=2) (ht : effective C de eh s∈Icc 0 (1/6:ℝ)) :
    PositiveBT3.Analytic.lowBaseline (PositiveBT3.lowK (effective C de eh s))
      (PositiveBT3.lowM (effective C de eh s)) (delta C.theta B)+gain s+
      TwoPositive.ASupport.charge (eTotal C de eh)+
      (∑i,PositiveBT3.LowEnvelope.block (effective C de eh s) i
        (blocks C hg atG de eh (PositiveBT3.lowK (effective C de eh s)) 1
          (PositiveBT3.lowM (effective C de eh s)) i).P
        (blocks C hg atG de eh (PositiveBT3.lowK (effective C de eh s)) 1
          (PositiveBT3.lowM (effective C de eh s)) i).N)≤
      actualStress C hg atG de eh (PositiveBT3.lowK (effective C de eh s)) 1
        (PositiveBT3.lowM (effective C de eh s)) := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    low_blocks_lower atG de eh hsorted hcontained hq hHy hGy hBy hDy hvar hs ha hz he ht i (hg:=hg))
  have hm : 0≤PositiveBT3.lowM (effective C de eh s) :=
    by linarith [(PositiveBT3.Analytic.low_ranges ht).2.1]
  have hres := reserves_nonnegative atG de eh hsorted hcontained hq hvar hs ha hz he
    (by norm_num : (0:ℝ)≤1) hm hgain (hg:=hg)
  rw [sorted_decomposition C atG de eh hhg _ _ s]
  simp only [one_mul] at hres
  linarith [hres.1,hres.2.1,hres.2.2]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LongE.Source
