module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Stress
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3DEnvelope

/-!
# The low-total sorted-D minorant on the original cycle

Uncompiled Sections 2--3. The fourth block contains the original TD0
error and the unselected DE error, with both of their positive and
negative parts. The complete signed sorted-D theorem is applied to
those actual arguments; the other three original full-circle blocks
use the same exact signed budgets.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open NegativePrimary (erase)

def lowBlock (t : ℝ) (i : Fin 4) (P N : ℝ) : ℝ :=
  if i=3 then -slope*P+vstar N
  else mixedBlock R (![lowK t,lowK t,1,lowK t] i) (![1,1,lowM t,1] i) P N

theorem low_blocks_lower {q : ℝ} {C : SignedCycle} {hg : Fin 4}
    (ga ab de eh : Bool) (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hu : 0≤delta C.theta B) (he : 0≤eTotal C de eh)
    (ht : total C ga ab de eh∈Icc 0 (1/6:ℝ)) (i : Fin 4) :
    lowBlock (total C ga ab de eh) i
      (blocks C hg ga ab de eh (lowK (total C ga ab de eh)) 1 (lowM (total C ga ab de eh)) i).P
      (blocks C hg ga ab de eh (lowK (total C ga ab de eh)) 1 (lowM (total C ga ab de eh)) i).N≤
        sortedBlocks C hg ga ab de eh (lowK (total C ga ab de eh)) (lowM (total C ga ab de eh)) i := by
  let t := total C ga ab de eh
  have hr := Analytic.low_ranges ht
  have huT : delta C.theta B∈Icc 0 t := ⟨hu,by dsimp [t,total]; linarith⟩
  have hrot := Analytic.low_tilted_ranges ht huT
  have hk : 0<lowK t := by dsimp [t]; linarith [hr.1.1]
  have hk1 : lowK t≤1 := by dsimp [t,K] at *; linarith [hr.1.2]
  have hm1 : 1≤lowM t := by dsimp [t] at *; linarith [hr.2.1]
  have hc1 : 1≤tilted (lowM t) (delta C.theta B) := hm1.trans hrot.1
  have hp (j : Fin 4) : 0<pWeights (lowK t) 1 (lowM t)
      (tilted (lowM t) (delta C.theta B)) j := by
    fin_cases j <;> simp [pWeights,min_eq_left hm1,min_eq_left hc1] <;> linarith
  have hfull (j : Fin 4) := full_blocks_lower ga ab de eh hc hq hHy hGy hBy hDy
    hvar ha hu he hk1 hk1 hp j (hg:=hg)
  fin_cases i
  · simpa [lowBlock,sortedBlocks,pWeights,qWeights,t] using hfull 0
  · simpa [lowBlock,sortedBlocks,pWeights,qWeights,t] using hfull 1
  · simpa [lowBlock,sortedBlocks,pWeights,qWeights,min_eq_left hm1,max_eq_right hm1,t] using hfull 2
  · have hb := block_budgets hg ga ab de eh (lowK t) 1 (lowM t) hvar ha hu he 3
    have hdom : SignedDomain (delta C.theta T) (erase de (delta C.theta Candidate.D)) := by
      simpa [blocks,Block.P,Block.N,SignedDomain,positiveTotal,negativeTotal] using hb
    have hcoef : tilted (lowM t) (delta C.theta B)∈Icc 1 Cmax := ⟨hc1,hrot.2⟩
    have hD := signed_minorant hcoef hdom
    have hactual := sortedD_lower de (hs Candidate.D) (hc Candidate.D) hq hDy hcoef hdom
    simpa [lowBlock,sortedBlocks,blocks,Block.P,Block.N,positiveTotal,negativeTotal,t] using
      hD.trans hactual

/-- The primary reserves and actual T support are retained before the
two nonnegative A/E charges are merged at their exact signed sum. -/
theorem low_stress_lower {q : ℝ} {C : SignedCycle} {hg : Fin 4}
    (ga ab de eh : Bool) (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hu : 0≤delta C.theta B) (he : 0≤eTotal C de eh)
    (hhg : hg=0∨hg=2) (ht : total C ga ab de eh∈Icc 0 (1/6:ℝ)) :
    Analytic.lowBaseline (lowK (total C ga ab de eh)) (lowM (total C ga ab de eh)) (delta C.theta B)+
      TwoPositive.ASupport.charge (aTotal C ga ab+eTotal C de eh)+
      (∑i,lowBlock (total C ga ab de eh) i
        (blocks C hg ga ab de eh (lowK (total C ga ab de eh)) 1 (lowM (total C ga ab de eh)) i).P
        (blocks C hg ga ab de eh (lowK (total C ga ab de eh)) 1 (lowM (total C ga ab de eh)) i).N)≤
      actualStress C hg ga ab de eh (lowK (total C ga ab de eh)) 1 (lowM (total C ga ab de eh)) := by
  have hb := budgets hg ga ab de eh (lowK (total C ga ab de eh)) 1 (lowM (total C ga ab de eh))
    hvar ha hu he
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    low_blocks_lower ga ab de eh hs hc hq hHy hGy hBy hDy hvar ha hu he ht i (hg:=hg))
  have hprimary := NonnegativeTotals.Source.primary_reserves ga ab de eh hs hc hq
    (original_error_bound hvar hn) (by norm_num : (0:ℝ)≤1) hb.2.1 hb.2.2.2.1
  have hm : 0≤lowM (total C ga ab de eh) := by linarith [(Analytic.low_ranges ht).2.1]
  have hT := tReserve_nonnegative (hs T) (hc T) hq hm hb.2.2.1
  have hcharge := PrimaryCharge.subadditive ha he
    (show aTotal C ga ab+eTotal C de eh≤frameCap by dsimp [total] at hb; linarith [hb.1.2])
  rw [sorted_decomposition C ga ab de eh hhg]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Source
