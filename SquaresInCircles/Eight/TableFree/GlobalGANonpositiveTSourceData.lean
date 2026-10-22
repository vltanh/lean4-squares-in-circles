module

public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTAlignedGain

/-!
# The original aligned-T owners and signed variation budgets

Uncompiled Sections 6--7 of the paired nonpositive-T note. Both actual
T primary arguments are deleted in the analytic blocks. The true TD
alignment is retained as an equation, and the remaining B transverse
coefficient is the unrotated c. No physical error is replaced in the cycle.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativePrimary (erase)
open NonnegativeTotals.Source (aTotal eTotal selectedSum)

def owners (hg : Fin 4) (ga ab de eh : Bool) : Vertex→Fin 4 :=
  ![hg,if ga then 3 else 2,if ab then 2 else 0,3,2,if de then 3 else 2,if eh then 1 else 0]

def total (C : SignedCycle) (ga ab de eh : Bool) : ℝ := aTotal C ga ab+eTotal C de eh

def weights (C : SignedCycle) (ε : ℝ) : Vertex→ℝ :=
  ![k ε,l ε,l ε,c,c,1,1]

def blocks (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ) : Fin 4→Block :=
  ![⟨k ε,1,if hg=0 then 0 else delta C.theta H,erase eh (delta C.theta E)⟩,
    ⟨k ε,l ε,if hg=0 then delta C.theta H else 0,erase ga (delta C.theta G)⟩,
    ⟨l ε,c,erase ab (delta C.theta A),0⟩,
    ⟨k ε,1,erase de (delta C.theta D),0⟩]

def actualBlocks (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab de eh ε 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh ε 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh ε 2) (C.point B).reflect,
    PositiveTD.actualDIncrement c (erase de (delta C.theta D)) (C.point D).reflect]

def actualStress (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ) : ℝ :=
  demand C (weights C ε)-∑i,work (force C (owners hg ga ab de eh) (weights C ε) i) (C.point i)

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab de eh : Bool)
    (hhg : hg=0∨hg=2) {s ε : ℝ} (hb : delta C.theta B=-s)
    (hd : delta C.theta T=0) :
    actualStress C hg ga ab de eh ε=base ε+
      l ε*TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh)+
      (∑i,actualBlocks C hg ga ab de eh ε i)+c*PairedA.work (C.point T) (-s) 0+
      NonnegativeTotals.Source.aReserve C ga ab (l ε)+NonnegativeTotals.Source.eReserve C de eh := by
  have hB : C.theta T-C.theta B=-s := by simpa [delta,B,T,next] using hb
  have hD : C.theta D-C.theta T=0 := by simpa [delta,T,D,next] using hd
  cases ga <;> cases ab <;> cases de <;> cases eh <;> rcases hhg with rfl|rfl <;>
    simp [actualStress,demand,force,source,target,work,add,scale,previous,
      owners,weights,blocks,actualBlocks,base,NonnegativeTotals.NegativeTD.base,
      PositiveTD.actualPairIncrement,PositiveTD.actualDIncrement,pairF,pairG,
      NonnegativeTotals.Source.aReserve,NonnegativeTotals.Source.eReserve,
      aTotal,eTotal,PairedE.total,PairedE.selected,PairedE.primaryGain,
      PairedA.work,erase,Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,
      SignedPoint.reflect,edgeWidth,pairWidth,clippedSupport,diagonalSupport,c,
      NonnegativeTotals.NegativeTD.c,hB,hD] <;> ring

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,f (blocks C hg ga ab de eh ε i).u+f (blocks C hg ga ab de eh ε i).v)=
      (∑v,f (delta C.theta v))-f (delta C.theta B)-f (delta C.theta T)-selectedSum C ga ab de eh f := by
  cases ga <;> cases ab <;> cases de <;> cases eh <;> by_cases hhg : hg=0 <;>
    simp [blocks,erase,selectedSum,PairedE.selected,hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

theorem budgets {C : SignedCycle} (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ) {s : ℝ}
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hs : s∈Icc 0 frameCap) (hd : delta C.theta B=-s) (hTD : delta C.theta T=0) :
    total C ga ab de eh∈Icc 0 frameCap ∧
    aTotal C ga ab∈Icc 0 frameCap ∧ eTotal C de eh∈Icc 0 frameCap ∧
    (∑i,(blocks C hg ga ab de eh ε i).P)≤frameCap-total C ga ab de eh ∧
    (∑i,(blocks C hg ga ab de eh ε i).N)≤frameCap-s ∧
    (∑i,(blocks C hg ga ab de eh ε i).N)=total C ga ab de eh-s+
      ∑i,(blocks C hg ga ab de eh ε i).P := by
  have hp := sum_parts C hg ga ab de eh ε positivePart positivePart_zero
  have hn := sum_parts C hg ga ab de eh ε negativePart negativePart_zero
  have hselected := NonnegativeTotals.Source.selected_signed C ga ab de eh
  have hnp := NonnegativeTotals.Source.selected_nonnegative C ga ab de eh negativePart negativePart_nonneg
  have hzero : positivePart (delta C.theta B)=0 := by
    rw [hd]
    exact max_eq_right (neg_nonpos.mpr hs.1)
  have hneg : negativePart (delta C.theta B)=s := by
    rw [hd]
    change max (-(-s)) 0=s
    rw [neg_neg,max_eq_left hs.1]
  have hP : (∑i,(blocks C hg ga ab de eh ε i).P)=
      positiveVariation C.theta-selectedSum C ga ab de eh positivePart := by
    simpa only [Block.P,hzero,hTD,positivePart_zero,positiveVariation,sub_zero] using hp
  have hN : (∑i,(blocks C hg ga ab de eh ε i).N)=
      negativeVariation C.theta-s-selectedSum C ga ab de eh negativePart := by
    simpa only [Block.N,hneg,hTD,negativePart_zero,negativeVariation,sub_zero] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab de eh ε i).P_nonneg)
  have ht : total C ga ab de eh≤frameCap := by
    dsimp [total]
    linarith
  have ht0 : 0≤total C ga ab de eh := by dsimp [total]; linarith
  have ht' : aTotal C ga ab+eTotal C de eh≤frameCap := ht
  refine ⟨⟨ht0,ht⟩,⟨ha,by linarith⟩,⟨he,by linarith⟩,?_,?_,?_⟩
  · dsimp [total]
    linarith
  · linarith [variations_equal C.theta]
  · dsimp [total]
    linarith [variations_equal C.theta]

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ) {s : ℝ}
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hs : s∈Icc 0 frameCap) (hd : delta C.theta B=-s) (hTD : delta C.theta T=0) (i : Fin 4) :
    (blocks C hg ga ab de eh ε i).P≤frameCap ∧ (blocks C hg ga ab de eh ε i).N≤frameCap := by
  have hb := budgets hg ga ab de eh ε hvar ha he hs hd hTD
  have hP := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab de eh ε j).P_nonneg) (Finset.mem_univ i)
  have hN := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab de eh ε j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.1.1,hb.2.2.2.1],by linarith [hb.2.2.2.2.1,hs.1]⟩

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool) {ε : ℝ}
    (hε : ε∈Icc 0 frameCap) (i : Fin 4) :
    (blocks C hg ga ab de eh ε i).p=p ε i ∧ (blocks C hg ga ab de eh ε i).q=q ε i := by
  have hr := ranges hε
  have hk : k ε≤1 := by linarith [hr.2.1]
  have hl : k ε≤l ε := hr.2.2.2.2.1.le
  have hc : l ε≤c := hr.2.2.2.2.2.1.le
  fin_cases i <;> simp [blocks,Block.p,Block.q,p,q,NonnegativeTotals.NegativeTD.p,NonnegativeTotals.NegativeTD.q,
    min_eq_left hk,max_eq_right hk,min_eq_left hl,max_eq_right hl,min_eq_left hc,max_eq_right hc]

end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired.Source
