module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2Scalar
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2SourceData
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDStress

/-!
# The original genuine-EH1 / TD2 stress and four retained blocks

Uncompiled source transcription. The EH multiplier is present in the
actual H-circle block. Its zero-angle support loss appears exactly once
in ehGain. The nominal H block has the same original angle and supplies
only the signed-mass bookkeeping. DE2 is never erased. Only the selected
A arguments, TD, and the actual negative EH argument are removed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks PairedE
open NegativePrimary (erase)

abbrev aTotal := LowA.aTotal
abbrev selectedA := NegativeELargeA.Source.selectedA

def total (C : SignedCycle) (ga ab : Bool) : ℝ := aTotal C ga ab+delta C.theta T
def magnitude (C : SignedCycle) : ℝ := -delta C.theta E

def owners (hg ga ab : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,2,2,2,1]
def weights (C : SignedCycle) (k l c u : ℝ) : Vertex→ℝ :=
  ![k,l,l,PositiveTD.tilted c (delta C.theta T),c,1,u]
def stress (C : SignedCycle) (hg ga ab : Bool) (k l c u : ℝ) : ℝ :=
  ∑i,weights C k l c u i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

/-- Nominal coefficients do not affect either original signed mass. -/
def blocks (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ) : Fin 4→Block :=
  ![⟨k,1,erase (!hg) (delta C.theta H),0⟩,
    ⟨k,l,erase hg (delta C.theta H),erase ga (delta C.theta G)⟩,
    ⟨l,PositiveTD.tilted c (delta C.theta T),erase ab (delta C.theta A),delta C.theta B⟩,
    ⟨k,1,delta C.theta D,0⟩]

def hBlock (C : SignedCycle) (hg : Bool) (k u : ℝ) : Block :=
  ⟨k,u,erase (!hg) (delta C.theta H),0⟩
def actualBlocks (C : SignedCycle) (hg ga ab : Bool) (k l c u : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (hBlock C hg k u) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 2) (C.point B).reflect,
    PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect]

def ehGain (C : SignedCycle) (k u : ℝ) : ℝ :=
  u*edgeWidth (delta C.theta E)-1-u*(C.point E).a*Real.sin (delta C.theta E)+
    (1-u*Real.cos (delta C.theta E))*(C.point E).y-
      (fullSupport u k-fullSupport 1 k)

/-- Every term is evaluated at the unchanged original points and frames. -/
theorem decomposition (C : SignedCycle) (hg ga ab : Bool) (k l c u : ℝ) :
    stress C hg ga ab k l c u=PositiveTD.baseline k l c (delta C.theta T)+
      (∑i,actualBlocks C hg ga ab k l c u i)+
      l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
      PositiveTD.tReserve C c+ehGain C k u := by
  cases hg <;> cases ga <;> cases ab <;>
    simp [stress,weights,owners,blocks,hBlock,actualBlocks,ehGain,
      PositiveTD.baseline,PositiveTD.actualPairIncrement,PositiveTD.actualDIncrement,
      PositiveTD.tReserve,PositiveTD.tilted,pairF,pairG,primaryGain,erase,
      SignedCycle.edge,zeroProjection,quarterProjection,Fin.sum_univ_succ,
      word,delta,next,H,G,A,B,T,D,E,SignedPoint.reflect] <;> ring

theorem sum_parts (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,f (blocks C hg ga ab k l c i).u+f (blocks C hg ga ab k l c i).v)=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-
        f (delta C.theta T)-f (delta C.theta E) := by
  cases hg <;> cases ga <;> cases ab <;>
    simp [blocks,erase,selectedA,NegativeELargeA.Source.selectedA,selected,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

structure Budgets (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ) : Prop where
  total_domain : total C ga ab∈Icc 0 frameCap
  a_domain : aTotal C ga ab∈Icc 0 (total C ga ab)
  td_domain : delta C.theta T∈Icc 0 (total C ga ab)
  eh_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l c i).P)≤frameCap-total C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l c i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l c i).N)-(∑i,(blocks C hg ga ab k l c i).P)=
    total C ga ab-magnitude C

theorem budgets {C : SignedCycle} (hg ga ab : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta T) (hs : delta C.theta E≤0) : Budgets C hg ga ab k l c := by
  have hp := sum_parts C hg ga ab k l c positivePart positivePart_zero
  have hn := sum_parts C hg ga ab k l c negativePart negativePart_zero
  have hA := NegativeELargeA.Source.selectedA_signed C ga ab
  have hAP := NegativeELargeA.Source.selectedA_nonnegative C ga ab positivePart positivePart_nonneg
  have hAN := NegativeELargeA.Source.selectedA_nonnegative C ga ab negativePart negativePart_nonneg
  have hzP : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hzN : negativePart (delta C.theta T)=0 := max_eq_right (by linarith)
  have hsP : positivePart (delta C.theta E)=0 := max_eq_right hs
  have hsN : negativePart (delta C.theta E)=magnitude C := max_eq_left (neg_nonneg.mpr hs)
  have hP : (∑i,(blocks C hg ga ab k l c i).P)=
      positiveVariation C.theta-selectedA C ga ab positivePart-delta C.theta T := by
    simpa only [Block.P,hzP,hsP,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab k l c i).N)=
      negativeVariation C.theta-selectedA C ga ab negativePart-magnitude C := by
    simpa only [Block.N,hzN,hsN,sub_zero,negativeVariation] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l c i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l c i).N_nonneg)
  have heq := variations_equal C.theta
  have hs0 : 0≤magnitude C := neg_nonneg.mpr hs
  change selectedA C ga ab positivePart-selectedA C ga ab negativePart=aTotal C ga ab at hA
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [total]; exact ⟨add_nonneg ha hz,by linarith⟩
  · dsimp [total]; exact ⟨ha,by linarith⟩
  · dsimp [total]; exact ⟨hz,by linarith⟩
  · exact ⟨hs0,by linarith⟩
  · dsimp [total]; linarith
  · linarith
  · dsimp [total]; linarith

theorem block_coefficients {C : SignedCycle} (hg ga ab : Bool) {k l c : ℝ}
    (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg ga ab k l c i).p=(![k,k,min l (PositiveTD.tilted c (delta C.theta T)),k] : Fin 4→ℝ) i ∧
    (blocks C hg ga ab k l c i).q=(![1,l,max l (PositiveTD.tilted c (delta C.theta T)),1] : Fin 4→ℝ) i := by
  fin_cases i <;> simp [blocks,Block.p,Block.q,min_eq_left hk,max_eq_right hk,
    min_eq_left hl,max_eq_right hl]

theorem block_budgets {C : SignedCycle} (hg ga ab : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta T) (hs : delta C.theta E≤0) (i : Fin 4) :
    (blocks C hg ga ab k l c i).P≤frameCap ∧ (blocks C hg ga ab k l c i).N≤frameCap := by
  have hb := budgets hg ga ab k l c hvar ha hz hs
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l c j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l c j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.total_domain.1],
    by linarith [hb.negative_bound,hb.eh_domain.1]⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Source
