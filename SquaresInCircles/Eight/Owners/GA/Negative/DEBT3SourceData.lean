module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2SourceData
public import SquaresInCircles.Eight.Owners.GA.Secant.DSingleData

/-!
# Eight squares: original source stress and both signed budgets for negative DE3 / BT3

Only the actual BT3 argument, the
selected A arguments, and the negative DE3 argument are removed. The
original EH0 argument remains at H and the original TD0 argument remains
as the distinguished D singleton. The E tangent coefficient cancels
only after the true flat-core identity and nonzero original cosine.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks PairedE
open NegativePrimary (erase)

abbrev aTotal := LowA.aTotal
abbrev selectedA := NegativeELargeA.Source.selectedA
abbrev magnitude := NegativeDEPositiveTD.Source.magnitude
abbrev deCorrection := NegativeDEPositiveTD.Source.deCorrection

def total (C : SignedCycle) (ga ab : Bool) : ℝ := aTotal C ga ab+delta C.theta B
def owners (hg ga ab : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,3,0,3,0]
def tilted (m eta z : ℝ) : ℝ := m*(Real.cos z+eta*Real.sin z)
def weights (C : SignedCycle) (k l m eta : ℝ) : Vertex→ℝ :=
  ![k,l,l,m,tilted m eta (delta C.theta B),1/Real.cos (delta C.theta D),1]
def stress (C : SignedCycle) (hg ga ab : Bool) (k l m eta : ℝ) : ℝ :=
  ∑i,weights C k l m eta i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

def blocks (C : SignedCycle) (hg ga ab : Bool) (k l m : ℝ) : Fin 4→Block :=
  ![⟨k,1,erase (!hg) (delta C.theta H),delta C.theta E⟩,
    ⟨k,l,erase hg (delta C.theta H),erase ga (delta C.theta G)⟩,
    ⟨l,m,erase ab (delta C.theta A),0⟩,
    ⟨k,1,delta C.theta T,0⟩]

def actualBlocks (C : SignedCycle) (hg ga ab : Bool) (k l m eta : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 2) (C.point B).reflect,
    SecantD.actualIncrement (1/Real.cos (delta C.theta D))
      (tilted m eta (delta C.theta B)) (delta C.theta T) (C.point D)]

def tReserve (C : SignedCycle) (m eta : ℝ) : ℝ :=
  m*Real.sin (delta C.theta B)*(fullSupport 1 eta-((C.point T).a+eta*(C.point T).y))
def base (C : SignedCycle) (k l m eta : ℝ) : ℝ :=
  k+2*l+m*edgeWidth (delta C.theta B)+tilted m eta (delta C.theta B)+
    1/Real.cos (delta C.theta D)+1-m*fullSupport 1 eta*Real.sin (delta C.theta B)-
    fullSupport 1 k-fullSupport k l-fullSupport l m-
    PositiveBT3.sortedSupport (1/Real.cos (delta C.theta D)) (tilted m eta (delta C.theta B))+
      deCorrection C

theorem decomposition (C : SignedCycle) (hg ga ab : Bool) (k l m eta : ℝ)
    (hflat : (C.point E).a=7/12) (hcos : Real.cos (delta C.theta D)≠0) :
    stress C hg ga ab k l m eta=base C k l m eta+
      (∑i,actualBlocks C hg ga ab k l m eta i)+
      l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+tReserve C m eta := by
  have hsymm : ∀ a b : ℝ,fullSupport a b=fullSupport b a := by
    intro a b
    simp only [fullSupport,add_comm (a^2) (b^2),add_comm a b]
  have hf : (C.point 6).a=7/12 := hflat
  have hinv : (Real.cos (C.theta 6-C.theta 5))⁻¹*Real.cos (C.theta 6-C.theta 5)=1 :=
    inv_mul_cancel₀ hcos
  cases hg <;> cases ga <;> cases ab <;>
    simp [stress,weights,owners,blocks,actualBlocks,base,tReserve,
      deCorrection,NegativeDEPositiveTD.Source.deCorrection,tilted,
      PositiveTD.actualPairIncrement,SecantD.actualIncrement,pairF,pairG,
      primaryGain,erase,hf,SignedCycle.edge,zeroProjection,quarterProjection,
      Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,SignedPoint.reflect,hsymm l k,hsymm m l] <;>
    linear_combination (C.point 6).y*hinv

theorem sum_parts (C : SignedCycle) (hg ga ab : Bool) (k l m : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab k l m i).u+f (blocks C hg ga ab k l m i).v))=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-f (delta C.theta B)-f (delta C.theta D) := by
  cases hg <;> cases ga <;> cases ab <;>
    simp [blocks,erase,selectedA,NegativeELargeA.Source.selectedA,selected,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

structure Budgets (C : SignedCycle) (hg ga ab : Bool) (k l m : ℝ) : Prop where
  total_domain : total C ga ab∈Icc 0 frameCap
  a_domain : aTotal C ga ab∈Icc 0 (total C ga ab)
  bt_domain : delta C.theta B∈Icc 0 (total C ga ab)
  de_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l m i).P)≤frameCap-total C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l m i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l m i).N)-(∑i,(blocks C hg ga ab k l m i).P)=
    total C ga ab-magnitude C

theorem budgets {C : SignedCycle} (hg ga ab : Bool) (k l m : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0) : Budgets C hg ga ab k l m := by
  have hp := sum_parts C hg ga ab k l m positivePart positivePart_zero
  have hn := sum_parts C hg ga ab k l m negativePart negativePart_zero
  have hA := NegativeELargeA.Source.selectedA_signed C ga ab
  have hAP := NegativeELargeA.Source.selectedA_nonnegative C ga ab positivePart positivePart_nonneg
  have hAN := NegativeELargeA.Source.selectedA_nonnegative C ga ab negativePart negativePart_nonneg
  have hzP : positivePart (delta C.theta B)=delta C.theta B := max_eq_left hz
  have hzN : negativePart (delta C.theta B)=0 := max_eq_right (by linarith)
  have hsP : positivePart (delta C.theta D)=0 := max_eq_right hs
  have hsN : negativePart (delta C.theta D)=magnitude C := max_eq_left (neg_nonneg.mpr hs)
  have hP : (∑i,(blocks C hg ga ab k l m i).P)=
      positiveVariation C.theta-selectedA C ga ab positivePart-delta C.theta B := by
    simpa only [Block.P,hzP,hsP,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab k l m i).N)=
      negativeVariation C.theta-selectedA C ga ab negativePart-magnitude C := by
    simpa only [Block.N,hzN,hsN,sub_zero,negativeVariation] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l m i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l m i).N_nonneg)
  have heq := variations_equal C.theta
  have hs0 : 0≤ magnitude C := neg_nonneg.mpr hs
  change selectedA C ga ab positivePart-selectedA C ga ab negativePart=aTotal C ga ab at hA
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [total]; exact ⟨add_nonneg ha hz,by linarith⟩
  · dsimp [total]; exact ⟨ha,by linarith⟩
  · dsimp [total]; exact ⟨hz,by linarith⟩
  · exact ⟨hs0,by linarith⟩
  · dsimp [total]; linarith
  · linarith
  · dsimp [total]; linarith

theorem block_coefficients {C : SignedCycle} (hg ga ab : Bool) {k l m : ℝ}
    (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg ga ab k l m i).p=(![k,k,min l m,k] : Fin 4→ℝ) i ∧
    (blocks C hg ga ab k l m i).q=(![1,l,max l m,1] : Fin 4→ℝ) i := by
  fin_cases i <;> simp [blocks,Block.p,Block.q,min_eq_left hk,max_eq_right hk,
    min_eq_left hl,max_eq_right hl]

theorem block_budgets {C : SignedCycle} (hg ga ab : Bool) (k l m : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta B) (hs : delta C.theta D≤0) (i : Fin 4) :
    (blocks C hg ga ab k l m i).P≤frameCap ∧ (blocks C hg ga ab k l m i).N≤frameCap := by
  have hb := budgets hg ga ab k l m hvar ha hz hs
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l m j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l m j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.total_domain.1],
    by linarith [hb.negative_bound,hb.de_domain.1]⟩

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Source
