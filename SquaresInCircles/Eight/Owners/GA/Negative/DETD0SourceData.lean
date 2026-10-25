module

public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3SourceData

/-!
# Eight squares: negative core DE3 with actual BT2 and arbitrary original TD0

Unlike positive-BT3, the BT2 error is not selected and stays in B's
ordinary signed block. The equal B/T weights eliminate T's coordinate
without a radial or tangent assumption. The negative DE3 is selected
and D retains its actual original TD0 error with secant support.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDETD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks PairedE
open NegativePrimary (erase)

abbrev aTotal := NegativeDEPositiveBT.Source.aTotal
abbrev magnitude := NegativeDEPositiveBT.Source.magnitude
abbrev deCorrection := NegativeDEPositiveBT.Source.deCorrection

def owners (hg : Fin 4) (ga ab : Bool) : Vertex→Fin 4 :=
  ![hg,if ga then 3 else 2,if ab then 2 else 0,2,0,3,0]

def weights (C : SignedCycle) (k l m : ℝ) : Vertex→ℝ :=
  ![k,l,l,m,m,1/Real.cos (delta C.theta D),1]

def stress (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l m : ℝ) : ℝ :=
  ∑i,weights C k l m i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

/-- The B block keeps the true BT2 error, and D keeps TD0. -/
def blocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l m : ℝ) : Fin 4→Block :=
  ![⟨k,1,if hg=0 then 0 else delta C.theta H,delta C.theta E⟩,
    ⟨k,l,if hg=0 then delta C.theta H else 0,erase ga (delta C.theta G)⟩,
    ⟨l,m,erase ab (delta C.theta A),delta C.theta B⟩,
    ⟨k,1,delta C.theta T,0⟩]

def actualBlocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l m : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 2) (C.point B).reflect,
    SecantD.actualIncrement (1/Real.cos (delta C.theta D)) m
      (delta C.theta T) (C.point D)]

def base (C : SignedCycle) (k l m : ℝ) : ℝ :=
  k+2*l+2*m+1/Real.cos (delta C.theta D)+1-
    fullSupport 1 k-fullSupport k l-fullSupport l m-
    PositiveBT3.sortedSupport (1/Real.cos (delta C.theta D)) m+
    deCorrection C

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab : Bool)
    (hhg : hg=0∨hg=2) (k l m : ℝ)
    (hflat : (C.point E).a=7/12) (hcos : Real.cos (delta C.theta D)≠0) :
    stress C hg ga ab k l m=base C k l m+
      (∑i,actualBlocks C hg ga ab k l m i)+
      l*PairedE.primaryGain (C.point A) ga ab
        (delta C.theta G) (delta C.theta A) := by
  have hsymm : ∀ a b : ℝ,fullSupport a b=fullSupport b a := by
    intro a b
    simp only [fullSupport,add_comm (a^2) (b^2),add_comm a b]
  have hf : (C.point 6).a=7/12 := hflat
  have hinv : (Real.cos (C.theta 6-C.theta 5))⁻¹*Real.cos (C.theta 6-C.theta 5)=1 :=
    inv_mul_cancel₀ hcos
  cases ga <;> cases ab <;> rcases hhg with rfl|rfl <;>
    simp [stress,weights,owners,blocks,actualBlocks,base,
      deCorrection,NegativeDEPositiveTD.Source.deCorrection,
      PositiveTD.actualPairIncrement,SecantD.actualIncrement,
      pairF,pairG,PairedE.primaryGain,erase,hf,SignedCycle.edge,
      zeroProjection,quarterProjection,Fin.sum_univ_succ,
      word,delta,next,H,G,A,B,T,D,E,SignedPoint.reflect,hsymm l k,hsymm m l] <;>
    linear_combination (C.point 6).y*hinv

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l m : ℝ) (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab k l m i).u+
      f (blocks C hg ga ab k l m i).v))=
    (∑i,f (delta C.theta i))-NegativeELargeA.Source.selectedA C ga ab f-
      f (delta C.theta D) := by
  cases ga <;> cases ab <;> by_cases hhg : hg=0 <;>
    simp [blocks,erase,NegativeELargeA.Source.selectedA,selected,hhg,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

structure Budgets (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l m : ℝ) : Prop where
  a_domain : aTotal C ga ab∈Icc 0 frameCap
  de_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l m i).P)≤frameCap-aTotal C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l m i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l m i).N)-
    (∑i,(blocks C hg ga ab k l m i).P)=aTotal C ga ab-magnitude C

theorem budgets {C : SignedCycle} (hg : Fin 4) (ga ab : Bool) (k l m : ℝ)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta D≤0) :
    Budgets C hg ga ab k l m := by
  have hp := sum_parts C hg ga ab k l m positivePart positivePart_zero
  have hn := sum_parts C hg ga ab k l m negativePart negativePart_zero
  have hA := NegativeELargeA.Source.selectedA_signed C ga ab
  have hAP := NegativeELargeA.Source.selectedA_nonnegative C ga ab
    positivePart positivePart_nonneg
  have hAN := NegativeELargeA.Source.selectedA_nonnegative C ga ab
    negativePart negativePart_nonneg
  have hsP : positivePart (delta C.theta D)=0 := max_eq_right hs
  have hsN : negativePart (delta C.theta D)=magnitude C := max_eq_left (neg_nonneg.mpr hs)
  have hP : (∑i,(blocks C hg ga ab k l m i).P)=
      positiveVariation C.theta-NegativeELargeA.Source.selectedA C ga ab positivePart := by
    simpa only [Block.P,hsP,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab k l m i).N)=
      negativeVariation C.theta-NegativeELargeA.Source.selectedA C ga ab negativePart-
        magnitude C := by
    simpa only [Block.N,hsN,negativeVariation] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l m i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l m i).N_nonneg)
  have heq := variations_equal C.theta
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact ⟨ha,by linarith⟩
  · exact ⟨neg_nonneg.mpr hs,by linarith⟩
  · linarith
  · linarith
  · linarith

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (ga ab : Bool)
    (k l m : ℝ) (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta D≤0) (i : Fin 4) :
    (blocks C hg ga ab k l m i).P≤frameCap ∧
    (blocks C hg ga ab k l m i).N≤frameCap := by
  have hb := budgets hg ga ab k l m hvar ha hs
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l m j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l m j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.a_domain.1],
    by linarith [hb.negative_bound,hb.de_domain.1]⟩

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (ga ab : Bool)
    {k l m : ℝ} (hk : k≤1) (hl : k≤l) (i : Fin 3) :
    (blocks C hg ga ab k l m i.castSucc).p =
      (![k,k,min l m] : Fin 3→ℝ) i ∧
    (blocks C hg ga ab k l m i.castSucc).q =
      (![1,l,max l m] : Fin 3→ℝ) i := by
  fin_cases i <;>
    simp [blocks,Block.p,Block.q,min_eq_left hk,max_eq_right hk,
      min_eq_left hl,max_eq_right hl]

end SquaresInCircles.Eight.GlobalGA.NegativeDETD0
