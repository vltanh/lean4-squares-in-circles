module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3SourceData
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsTD0Data

/-!
# Eight squares: negative EH1 and the four circles with BT2 and TD0

The two BT2 and TD0 angles stay: BT in the two-angle block of B and TD in the two-angle block of D
(`blocks`). Only the selected A primaries and the negative EH1 are deleted. The E multiplier enters
H and keeps the EH support correction. All statements concern one `SignedCycle` and one radius.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalGA.NegativeEHTD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NegativePrimary (erase)

abbrev aTotal := NegativeEHBT3.Source.aTotal
abbrev magnitude := NegativeEHBT3.Source.magnitude
abbrev selectedA := NegativeEHBT3.Source.selectedA

def owners (hg : Fin 4) (ga ab : Bool) : Vertex→Fin 4 :=
  NonnegativeTotals.TD0.owners hg ga ab false true

def weights (k l c w : ℝ) : Vertex→ℝ := ![k,l,l,c,c,1,w]

def stress (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l c w : ℝ) : ℝ :=
  ∑i,weights k l c w i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

/-- The order H, G, B, D matches the four pairs of the scalar certificate. In particular D uses the
angles `(delta TD, delta DE)` of the cycle, not those of a TD2. -/
def blocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l c : ℝ) : Fin 4→Block :=
  ![NonnegativeTotals.TD0.blocks C hg ga ab false true k l c 1,
    NonnegativeTotals.TD0.blocks C hg ga ab false true k l c 0,
    NonnegativeTotals.TD0.blocks C hg ga ab false true k l c 2,
    NonnegativeTotals.TD0.blocks C hg ga ab false true k l c 3]

def hBlock (C : SignedCycle) (hg : Fin 4) (k w : ℝ) : Block :=
  ⟨k,w,if hg=0 then 0 else delta C.theta H,0⟩

def actualBlocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l c w : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (hBlock C hg k w) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 2) (C.point B).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 3) (C.point D).reflect]

/-- The force sum. Both multipliers of T and B equal `c`, so the T support cancels and no
assumption on the tangent or the radial kind of T is used. -/
theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab : Bool)
    (hhg : hg=0∨hg=2) (k l c w : ℝ) :
    stress C hg ga ab k l c w =
      PositiveATD0.fullBaseline k l c+
        (∑i,actualBlocks C hg ga ab k l c w i)+
        l*PairedE.primaryGain (C.point A) ga ab
          (delta C.theta G) (delta C.theta A)+
        NegativeEHPositiveTD.Source.ehGain C k w := by
  cases ga <;> cases ab <;> rcases hhg with rfl|rfl <;>
    simp [stress,weights,owners,NonnegativeTotals.TD0.owners,
      blocks,NonnegativeTotals.TD0.blocks,hBlock,actualBlocks,
      PositiveATD0.fullBaseline,PositiveTD.actualPairIncrement,
      NegativeEHPositiveTD.Source.ehGain,PairedE.primaryGain,
      pairF,pairG,erase,SignedCycle.edge,zeroProjection,quarterProjection,
      Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,
      SignedPoint.reflect,edgeWidth,pairWidth] <;> ring

/-- Every unselected signed argument of the cycle appears exactly once. -/
theorem sum_parts (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l c : ℝ) (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab k l c i).u+
      f (blocks C hg ga ab k l c i).v))=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-
        f (delta C.theta E) := by
  have hh := NonnegativeTotals.TD0.sum_parts C hg ga ab false true k l c f hf
  have hperm : (∑i,(f (blocks C hg ga ab k l c i).u+f (blocks C hg ga ab k l c i).v))=
      ∑i,(f (NonnegativeTotals.TD0.blocks C hg ga ab false true k l c i).u+
        f (NonnegativeTotals.TD0.blocks C hg ga ab false true k l c i).v) := by
    simp only [blocks,Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.head_cons]
    ring
  rw [hperm,hh]
  simp only [NonnegativeTotals.Source.selectedSum,selectedA,NegativeEHBT3.Source.selectedA,
    PairedE.selected,Bool.false_eq_true,↓reduceIte,hf]
  ring

structure Budgets (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l c : ℝ) : Prop where
  a_domain : aTotal C ga ab∈Icc 0 frameCap
  eh_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l c i).P)≤frameCap-aTotal C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l c i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l c i).N)-
    (∑i,(blocks C hg ga ab k l c i).P)=aTotal C ga ab-magnitude C

/-- The two sign budgets, opposite signs of GA and AB included. -/
theorem budgets {C : SignedCycle} (hg : Fin 4) (ga ab : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta E≤0) :
    Budgets C hg ga ab k l c := by
  have hp := sum_parts C hg ga ab k l c positivePart positivePart_zero
  have hn := sum_parts C hg ga ab k l c negativePart negativePart_zero
  have hA := NegativeEHBT3.Source.selectedA_signed C ga ab
  have hAP := NegativeEHBT3.Source.selectedA_nonnegative C ga ab
    positivePart positivePart_nonneg
  have hAN := NegativeEHBT3.Source.selectedA_nonnegative C ga ab
    negativePart negativePart_nonneg
  have hsP : positivePart (delta C.theta E)=0 := max_eq_right hs
  have hsN : negativePart (delta C.theta E)=magnitude C := max_eq_left (neg_nonneg.mpr hs)
  have hP : (∑i,(blocks C hg ga ab k l c i).P)=
      positiveVariation C.theta-selectedA C ga ab positivePart := by
    simpa only [Block.P,hsP,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab k l c i).N)=
      negativeVariation C.theta-selectedA C ga ab negativePart-magnitude C := by
    simpa only [Block.N,hsN,negativeVariation] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l c i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l c i).N_nonneg)
  have heq := variations_equal C.theta
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact ⟨ha,by linarith⟩
  · exact ⟨neg_nonneg.mpr hs,by linarith⟩
  · linarith
  · linarith
  · linarith

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (ga ab : Bool)
    (k l c : ℝ) (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta E≤0)
    (i : Fin 4) :
    (blocks C hg ga ab k l c i).P≤frameCap ∧
    (blocks C hg ga ab k l c i).N≤frameCap := by
  have hb := budgets hg ga ab k l c hvar ha hs
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l c j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l c j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.a_domain.1],
    by linarith [hb.negative_bound,hb.eh_domain.1]⟩

/-- The B and D pairs keep their own signed errors. -/
theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (ga ab : Bool)
    {k l c : ℝ} (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg ga ab k l c i).p=
      PositiveBT3.pWeights k l c c i ∧
    (blocks C hg ga ab k l c i).q=
      PositiveBT3.qWeights k l c c i := by
  fin_cases i <;>
    simp [blocks,NonnegativeTotals.TD0.blocks,Block.p,Block.q,
      PositiveBT3.pWeights,PositiveBT3.qWeights,
      min_eq_left hk,max_eq_right hk,min_eq_left hl,max_eq_right hl,
      min_comm,max_comm]

end SquaresInCircles.Eight.GlobalGA.NegativeEHTD0
