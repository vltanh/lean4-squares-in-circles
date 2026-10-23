module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3SourceCoefficients
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsTD0Data

/-!
# Genuine negative EH1 and the original BT2 / TD0 four circles

The two BT2/TD0 angles have not been suppressed: BT remains in B's
two-angle block and TD remains in D's two-angle block. Only the
designated A primaries and negative EH1 are deleted. The original
E multiplier enters H, preserving the actual EH support correction.
All statements concern one unchanged SignedCycle and one radius.
Uncompiled transcription of Sections 1–3 of the genuine EH1/TD0 note.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHTD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks NegativePrimary (erase)

abbrev aTotal := NegativeEHBT3.Source.aTotal
abbrev magnitude := NegativeEHBT3.Source.magnitude
abbrev selectedA := NegativeEHBT3.Source.selectedA

def owners (hg : Fin 4) (ga ab : Bool) : Vertex→Fin 4 :=
  NonnegativeTotals.TD0.owners hg ga ab false true

def weights (k l c w : ℝ) : Vertex→ℝ := ![k,l,l,c,c,1,w]

def stress (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l c w : ℝ) : ℝ :=
  ∑i,weights k l c w i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

/-- H, G, B and D order matches the four pairs in the scalar certificate.
In particular D uses original (delta TD,delta DE), not a virtual TD2. -/
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

/-- Exact force sum. Both T/B multipliers equal c, so the T support
cancels and no assumption on T's tangent or radial kind is used. -/
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

/-- Every original unselected signed argument appears exactly once. -/
theorem sum_parts (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l c : ℝ) (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,f (blocks C hg ga ab k l c i).u+
      f (blocks C hg ga ab k l c i).v)=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-
        f (delta C.theta E) := by
  have hh := NonnegativeTotals.TD0.sum_parts C hg ga ab false true k l c f hf
  simp only [NonnegativeTotals.Source.selectedSum,PairedE.selected,
    if_false,if_true,hf,zero_add,add_zero] at hh
  simp only [blocks,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.reduceFinMk,Fin.sum_univ_zero,add_zero]
  dsimp [selectedA,NegativeEHBT3.Source.selectedA] at *
  linarith only [hh]

structure Budgets (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l c : ℝ) : Prop where
  a_domain : aTotal C ga ab∈Icc 0 frameCap
  eh_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l c i).P)≤frameCap-aTotal C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l c i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l c i).N)-
    (∑i,(blocks C hg ga ab k l c i).P)=aTotal C ga ab-magnitude C

/-- Two true sign budgets, including opposite signs of GA and AB. -/
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

/-- The B and D pairs have their own original signed errors. -/
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHTD0
