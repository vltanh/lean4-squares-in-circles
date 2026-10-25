module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3Data
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2SourceHSupport

/-!
# Original EH1 / BT3 / TD0 stress and signed budgets

Uncompiled Sections 2--3 of the negative-EH / positive-BT3 proof.
The original TD0 and DE2 arguments both remain in D's block. Only
selected A primaries, BT3, and EH1 are removed from the mass ledger.
The EH multiplier changes H's actual support, not its nominal masses.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

abbrev aTotal := PositiveBT3.Source.aTotal

def total (C : SignedCycle) (ga ab : Bool) : ℝ := aTotal C ga ab+delta C.theta B
def magnitude (C : SignedCycle) : ℝ := -delta C.theta E

def owners (hg : Fin 4) (ga ab : Bool) : Vertex→Fin 4 :=
  PositiveBT3.Source.owners hg ga ab false true

def weights (C : SignedCycle) (k l m u : ℝ) : Vertex→ℝ :=
  ![k,l,l,m,PositiveBT3.tilted m (delta C.theta B),1,u]

def stress (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l m u : ℝ) : ℝ :=
  ∑i,weights C k l m u i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

abbrev blocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l m : ℝ) : Fin 4→Block :=
  PositiveBT3.Source.blocks C hg ga ab false true k l m

def hBlock (C : SignedCycle) (hg : Fin 4) (k u : ℝ) : Block :=
  ⟨k,u,if hg=0 then 0 else delta C.theta H,0⟩

def actualBlocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l m u : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (hBlock C hg k u) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 2) (C.point B).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 3) (C.point Candidate.D).reflect]

abbrev ehGain := NegativeEHPositiveTD.Source.ehGain

def selectedA (C : SignedCycle) (ga ab : Bool) (f : ℝ→ℝ) : ℝ :=
  f (PairedE.selected ga (delta C.theta G))+f (PairedE.selected ab (delta C.theta A))

/-- Exact original-point identity, before any support estimate. -/
theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab : Bool)
    (hhg : hg=0∨hg=2) (k l m u : ℝ) :
    stress C hg ga ab k l m u=
      PositiveBT3.Analytic.fullBaseline k l m (delta C.theta B)+
        (∑i,actualBlocks C hg ga ab k l m u i)+
        l*PairedE.primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
        PositiveBT3.Source.tReserve C m+ehGain C k u := by
  cases ga <;> cases ab <;> rcases hhg with rfl|rfl <;>
    simp [stress,weights,owners,PositiveBT3.Source.owners,blocks,
      PositiveBT3.Source.blocks,hBlock,actualBlocks,ehGain,NegativeEHPositiveTD.Source.ehGain,
      PositiveBT3.Analytic.fullBaseline,PositiveBT3.Source.tReserve,PositiveBT3.tilted,
      PositiveTD.actualPairIncrement,pairF,pairG,PairedE.primaryGain,NegativePrimary.erase,
      SignedCycle.edge,zeroProjection,quarterProjection,Fin.sum_univ_succ,
      word,delta,next,H,G,A,B,T,Candidate.D,E,SignedPoint.reflect,edgeWidth,pairWidth] <;> ring

theorem selectedA_nonnegative (C : SignedCycle) (ga ab : Bool)
    (f : ℝ→ℝ) (hf : ∀x,0≤f x) : 0≤ selectedA C ga ab f := by
  exact add_nonneg (hf _) (hf _)

theorem selectedA_signed (C : SignedCycle) (ga ab : Bool) :
    selectedA C ga ab positivePart-selectedA C ga ab negativePart=aTotal C ga ab := by
  have hG := positive_sub_negative (PairedE.selected ga (delta C.theta G))
  have hA := positive_sub_negative (PairedE.selected ab (delta C.theta A))
  dsimp [selectedA,aTotal,PositiveBT3.Source.aTotal,PairedE.total]
  linarith

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l m : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab k l m i).u+f (blocks C hg ga ab k l m i).v))=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-
        f (delta C.theta B)-f (delta C.theta E) := by
  have hh := PositiveBT3.Source.sum_parts C hg ga ab false true k l m f hf
  have e : PositiveBT3.Source.selectedSum C ga ab false true f=
      selectedA C ga ab f+f (delta C.theta E) := by
    simp only [PositiveBT3.Source.selectedSum,selectedA,PairedE.selected,Bool.false_eq_true,
      ↓reduceIte,hf,add_zero]
  rw [e] at hh
  calc _=_ := hh
    _=_ := by ring

structure Budgets (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l m : ℝ) : Prop where
  total_domain : total C ga ab∈Icc 0 frameCap
  a_domain : aTotal C ga ab∈Icc 0 (total C ga ab)
  bt_domain : delta C.theta B∈Icc 0 (total C ga ab)
  eh_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l m i).P)≤frameCap-total C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l m i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l m i).N)-(∑i,(blocks C hg ga ab k l m i).P)=
    total C ga ab-magnitude C

/-- Signed A constituents are not separately required to be nonnegative. -/
theorem budgets {C : SignedCycle} (hg : Fin 4) (ga ab : Bool) (k l m : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0) : Budgets C hg ga ab k l m := by
  have hp := sum_parts C hg ga ab k l m positivePart positivePart_zero
  have hn := sum_parts C hg ga ab k l m negativePart negativePart_zero
  have hA := selectedA_signed C ga ab
  have hAP := selectedA_nonnegative C ga ab positivePart positivePart_nonneg
  have hAN := selectedA_nonnegative C ga ab negativePart negativePart_nonneg
  have hzP : positivePart (delta C.theta B)=delta C.theta B := max_eq_left hz
  have hzN : negativePart (delta C.theta B)=0 := max_eq_right (by linarith)
  have hsP : positivePart (delta C.theta E)=0 := max_eq_right hs
  have hsN : negativePart (delta C.theta E)=magnitude C := max_eq_left (neg_nonneg.mpr hs)
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
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [total]; exact ⟨add_nonneg ha hz,by linarith⟩
  · dsimp [total]; exact ⟨ha,by linarith⟩
  · dsimp [total]; exact ⟨hz,by linarith⟩
  · exact ⟨hs0,by linarith⟩
  · dsimp [total]; linarith
  · linarith
  · dsimp [total]; linarith

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (ga ab : Bool) (k l m : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0) (i : Fin 4) :
    (blocks C hg ga ab k l m i).P≤frameCap ∧ (blocks C hg ga ab k l m i).N≤frameCap := by
  have hb := budgets hg ga ab k l m hvar ha hz hs
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l m j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l m j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.total_domain.1],
    by linarith [hb.negative_bound,hb.eh_domain.1]⟩

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (ga ab : Bool)
    {k l m : ℝ} (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg ga ab k l m i).p=
      PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i ∧
    (blocks C hg ga ab k l m i).q=
      PositiveBT3.qWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i :=
  PositiveBT3.Source.block_coefficients ga ab false true hk hl i

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
