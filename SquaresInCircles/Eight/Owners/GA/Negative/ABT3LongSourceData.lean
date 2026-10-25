module

public import SquaresInCircles.Eight.Owners.GA.Negative.ALongESourceData
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Stress

/-!
# Eight squares: original signed budgets for a negative A primary and positive BT3

The original BT error and single negative A
argument are deleted only from the analytic ordinary blocks. Both
signed E errors are kept until their exact selected total is formed.
Their positive and negative parts give the two original variation
budgets and the enlarged nonnegative remaining total.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

abbrev aError := NegativeAPositiveTD.Source.aError
abbrev eTotal := PairedE.cycleTotal
def effective (C : SignedCycle) (de eh : Bool) (s : ℝ) : ℝ :=
  delta C.theta B+eTotal C de eh-s
def blocks (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ) : Fin 4 → Block :=
  PositiveBT3.Source.blocks C hg atG (!atG) de eh k l c
def actualBlocks (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ) : Fin 4 → ℝ :=
  PositiveBT3.Source.actualBlocks C hg atG (!atG) de eh k l c
def actualStress (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ) : ℝ :=
  PositiveBT3.Source.actualStress C hg atG (!atG) de eh k l c
def eParts (C : SignedCycle) (de eh : Bool) (f : ℝ → ℝ) : ℝ :=
  f (PairedE.selected de (delta C.theta D))+f (PairedE.selected eh (delta C.theta E))

theorem eParts_nonnegative (C : SignedCycle) (de eh : Bool) (f : ℝ → ℝ)
    (hf : ∀u,0≤f u) : 0≤eParts C de eh f := by
  exact add_nonneg (hf _) (hf _)

theorem eParts_signed (C : SignedCycle) (de eh : Bool) :
    eParts C de eh positivePart-eParts C de eh negativePart=eTotal C de eh := by
  have hD := positive_sub_negative (PairedE.selected de (delta C.theta D))
  have hE := positive_sub_negative (PairedE.selected eh (delta C.theta E))
  dsimp [eParts,eTotal,PairedE.cycleTotal,PairedE.total]
  linarith

theorem selected_parts {C : SignedCycle} {s : ℝ} (atG de eh : Bool)
    (ha : aError C atG= -s) (f : ℝ → ℝ) (hf : f 0=0) :
    PositiveBT3.Source.selectedSum C atG (!atG) de eh f=f (-s)+eParts C de eh f := by
  cases atG <;>
    simp only [aError,NegativeAPositiveTD.Source.aError,Bool.false_eq_true,ite_false,ite_true] at ha <;>
    simp [PositiveBT3.Source.selectedSum,PairedE.selected,eParts,ha,hf,add_assoc]

theorem block_parts {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool)
    (k l c : ℝ) (ha : aError C atG= -s) (f : ℝ → ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg atG de eh k l c i).u+f (blocks C hg atG de eh k l c i).v))=
      (∑v,f (delta C.theta v))-f (delta C.theta B)-f (-s)-eParts C de eh f := by
  have hh := PositiveBT3.Source.sum_parts C hg atG (!atG) de eh k l c f hf
  rw [selected_parts atG de eh ha f hf] at hh
  dsimp [blocks]
  linarith

structure Budget (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c s : ℝ) : Prop where
  bt_domain : delta C.theta B∈Icc 0 frameCap
  e_domain : eTotal C de eh∈Icc 0 frameCap
  total_upper : delta C.theta B+eTotal C de eh≤frameCap
  residual_domain : effective C de eh s∈Icc 0 frameCap
  positive_original : (∑i,(blocks C hg atG de eh k l c i).P)≤frameCap-delta C.theta B-eTotal C de eh
  positive_bound : (∑i,(blocks C hg atG de eh k l c i).P)≤frameCap-effective C de eh s
  negative_original : (∑i,(blocks C hg atG de eh k l c i).N)≤frameCap-s
  negative_bound : (∑i,(blocks C hg atG de eh k l c i).N)≤frameCap
  balance : (∑i,(blocks C hg atG de eh k l c i).N)=
    effective C de eh s+∑i,(blocks C hg atG de eh k l c i).P

theorem budgets {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (hs : 0≤ s) (ha : aError C atG= -s)
    (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh) :
    Budget C hg atG de eh k l c s := by
  have hp := block_parts hg atG de eh k l c ha positivePart positivePart_zero
  have hn := block_parts hg atG de eh k l c ha negativePart negativePart_zero
  have hpz : positivePart (delta C.theta B)=delta C.theta B := max_eq_left hz
  have hnz : negativePart (delta C.theta B)=0 := max_eq_right (by linarith)
  have hps : positivePart (-s)=0 := max_eq_right (by linarith)
  have hns : negativePart (-s)=s := by simp [negativePart,hs]
  have hP : (∑i,(blocks C hg atG de eh k l c i).P)=
      positiveVariation C.theta-delta C.theta B-eParts C de eh positivePart := by
    simpa only [Block.P,hpz,hps,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg atG de eh k l c i).N)=
      negativeVariation C.theta-s-eParts C de eh negativePart := by
    simpa only [Block.N,hnz,hns,sub_zero,negativeVariation] using hn
  have heq := eParts_signed C de eh
  have hEneg := eParts_nonnegative C de eh negativePart negativePart_nonneg
  have hP0 : 0≤∑i,(blocks C hg atG de eh k l c i).P :=
    Finset.sum_nonneg (fun i _ => (blocks C hg atG de eh k l c i).P_nonneg)
  have hN0 : 0≤∑i,(blocks C hg atG de eh k l c i).N :=
    Finset.sum_nonneg (fun i _ => (blocks C hg atG de eh k l c i).N_nonneg)
  have hPcap : (∑i,(blocks C hg atG de eh k l c i).P)≤frameCap-delta C.theta B-eTotal C de eh := by
    linarith
  have hNcap : (∑i,(blocks C hg atG de eh k l c i).N)≤frameCap-s := by
    linarith [variations_equal C.theta]
  have hbalance : (∑i,(blocks C hg atG de eh k l c i).N)=
      effective C de eh s+∑i,(blocks C hg atG de eh k l c i).P := by
    dsimp [effective]
    linarith [variations_equal C.theta]
  have htotal : delta C.theta B+eTotal C de eh≤frameCap := by linarith
  refine ⟨⟨hz,by linarith⟩,⟨by linarith,by linarith⟩,htotal,
    ?_,hPcap,?_,hNcap,by linarith,hbalance⟩
  · dsimp [effective]; constructor <;> linarith
  · dsimp [effective]; linarith

theorem block_budgets {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (hs : 0≤ s) (ha : aError C atG= -s)
    (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh) (i : Fin 4) :
    (blocks C hg atG de eh k l c i).P≤frameCap ∧ (blocks C hg atG de eh k l c i).N≤frameCap := by
  have hb := budgets hg atG de eh k l c hvar hs ha hz he
  have hP := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG de eh k l c j).P_nonneg) (Finset.mem_univ i)
  have hN := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG de eh k l c j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.residual_domain.1],hN.trans hb.negative_bound⟩

abbrev gain_lower := @NegativeA.LongE.Source.gain_lower

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE.Source
