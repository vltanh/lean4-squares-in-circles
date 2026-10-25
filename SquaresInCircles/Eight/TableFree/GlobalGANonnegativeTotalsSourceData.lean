module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsScalar
public import SquaresInCircles.Eight.TableFree.GlobalGAPairedECharge
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveSource

/-!
# Original owners and both signed budgets for nonnegative A/E totals

Uncompiled transcription of equations (1)--(4) and (14). Neither A nor
E is assigned a sign on its individual primary errors. Their two flags
retain all original primary ties; only their signed totals are assumed
nonnegative. Angular deletion occurs only in the four analytic blocks.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NegativePrimary (erase)

def aTotal (C : SignedCycle) (ga ab : Bool) : ℝ :=
  PairedE.total ga ab (delta C.theta G) (delta C.theta A)
def eTotal (C : SignedCycle) (de eh : Bool) : ℝ :=
  PairedE.total de eh (delta C.theta D) (delta C.theta E)
def total (C : SignedCycle) (ga ab de eh : Bool) : ℝ :=
  aTotal C ga ab+delta C.theta T+eTotal C de eh

def owners (hg : Fin 4) (ga ab de eh : Bool) : Vertex→Fin 4 :=
  ![hg,if ga then 3 else 2,if ab then 2 else 0,2,2,if de then 3 else 2,if eh then 1 else 0]

def blocks (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (k l c : ℝ) : Fin 4→Block :=
  ![⟨k,1,if hg=0 then 0 else delta C.theta H,erase eh (delta C.theta E)⟩,
    ⟨k,l,if hg=0 then delta C.theta H else 0,erase ga (delta C.theta G)⟩,
    ⟨l,PositiveTD.tilted c (delta C.theta T),erase ab (delta C.theta A),delta C.theta B⟩,
    ⟨k,1,erase de (delta C.theta D),0⟩]

def selectedSum (C : SignedCycle) (ga ab de eh : Bool) (f : ℝ→ℝ) : ℝ :=
  f (PairedE.selected ga (delta C.theta G))+f (PairedE.selected ab (delta C.theta A))+
    f (PairedE.selected de (delta C.theta D))+f (PairedE.selected eh (delta C.theta E))

theorem selected_nonnegative (C : SignedCycle) (ga ab de eh : Bool)
    (f : ℝ→ℝ) (hf : ∀x,0≤f x) : 0≤ selectedSum C ga ab de eh f := by
  dsimp only [selectedSum]
  linarith [hf (PairedE.selected ga (delta C.theta G)),hf (PairedE.selected ab (delta C.theta A)),
    hf (PairedE.selected de (delta C.theta D)),hf (PairedE.selected eh (delta C.theta E))]

theorem selected_signed (C : SignedCycle) (ga ab de eh : Bool) :
    selectedSum C ga ab de eh positivePart-selectedSum C ga ab de eh negativePart=
      aTotal C ga ab+eTotal C de eh := by
  have hG := positive_sub_negative (PairedE.selected ga (delta C.theta G))
  have hA := positive_sub_negative (PairedE.selected ab (delta C.theta A))
  have hD := positive_sub_negative (PairedE.selected de (delta C.theta D))
  have hE := positive_sub_negative (PairedE.selected eh (delta C.theta E))
  dsimp [selectedSum,aTotal,eTotal,PairedE.total]
  linarith

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (k l c : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab de eh k l c i).u+f (blocks C hg ga ab de eh k l c i).v))=
      (∑v,f (delta C.theta v))-f (delta C.theta T)-selectedSum C ga ab de eh f := by
  cases ga <;> cases ab <;> cases de <;> cases eh <;> by_cases hhg : hg=0 <;>
    simp [blocks,erase,selectedSum,PairedE.selected,hhg,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool)
    {k l c : ℝ} (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg ga ab de eh k l c i).p=PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)) i ∧
    (blocks C hg ga ab de eh k l c i).q=PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T)) i := by
  fin_cases i <;> simp [blocks,Block.p,Block.q,PositiveTD.pWeights,PositiveTD.qWeights,
    min_eq_left hk,max_eq_right hk,min_eq_left hl,max_eq_right hl]

theorem budgets {C : SignedCycle} (hg : Fin 4) (ga ab de eh : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (he : 0≤eTotal C de eh) :
    total C ga ab de eh∈Icc 0 frameCap ∧
    aTotal C ga ab∈Icc 0 frameCap ∧ delta C.theta T∈Icc 0 frameCap ∧
    eTotal C de eh∈Icc 0 frameCap ∧
    (∑i,(blocks C hg ga ab de eh k l c i).P)≤frameCap-total C ga ab de eh ∧
    (∑i,(blocks C hg ga ab de eh k l c i).N)=
      total C ga ab de eh+∑i,(blocks C hg ga ab de eh k l c i).P := by
  have hp := sum_parts C hg ga ab de eh k l c positivePart positivePart_zero
  have hn := sum_parts C hg ga ab de eh k l c negativePart negativePart_zero
  have hselected := selected_signed C ga ab de eh
  have hnp := selected_nonnegative C ga ab de eh negativePart negativePart_nonneg
  have hzero : negativePart (delta C.theta T)=0 := max_eq_right (by linarith)
  have hpos : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hP : (∑i,(blocks C hg ga ab de eh k l c i).P)=
      positiveVariation C.theta-delta C.theta T-selectedSum C ga ab de eh positivePart := by
    simpa only [Block.P,hpos,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab de eh k l c i).N)=
      negativeVariation C.theta-selectedSum C ga ab de eh negativePart := by
    simpa only [Block.N,hzero,negativeVariation,sub_zero] using hn
  have hPN : (∑i,(blocks C hg ga ab de eh k l c i).N)=
      total C ga ab de eh+∑i,(blocks C hg ga ab de eh k l c i).P := by
    dsimp [total]
    linarith [variations_equal C.theta]
  have hNcap : (∑i,(blocks C hg ga ab de eh k l c i).N)≤frameCap := by
    linarith [variations_equal C.theta]
  have hP0 : 0≤∑i,(blocks C hg ga ab de eh k l c i).P :=
    Finset.sum_nonneg (fun i _ => (blocks C hg ga ab de eh k l c i).P_nonneg)
  have htotal0 : 0≤total C ga ab de eh := by dsimp [total]; linarith
  have htotalcap : total C ga ab de eh≤frameCap := by linarith
  have hsumcap : aTotal C ga ab+delta C.theta T+eTotal C de eh≤frameCap := htotalcap
  exact ⟨⟨htotal0,htotalcap⟩,⟨ha,by linarith⟩,⟨hz,by linarith⟩,
    ⟨he,by linarith⟩,by linarith,hPN⟩

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (ga ab de eh : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (he : 0≤eTotal C de eh)
    (i : Fin 4) :
    (blocks C hg ga ab de eh k l c i).P≤frameCap ∧
    (blocks C hg ga ab de eh k l c i).N≤frameCap := by
  have hb := budgets hg ga ab de eh k l c hvar ha hz he
  have hP := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab de eh k l c j).P_nonneg) (Finset.mem_univ i)
  have hN := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab de eh k l c j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.1.1,hb.2.2.2.2.1],
    by linarith [hb.2.2.2.2.1,hb.2.2.2.2.2]⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Source
