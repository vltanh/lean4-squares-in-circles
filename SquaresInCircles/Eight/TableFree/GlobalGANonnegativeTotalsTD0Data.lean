module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsTD0Envelope

/-!
# The original four ordinary blocks with arbitrary signed TD0 error

Uncompiled transcription of Section 8. TD0 receives exactly the BT2
weight, so the actual T coordinate cancels. Its error remains in the
D block. Only the selected A and E primary arguments are deleted,
with their signed totals accounted for before concentration.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.TD0
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NegativePrimary (erase)
open NonnegativeTotals.Source (aTotal eTotal selectedSum)

def total (C : SignedCycle) (ga ab de eh : Bool) : ℝ := aTotal C ga ab+eTotal C de eh
def owners (hg : Fin 4) (ga ab de eh : Bool) : Vertex→Fin 4 :=
  ![hg,if ga then 3 else 2,if ab then 2 else 0,2,0,if de then 3 else 2,if eh then 1 else 0]
def weights (k l c : ℝ) : Vertex→ℝ := ![k,l,l,c,c,1,1]

def blocks (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (k l c : ℝ) : Fin 4→Block :=
  ![⟨k,l,if hg=0 then delta C.theta H else 0,erase ga (delta C.theta G)⟩,
    ⟨k,1,if hg=0 then 0 else delta C.theta H,erase eh (delta C.theta E)⟩,
    ⟨l,c,erase ab (delta C.theta A),delta C.theta B⟩,
    ⟨c,1,delta C.theta T,erase de (delta C.theta D)⟩]

def actualBlocks (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (k l c : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l c 0) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l c 1) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l c 2) (C.point B).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l c 3) (C.point D).reflect]

def actualStress (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (k l c : ℝ) : ℝ :=
  demand C (weights k l c)-∑i,work (force C (owners hg ga ab de eh) (weights k l c) i) (C.point i)

private theorem r79_stress_sum (C : SignedCycle) (owner : Vertex → Fin 4) (w : Vertex → ℝ) :
    demand C w-∑ i,work (force C owner w i) (C.point i)=
      ∑ i,w i*(edgeWidth (delta C.theta i)-C.edge i (owner i)) := by
  rw [←sum_force_work,demand,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

private theorem r79_edge_G (C : SignedCycle) (j : Fin 4) :
    C.edge G j=quarterProjection (C.point G) (C.point A) (delta C.theta G) j := by
  simp only [SignedCycle.edge,word,G,A,next]
  rfl

private theorem r79_edge_A (C : SignedCycle) (j : Fin 4) :
    C.edge A j=zeroProjection (C.point A) (C.point B) (delta C.theta A) j := by
  simp only [SignedCycle.edge,word,A,B,next]
  rfl

private theorem r79_edge_D (C : SignedCycle) (j : Fin 4) :
    C.edge D j=quarterProjection (C.point D) (C.point E) (delta C.theta D) j := by
  simp only [SignedCycle.edge,word,D,E,next]
  rfl

private theorem r79_edge_E (C : SignedCycle) (j : Fin 4) :
    C.edge E j=quarterProjection (C.point E) (C.point H) (delta C.theta E) j := by
  simp only [SignedCycle.edge,word,E,H,next]
  rfl

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab de eh : Bool)
    (hhg : hg=0∨hg=2) (k l c : ℝ) :
    actualStress C hg ga ab de eh k l c=PositiveATD0.fullBaseline k l c+
      l*TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh)+
      (∑i,actualBlocks C hg ga ab de eh k l c i)+
      NonnegativeTotals.Source.aReserve C ga ab l+NonnegativeTotals.Source.eReserve C de eh := by
  have h1 : actualStress C hg ga ab de eh k l c=PositiveATD0.Source.actualStress C hg true k l c+
      l*(C.edge G 3-C.edge G (if ga then 3 else 2))+
      l*(C.edge A 0-C.edge A (if ab then 2 else 0))+
      (C.edge D 2-C.edge D (if de then 3 else 2))+
      (C.edge E 0-C.edge E (if eh then 1 else 0)) := by
    rw [actualStress,PositiveATD0.Source.actualStress,r79_stress_sum,r79_stress_sum]
    simp only [Fin.sum_univ_seven,owners,PositiveATD0.Source.owners,weights,
      PositiveATD0.Source.weights,Matrix.cons_val,G,A,D,E,↓reduceIte]
    ring
  have h2 := PositiveATD0.Source.full_decomposition C true hhg k l c
  have hGe : l*(C.edge G 3-C.edge G (if ga then 3 else 2))=
      (actualBlocks C hg ga ab de eh k l c 0-PositiveATD0.Source.actualFullBlocks C hg true k l c 0)+
      l*(if ga then edgeWidth (delta C.theta G)-1-((C.point A).a*Real.sin (delta C.theta G)+
        (C.point A).y*(1-Real.cos (delta C.theta G))) else 0)-
      l*(edgeWidth (delta C.theta G)-1-TwoPositive.Source.aWork C true) := by
    cases ga
    · simp only [actualBlocks,PositiveATD0.Source.actualFullBlocks,blocks,
        PositiveATD0.Source.blocks,Matrix.cons_val,TwoPositive.Source.aWork,
        TwoPositive.Source.aError,r79_edge_G,quarterProjection,PositiveTD.actualPairIncrement,
        pairF,pairG,erase,SignedPoint.reflect,↓reduceIte,Bool.false_eq_true,Real.sin_zero,
        Real.cos_zero,edgeWidth_zero]
      ring
    · simp only [actualBlocks,PositiveATD0.Source.actualFullBlocks,blocks,
        PositiveATD0.Source.blocks,Matrix.cons_val,TwoPositive.Source.aWork,
        TwoPositive.Source.aError,erase,↓reduceIte]
      ring
  have hAe : l*(C.edge A 0-C.edge A (if ab then 2 else 0))=
      (actualBlocks C hg ga ab de eh k l c 2-PositiveATD0.Source.actualFullBlocks C hg true k l c 2)+
      l*(if ab then edgeWidth (delta C.theta A)-1-((C.point A).a*Real.sin (delta C.theta A)+
        (C.point A).y*(Real.cos (delta C.theta A)-1)) else 0) := by
    cases ab
    · simp only [actualBlocks,PositiveATD0.Source.actualFullBlocks,blocks,
        PositiveATD0.Source.blocks,Matrix.cons_val,erase,↓reduceIte,Bool.false_eq_true]
      ring
    · simp only [actualBlocks,PositiveATD0.Source.actualFullBlocks,blocks,
        PositiveATD0.Source.blocks,Matrix.cons_val,r79_edge_A,zeroProjection,
        PositiveTD.actualPairIncrement,pairF,pairG,erase,SignedPoint.reflect,↓reduceIte,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hDe : C.edge D 2-C.edge D (if de then 3 else 2)=
      (actualBlocks C hg ga ab de eh k l c 3-PositiveATD0.Source.actualFullBlocks C hg true k l c 3)+
      (if de then edgeWidth (delta C.theta D)-1-((C.point E).a*Real.sin (delta C.theta D)+
        (C.point E).y*(1-Real.cos (delta C.theta D))) else 0) := by
    cases de
    · simp only [actualBlocks,PositiveATD0.Source.actualFullBlocks,blocks,
        PositiveATD0.Source.blocks,Matrix.cons_val,erase,↓reduceIte,Bool.false_eq_true]
      ring
    · simp only [actualBlocks,PositiveATD0.Source.actualFullBlocks,blocks,
        PositiveATD0.Source.blocks,Matrix.cons_val,r79_edge_D,quarterProjection,
        PositiveTD.actualPairIncrement,pairF,pairG,erase,SignedPoint.reflect,↓reduceIte,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hEe : C.edge E 0-C.edge E (if eh then 1 else 0)=
      (actualBlocks C hg ga ab de eh k l c 1-PositiveATD0.Source.actualFullBlocks C hg true k l c 1)+
      (if eh then edgeWidth (delta C.theta E)-1-((C.point E).a*Real.sin (delta C.theta E)+
        (C.point E).y*(Real.cos (delta C.theta E)-1)) else 0) := by
    cases eh
    · simp only [actualBlocks,PositiveATD0.Source.actualFullBlocks,blocks,
        PositiveATD0.Source.blocks,Matrix.cons_val,erase,↓reduceIte,Bool.false_eq_true]
      ring
    · simp only [actualBlocks,PositiveATD0.Source.actualFullBlocks,blocks,
        PositiveATD0.Source.blocks,Matrix.cons_val,r79_edge_E,quarterProjection,
        PositiveTD.actualPairIncrement,pairF,pairG,erase,↓reduceIte,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  rw [h1,h2]
  simp only [NonnegativeTotals.Source.aReserve,NonnegativeTotals.Source.eReserve,
    TwoPositive.Source.aReserve,TwoPositive.Source.aError,PairedE.primaryGain,Fin.sum_univ_four,
    ↓reduceIte]
  linear_combination hGe+hAe+hDe+hEe

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (k l c : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab de eh k l c i).u+f (blocks C hg ga ab de eh k l c i).v))=
      (∑v,f (delta C.theta v))-selectedSum C ga ab de eh f := by
  cases ga <;> cases ab <;> cases de <;> cases eh <;> by_cases hhg : hg=0 <;>
    simp [blocks,erase,selectedSum,PairedE.selected,hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

theorem budgets {C : SignedCycle} (hg : Fin 4) (ga ab de eh : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh) :
    total C ga ab de eh∈Icc 0 frameCap ∧
    aTotal C ga ab∈Icc 0 frameCap ∧ eTotal C de eh∈Icc 0 frameCap ∧
    (∑i,(blocks C hg ga ab de eh k l c i).P)≤frameCap-total C ga ab de eh ∧
    (∑i,(blocks C hg ga ab de eh k l c i).N)=
      total C ga ab de eh+∑i,(blocks C hg ga ab de eh k l c i).P := by
  have hp := sum_parts C hg ga ab de eh k l c positivePart positivePart_zero
  have hn := sum_parts C hg ga ab de eh k l c negativePart negativePart_zero
  have hselected := NonnegativeTotals.Source.selected_signed C ga ab de eh
  have hnp := NonnegativeTotals.Source.selected_nonnegative C ga ab de eh negativePart negativePart_nonneg
  have hP : (∑i,(blocks C hg ga ab de eh k l c i).P)=
      positiveVariation C.theta-selectedSum C ga ab de eh positivePart := hp
  have hN : (∑i,(blocks C hg ga ab de eh k l c i).N)=
      negativeVariation C.theta-selectedSum C ga ab de eh negativePart := hn
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
  have hsumcap : aTotal C ga ab+eTotal C de eh≤frameCap := htotalcap
  exact ⟨⟨htotal0,htotalcap⟩,⟨ha,by linarith⟩,⟨he,by linarith⟩,by linarith,hPN⟩

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (ga ab de eh : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (i : Fin 4) :
    (blocks C hg ga ab de eh k l c i).P≤frameCap ∧
    (blocks C hg ga ab de eh k l c i).N≤frameCap := by
  have hb := budgets hg ga ab de eh k l c hvar ha he
  have hP := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab de eh k l c j).P_nonneg) (Finset.mem_univ i)
  have hN := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab de eh k l c j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.1.1,hb.2.2.2.1],by linarith [hb.2.2.2.1,hb.2.2.2.2]⟩

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool)
    {k l c : ℝ} (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg ga ab de eh k l c i).p=p k l c i ∧
    (blocks C hg ga ab de eh k l c i).q=q k l c i := by
  fin_cases i <;> simp [blocks,p,q,PositiveATD0.pWeights,PositiveATD0.qWeights,
    Block.p,Block.q,min_eq_left hk,max_eq_right hk,min_eq_left hl,max_eq_right hl,min_comm,max_comm]

theorem full_blocks_lower {Q k l c : ℝ} {C : SignedCycle} {hg : Fin 4}
    (ga ab de eh : Bool) (hc : ∀i,(C.point i).Contained Q) (hq : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hk : k≤1) (hl : k≤l) (hp : ∀i,0<p k l c i) (i : Fin 4) :
    mixedBlock R (p k l c i) (q k l c i)
      (blocks C hg ga ab de eh k l c i).P (blocks C hg ga ab de eh k l c i).N≤
        actualBlocks C hg ga ab de eh k l c i := by
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained Q) :
      mixedBlock R (p k l c j) (q k l c j)
        (blocks C hg ga ab de eh k l c j).P (blocks C hg ga ab de eh k l c j).N≤
          PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l c j) P := by
    have hd := block_coefficients (C:=C) (hg:=hg) (c:=c) ga ab de eh hk hl j
    have hpn : 0≤(blocks C hg ga ab de eh k l c j).p := by rw [hd.1]; exact (hp j).le
    have hb := block_budgets hg ga ab de eh k l c hvar ha he j
    have hh := PositiveTD.actual_block_minorant hy hP hq hpn hb.1 hb.2
    rwa [hd.1,hd.2] at hh
  fin_cases i
  · simpa [actualBlocks] using hordinary 0
      (P:=(C.point G).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hc G)
  · simpa [actualBlocks] using hordinary 1 hHy (hc H)
  · simpa [actualBlocks] using hordinary 2
      (P:=(C.point B).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hc B)
  · simpa [actualBlocks] using hordinary 3
      (P:=(C.point D).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy) (by simpa using hc D)

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool) {k l c : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0≤c)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : actualStress C hg ga ab de eh k l c≤0 := by
  have hw (i : Vertex) : 0≤weights k l c i := by fin_cases i <;> simp [weights] <;> positivity
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation hw hf)

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.TD0
