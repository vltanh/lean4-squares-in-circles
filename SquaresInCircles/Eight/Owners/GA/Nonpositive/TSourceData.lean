module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsStress
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TPairedBounds

/-!
# Eight squares: the aligned-T owners and the signed variation budgets

Both T primary arguments are deleted in the analytic blocks. The TD alignment is kept as an
equation, and the remaining transverse coefficient of B is the unrotated `c` (`block_coefficients`).
No error of the cycle changes.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativePrimary (erase)
open NonnegativeTotals.Source (aTotal eTotal selectedSum)

def owners (hg : Fin 4) (ga ab de eh : Bool) : Vertex→Fin 4 :=
  ![hg,if ga then 3 else 2,if ab then 2 else 0,3,2,if de then 3 else 2,if eh then 1 else 0]

def total (C : SignedCycle) (ga ab de eh : Bool) : ℝ := aTotal C ga ab+eTotal C de eh

def weights (_C : SignedCycle) (ε : ℝ) : Vertex→ℝ :=
  ![k ε,l ε,l ε,c,c,1,1]

def blocks (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ) : Fin 4→ActualOrdinaryBlocks.Block :=
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

private theorem r92sd_edge_zero (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i=0) :
    C.edge i j=zeroProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92sd_edge_quarter (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i≠0) :
    C.edge i j=quarterProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92sd_e0 (C : SignedCycle) (j : Fin 4) :
    C.edge 0 j=zeroProjection (C.point 0) (C.point 1) (delta C.theta 0) j :=
  r92sd_edge_zero C 0 j (by decide)
private theorem r92sd_e1 (C : SignedCycle) (j : Fin 4) :
    C.edge 1 j=quarterProjection (C.point 1) (C.point 2) (delta C.theta 1) j :=
  r92sd_edge_quarter C 1 j (by decide)
private theorem r92sd_e2 (C : SignedCycle) (j : Fin 4) :
    C.edge 2 j=zeroProjection (C.point 2) (C.point 3) (delta C.theta 2) j :=
  r92sd_edge_zero C 2 j (by decide)
private theorem r92sd_e3 (C : SignedCycle) (j : Fin 4) :
    C.edge 3 j=quarterProjection (C.point 3) (C.point 4) (delta C.theta 3) j :=
  r92sd_edge_quarter C 3 j (by decide)
private theorem r92sd_e4 (C : SignedCycle) (j : Fin 4) :
    C.edge 4 j=zeroProjection (C.point 4) (C.point 5) (delta C.theta 4) j :=
  r92sd_edge_zero C 4 j (by decide)
private theorem r92sd_e5 (C : SignedCycle) (j : Fin 4) :
    C.edge 5 j=quarterProjection (C.point 5) (C.point 6) (delta C.theta 5) j :=
  r92sd_edge_quarter C 5 j (by decide)
private theorem r92sd_e6 (C : SignedCycle) (j : Fin 4) :
    C.edge 6 j=quarterProjection (C.point 6) (C.point 0) (delta C.theta 6) j :=
  r92sd_edge_quarter C 6 j (by decide)

private def r92sd_u (α u : ℝ) (P : SignedPoint) : ℝ :=
  α*(edgeWidth u-1)-α*Real.sin u*P.a-α*Real.cos u*P.y
private def r92sd_v (β v : ℝ) (P : SignedPoint) : ℝ :=
  β*(edgeWidth v-1)-β*Real.cos v*P.a-β*Real.sin v*P.y

private theorem r92sd_increment (α β u v : ℝ) (P : SignedPoint) :
    PositiveTD.actualPairIncrement ⟨α,β,u,v⟩ P=r92sd_u α u P+r92sd_v β v P+fullSupport β α := by
  simp only [PositiveTD.actualPairIncrement,pairF,pairG,r92sd_u,r92sd_v]
  ring

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab de eh : Bool)
    (hhg : hg=0∨hg=2) {s ε : ℝ} (hb : delta C.theta B=-s)
    (hd : delta C.theta T=0) :
    actualStress C hg ga ab de eh ε=base ε+
      l ε*TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh)+
      (∑i,actualBlocks C hg ga ab de eh ε i)+c*PairedA.work (C.point T) (-s) 0+
      NonnegativeTotals.Source.aReserve C ga ab (l ε)+NonnegativeTotals.Source.eReserve C de eh := by
  have hT4 : delta C.theta 4=0 := hd
  have hclip : clippedSupport 1 c=(1+c)*Secondary.diagonal := by
    rw [clippedSupport,ite_eq_left (by norm_num [c,NonnegativeTotals.NegativeTD.c]),diagonalSupport]
  have h1 : actualStress C hg ga ab de eh ε=
      k ε*(edgeWidth (delta C.theta H)-C.edge H hg)+
      l ε*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))+
      l ε*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))+
      c*(edgeWidth (delta C.theta B)-C.edge B 3)+c*(edgeWidth (delta C.theta T)-C.edge T 2)+
      1*(edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))+
      1*(edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0)) := by
    rw [actualStress,demand,←sum_force_work,←Finset.sum_sub_distrib]
    simp only [Fin.sum_univ_seven,weights,owners,Matrix.cons_val,H,G,A,B,T,D,E]
    ring
  have hG : l ε*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))=
      r92sd_v (l ε) (erase ga (delta C.theta G)) (C.point G).reflect+
      l ε*(if ga then edgeWidth (delta C.theta G)-1-((C.point A).a*
        Real.sin (delta C.theta G)+(C.point A).y*(1-Real.cos (delta C.theta G))) else 0)+
      l ε+l ε*(C.point A).y := by
    cases ga <;>
      simp only [r92sd_v,r92sd_e1,G,A,quarterProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hA : l ε*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))=
      r92sd_u (l ε) (erase ab (delta C.theta A)) (C.point B).reflect+
      l ε*(if ab then edgeWidth (delta C.theta A)-1-((C.point A).a*
        Real.sin (delta C.theta A)+(C.point A).y*(Real.cos (delta C.theta A)-1)) else 0)+
      l ε-l ε*(C.point A).y := by
    cases ab <;>
      simp only [r92sd_u,r92sd_e2,A,B,zeroProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hBv : c*(edgeWidth (delta C.theta B)-C.edge B 3)=
      r92sd_v c 0 (C.point B).reflect+c*PairedA.work (C.point T) (-s) 0+c+c*(C.point T).y := by
    rw [←hb]
    simp only [r92sd_v,r92sd_e3,B,T,quarterProjection,PairedA.work,
      SignedPoint.reflect,Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
    ring
  have hTv : c*(edgeWidth (delta C.theta T)-C.edge T 2)=
      c*(1-(C.point T).y+(C.point D).y) := by
    simp only [r92sd_e4,T,D,zeroProjection,hT4,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
      edgeWidth_zero]
    ring
  have hDv : 1*(edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))=
      PositiveTD.actualDIncrement c (erase de (delta C.theta D)) (C.point D).reflect+
      (if de then edgeWidth (delta C.theta D)-1-((C.point E).a*Real.sin (delta C.theta D)+
        (C.point E).y*(1-Real.cos (delta C.theta D))) else 0)+
      1+(C.point E).y-c*(C.point D).y-clippedSupport 1 c := by
    cases de <;>
      simp only [r92sd_e5,D,E,quarterProjection,PositiveTD.actualDIncrement,erase,
        SignedPoint.reflect,Bool.false_eq_true,↓reduceIte,Matrix.cons_val,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero] <;>
      ring
  have hEv : 1*(edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0))=
      r92sd_v 1 (erase eh (delta C.theta E)) (C.point H)+
      (if eh then edgeWidth (delta C.theta E)-1-((C.point E).a*Real.sin (delta C.theta E)+
        (C.point E).y*(Real.cos (delta C.theta E)-1)) else 0)+1-(C.point E).y := by
    cases eh <;>
      simp only [r92sd_v,r92sd_e6,E,H,quarterProjection,erase,Bool.false_eq_true,↓reduceIte,
        Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero] <;>
      ring
  rw [h1,hG,hA,hBv,hTv,hDv,hEv]
  rcases hhg with rfl|rfl
  · have hH : k ε*(edgeWidth (delta C.theta H)-C.edge H 0)=
        r92sd_u (k ε) 0 (C.point H)+r92sd_u (k ε) (delta C.theta H) (C.point G).reflect+k ε := by
      simp only [r92sd_u,r92sd_e0,H,G,zeroProjection,SignedPoint.reflect,Matrix.cons_val,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
    rw [hH]
    simp only [actualBlocks,blocks,Fin.sum_univ_four,Matrix.cons_val,r92sd_increment,base,
      NonnegativeTotals.NegativeTD.base,NonnegativeTotals.Source.aReserve,
      NonnegativeTotals.Source.eReserve,PairedE.primaryGain,↓reduceIte]
    linear_combination -hclip
  · have hH : k ε*(edgeWidth (delta C.theta H)-C.edge H 2)=
        r92sd_u (k ε) (delta C.theta H) (C.point H)+r92sd_u (k ε) 0 (C.point G).reflect+k ε := by
      simp only [r92sd_u,r92sd_e0,H,G,zeroProjection,SignedPoint.reflect,Matrix.cons_val,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
    rw [hH]
    simp only [actualBlocks,blocks,Fin.sum_univ_four,Matrix.cons_val,r92sd_increment,base,
      NonnegativeTotals.NegativeTD.base,NonnegativeTotals.Source.aReserve,
      NonnegativeTotals.Source.eReserve,PairedE.primaryGain,
      show ((2:Fin 4)=0)=False by decide,↓reduceIte]
    linear_combination -hclip

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab de eh ε i).u+f (blocks C hg ga ab de eh ε i).v))=
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
    simpa only [ActualOrdinaryBlocks.Block.P,hzero,hTD,positivePart_zero,positiveVariation,sub_zero] using hp
  have hN : (∑i,(blocks C hg ga ab de eh ε i).N)=
      negativeVariation C.theta-s-selectedSum C ga ab de eh negativePart := by
    simpa only [ActualOrdinaryBlocks.Block.N,hneg,hTD,negativePart_zero,negativeVariation,sub_zero] using hn
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
  fin_cases i <;> simp [blocks,ActualOrdinaryBlocks.Block.p,ActualOrdinaryBlocks.Block.q,p,q,NonnegativeTotals.NegativeTD.p,NonnegativeTotals.NegativeTD.q,
    min_eq_left hk,max_eq_right hk,min_eq_left hl,max_eq_right hl,min_eq_left hc,max_eq_right hc]

end SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired.Source
