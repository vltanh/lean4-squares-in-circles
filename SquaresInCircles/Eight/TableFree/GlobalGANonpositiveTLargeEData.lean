module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELargeAStress
public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTLowESource
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELowAStress

/-!
# Actual large-A negative-E blocks with the aligned BT3 pair removed

Uncompiled all-E nonpositive-T stress. The DE secant and genuine EH
charge are unchanged. Both T arguments are deleted only in the analytic
blocks, and the actual TD alignment is retained in every signed budget.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.LargeE
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks
open NegativePrimary (erase)
open PairedE NegativeELargeA

abbrev aTotal := LowA.aTotal
abbrev magnitude := NegativeELowA.magnitude

def negativeTotal (C : SignedCycle) (de eh : Bool) : ℝ :=
  magnitude C D de+magnitude C E eh-delta C.theta B

def owners (hg ga ab de eh : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,
    3,2,if de then 3 else 2,if eh then 1 else 0]

def weights (C : SignedCycle) (de : Bool) : Vertex→ℝ :=
  ![NegativeELargeA.k,NegativeELargeA.l,NegativeELargeA.l,c,c,if de then 1/Real.cos (delta C.theta D) else 1,1]

def stress (C : SignedCycle) (hg ga ab de eh : Bool) : ℝ :=
  ∑i,weights C de i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab de eh i))

def blocks (C : SignedCycle) (hg ga ab de eh : Bool) : Fin 4→Block :=
  ![⟨NegativeELargeA.k,1,erase (!hg) (delta C.theta H),erase eh (delta C.theta E)⟩,
    ⟨NegativeELargeA.k,NegativeELargeA.l,erase hg (delta C.theta H),erase ga (delta C.theta G)⟩,
    ⟨NegativeELargeA.l,c,erase ab (delta C.theta A),0⟩,
    ⟨NegativeELargeA.k,1,erase de (delta C.theta D),0⟩]

def actualBlocks (C : SignedCycle) (hg ga ab de eh : Bool) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab de eh 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh 2) (C.point B).reflect,
    if de then 0 else PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect]

abbrev deGain := NegativeELargeA.Source.deGain
abbrev ehGain := NegativeELargeA.Source.ehGain

def tGain (C : SignedCycle) : ℝ :=
  c*PairedA.work (C.point T) (delta C.theta B) 0

private theorem r92le_edge_zero (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i=0) :
    C.edge i j=zeroProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92le_edge_quarter (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i≠0) :
    C.edge i j=quarterProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92le_e0 (C : SignedCycle) (j : Fin 4) :
    C.edge 0 j=zeroProjection (C.point 0) (C.point 1) (delta C.theta 0) j :=
  r92le_edge_zero C 0 j (by decide)
private theorem r92le_e1 (C : SignedCycle) (j : Fin 4) :
    C.edge 1 j=quarterProjection (C.point 1) (C.point 2) (delta C.theta 1) j :=
  r92le_edge_quarter C 1 j (by decide)
private theorem r92le_e2 (C : SignedCycle) (j : Fin 4) :
    C.edge 2 j=zeroProjection (C.point 2) (C.point 3) (delta C.theta 2) j :=
  r92le_edge_zero C 2 j (by decide)
private theorem r92le_e3 (C : SignedCycle) (j : Fin 4) :
    C.edge 3 j=quarterProjection (C.point 3) (C.point 4) (delta C.theta 3) j :=
  r92le_edge_quarter C 3 j (by decide)
private theorem r92le_e4 (C : SignedCycle) (j : Fin 4) :
    C.edge 4 j=zeroProjection (C.point 4) (C.point 5) (delta C.theta 4) j :=
  r92le_edge_zero C 4 j (by decide)
private theorem r92le_e5 (C : SignedCycle) (j : Fin 4) :
    C.edge 5 j=quarterProjection (C.point 5) (C.point 6) (delta C.theta 5) j :=
  r92le_edge_quarter C 5 j (by decide)
private theorem r92le_e6 (C : SignedCycle) (j : Fin 4) :
    C.edge 6 j=quarterProjection (C.point 6) (C.point 0) (delta C.theta 6) j :=
  r92le_edge_quarter C 6 j (by decide)

private def r92le_u (α u : ℝ) (P : SignedPoint) : ℝ :=
  α*(edgeWidth u-1)-α*Real.sin u*P.a-α*Real.cos u*P.y
private def r92le_v (β v : ℝ) (P : SignedPoint) : ℝ :=
  β*(edgeWidth v-1)-β*Real.cos v*P.a-β*Real.sin v*P.y

private theorem r92le_increment (α β u v : ℝ) (P : SignedPoint) :
    PositiveTD.actualPairIncrement ⟨α,β,u,v⟩ P=r92le_u α u P+r92le_v β v P+fullSupport β α := by
  simp only [PositiveTD.actualPairIncrement,pairF,pairG,r92le_u,r92le_v]
  ring

theorem decomposition (C : SignedCycle) (hg ga ab de eh : Bool)
    (hflat : (C.point E).a=7/12)
    (hTD : delta C.theta T=0) (hD : Real.cos (delta C.theta D)≠0) :
    stress C hg ga ab de eh=base+(∑i,actualBlocks C hg ga ab de eh i)+
      NegativeELargeA.l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
      deGain C de+ehGain C eh+tGain C := by
  have hT4 : delta C.theta 4=0 := hTD
  have hE6 : (C.point 6).a=7/12 := hflat
  have hinv : Real.cos (delta C.theta 5)*(Real.cos (delta C.theta 5))⁻¹=1 := mul_inv_cancel₀ hD
  have hclip : clippedSupport 1 c=(1+c)*Secondary.diagonal := by
    rw [clippedSupport,ite_eq_left (by norm_num [c]),diagonalSupport]
  have h1 : stress C hg ga ab de eh=
      NegativeELargeA.k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))+
      NegativeELargeA.l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))+
      NegativeELargeA.l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))+
      c*(edgeWidth (delta C.theta B)-C.edge B 3)+c*(edgeWidth (delta C.theta T)-C.edge T 2)+
      (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))+
      1*(edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0)) := by
    simp only [stress,Fin.sum_univ_seven,weights,owners,Matrix.cons_val,H,G,A,B,T,D,E]
  have hH : NegativeELargeA.k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))=
      r92le_u NegativeELargeA.k (erase (!hg) (delta C.theta H)) (C.point H)+
      r92le_u NegativeELargeA.k (erase hg (delta C.theta H)) (C.point G).reflect+
      NegativeELargeA.k := by
    cases hg <;>
      simp only [r92le_u,r92le_e0,H,G,zeroProjection,erase,SignedPoint.reflect,Bool.not_true,
        Bool.not_false,Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hG : NegativeELargeA.l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))=
      r92le_v NegativeELargeA.l (erase ga (delta C.theta G)) (C.point G).reflect+
      NegativeELargeA.l*(if ga then edgeWidth (delta C.theta G)-1-((C.point A).a*
        Real.sin (delta C.theta G)+(C.point A).y*(1-Real.cos (delta C.theta G))) else 0)+
      NegativeELargeA.l+NegativeELargeA.l*(C.point A).y := by
    cases ga <;>
      simp only [r92le_v,r92le_e1,G,A,quarterProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hA : NegativeELargeA.l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))=
      r92le_u NegativeELargeA.l (erase ab (delta C.theta A)) (C.point B).reflect+
      NegativeELargeA.l*(if ab then edgeWidth (delta C.theta A)-1-((C.point A).a*
        Real.sin (delta C.theta A)+(C.point A).y*(Real.cos (delta C.theta A)-1)) else 0)+
      NegativeELargeA.l-NegativeELargeA.l*(C.point A).y := by
    cases ab <;>
      simp only [r92le_u,r92le_e2,A,B,zeroProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hB : c*(edgeWidth (delta C.theta B)-C.edge B 3)=
      r92le_v c 0 (C.point B).reflect+tGain C+c+c*(C.point T).y := by
    simp only [r92le_v,r92le_e3,B,T,quarterProjection,tGain,PairedA.work,SignedPoint.reflect,
      Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
    ring
  have hT : c*(edgeWidth (delta C.theta T)-C.edge T 2)=
      c*(1-(C.point T).y+(C.point D).y) := by
    simp only [r92le_e4,T,D,zeroProjection,hT4,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
      edgeWidth_zero]
    ring
  have hDv : (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))=
      (if de then 0 else PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect)+
      deGain C de+1+(C.point E).y-c*(C.point D).y-clippedSupport 1 c := by
    cases de
    · simp only [r92le_e5,D,E,quarterProjection,deGain,NegativeELargeA.Source.deGain,
        PositiveTD.actualDIncrement,SignedPoint.reflect,Bool.false_eq_true,↓reduceIte,
        Matrix.cons_val]
      ring
    · simp only [r92le_e5,D,E,quarterProjection,deGain,NegativeELargeA.Source.deGain,hE6,
        ↓reduceIte,Matrix.cons_val]
      linear_combination (C.point 6).y*hinv
  have hEv : 1*(edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0))=
      r92le_v 1 (erase eh (delta C.theta E)) (C.point H)+ehGain C eh+1-(C.point E).y := by
    cases eh <;>
      simp only [r92le_v,r92le_e6,E,H,quarterProjection,ehGain,NegativeELargeA.Source.ehGain,erase,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  rw [h1,hH,hG,hA,hB,hT,hDv,hEv]
  simp only [actualBlocks,blocks,Fin.sum_univ_four,Matrix.cons_val,r92le_increment,base,
    primaryGain]
  linear_combination -hclip

def selectedA (C : SignedCycle) (ga ab : Bool) (f : ℝ→ℝ) : ℝ :=
  selected ga (f (delta C.theta G))+selected ab (f (delta C.theta A))

def selectedNegative (C : SignedCycle) (de eh : Bool) (f : ℝ→ℝ) : ℝ :=
  f (delta C.theta B)+f (delta C.theta T)+selected de (f (delta C.theta D))+selected eh (f (delta C.theta E))

theorem sum_parts (C : SignedCycle) (hg ga ab de eh : Bool)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab de eh i).u+f (blocks C hg ga ab de eh i).v))=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-selectedNegative C de eh f := by
  cases hg <;> cases ga <;> cases ab <;> cases de <;> cases eh <;>
    simp [blocks,erase,selectedA,selectedNegative,selected,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

theorem selectedA_signed (C : SignedCycle) (ga ab : Bool) :
    selectedA C ga ab positivePart-selectedA C ga ab negativePart=aTotal C ga ab := by
  have hG := positive_sub_negative (delta C.theta G)
  have hA := positive_sub_negative (delta C.theta A)
  cases ga <;> cases ab <;>
    simp [selectedA,aTotal,PairedE.LowA.aTotal,PairedE.total,PairedE.selected] <;> linarith

theorem selectedA_nonnegative (C : SignedCycle) (ga ab : Bool) (f : ℝ→ℝ)
    (hf : ∀x,0≤f x) : 0≤ selectedA C ga ab f := by
  have hG := hf (delta C.theta G)
  have hA := hf (delta C.theta A)
  cases ga <;> cases ab <;> simp [selectedA,selected] <;> positivity

theorem selectedNegative_parts {C : SignedCycle} (de eh : Bool)
    (ht : delta C.theta B≤0) (hTD : delta C.theta T=0) (hd : de=true→delta C.theta D≤0)
    (he : eh=true→delta C.theta E≤0) :
    selectedNegative C de eh positivePart=0 ∧
    selectedNegative C de eh negativePart=negativeTotal C de eh ∧
    0≤negativeTotal C de eh := by
  have hT0 : positivePart (delta C.theta B)=0 := max_eq_right ht
  have hTN : negativePart (delta C.theta B)= -delta C.theta B := max_eq_left (neg_nonneg.mpr ht)
  have hDE0 : selected de (positivePart (delta C.theta D))=0 := by
    cases hd' : de
    · simp [selected]
    · simp [selected,positivePart,max_eq_right (hd hd')]
  have hEH0 : selected eh (positivePart (delta C.theta E))=0 := by
    cases he' : eh
    · simp [selected]
    · simp [selected,positivePart,max_eq_right (he he')]
  have hDEN : selected de (negativePart (delta C.theta D))=magnitude C D de := by
    cases hd' : de
    · simp [selected,magnitude,NegativeELowA.magnitude]
    · simp [selected,magnitude,NegativeELowA.magnitude,negativePart,max_eq_left (neg_nonneg.mpr (hd hd'))]
  have hEHN : selected eh (negativePart (delta C.theta E))=magnitude C E eh := by
    cases he' : eh
    · simp [selected,magnitude,NegativeELowA.magnitude]
    · simp [selected,magnitude,NegativeELowA.magnitude,negativePart,max_eq_left (neg_nonneg.mpr (he he'))]
  have hneg0 : 0≤ selectedNegative C de eh negativePart := by
    have hB := negativePart_nonneg (delta C.theta B)
    have hT := negativePart_nonneg (delta C.theta T)
    have hD := negativePart_nonneg (delta C.theta D)
    have hE := negativePart_nonneg (delta C.theta E)
    cases de <;> cases eh <;> simp [selectedNegative,selected]
    all_goals positivity
  have hpos : selectedNegative C de eh positivePart=0 := by
    simp [selectedNegative,hT0,hTD,positivePart_zero,hDE0,hEH0]
  have hneg : selectedNegative C de eh negativePart=negativeTotal C de eh := by
    rw [selectedNegative,hTN,hTD,negativePart_zero,hDEN,hEHN]
    dsimp [negativeTotal]
    ring
  exact ⟨hpos,hneg,by rw [← hneg]; exact hneg0⟩

theorem budgets {C : SignedCycle} (hg ga ab de eh : Bool)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (ht : delta C.theta B≤0) (hTD : delta C.theta T=0) (hd : de=true→delta C.theta D≤0)
    (he : eh=true→delta C.theta E≤0) :
    aTotal C ga ab∈Icc 0 frameCap ∧ negativeTotal C de eh∈Icc 0 frameCap ∧
    (∑i,(blocks C hg ga ab de eh i).P)≤frameCap-aTotal C ga ab ∧
    (∑i,(blocks C hg ga ab de eh i).N)≤frameCap-negativeTotal C de eh ∧
    (∑i,(blocks C hg ga ab de eh i).N)-(∑i,(blocks C hg ga ab de eh i).P)=
      aTotal C ga ab-negativeTotal C de eh := by
  have hp := sum_parts C hg ga ab de eh positivePart positivePart_zero
  have hn := sum_parts C hg ga ab de eh negativePart negativePart_zero
  have hparts := selectedNegative_parts de eh ht hTD hd he
  have haSigned := selectedA_signed C ga ab
  have haN := selectedA_nonnegative C ga ab negativePart negativePart_nonneg
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab de eh i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab de eh i).N_nonneg)
  have hP : (∑i,(blocks C hg ga ab de eh i).P)=
      positiveVariation C.theta-selectedA C ga ab positivePart := by
    simpa only [Block.P,hparts.1,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab de eh i).N)=
      negativeVariation C.theta-selectedA C ga ab negativePart-negativeTotal C de eh := by
    simpa only [Block.N,hparts.2.1,negativeVariation] using hn
  have hvariation := variations_equal C.theta
  exact ⟨⟨ha,by linarith⟩,⟨hparts.2.2,by linarith⟩,
    by linarith,by linarith,by linarith⟩

theorem block_coefficients (C : SignedCycle) (hg ga ab de eh : Bool) (i : Fin 4) :
    (blocks C hg ga ab de eh i).p=p i ∧ (blocks C hg ga ab de eh i).q=q i := by
  fin_cases i <;> norm_num [blocks,Block.p,Block.q,p,q,NegativeELargeA.k,NegativeELargeA.l,c]

theorem actual_blocks_lower {Q : ℝ} {C : SignedCycle} (hg ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hq : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (ht : delta C.theta B≤0) (hTD : delta C.theta T=0) (hd : de=true→delta C.theta D≤0)
    (he : eh=true→delta C.theta E≤0) (i : Fin 4) :
    block i (blocks C hg ga ab de eh i).P (blocks C hg ga ab de eh i).N≤
      actualBlocks C hg ga ab de eh i := by
  have hb := budgets hg ga ab de eh hvar ha ht hTD hd he
  have hbudget (i : Fin 4) : (blocks C hg ga ab de eh i).P≤frameCap ∧
      (blocks C hg ga ab de eh i).N≤frameCap := by
    have hP := Finset.single_le_sum (s:=Finset.univ)
      (fun j _ => (blocks C hg ga ab de eh j).P_nonneg) (Finset.mem_univ i)
    have hN := Finset.single_le_sum (s:=Finset.univ)
      (fun j _ => (blocks C hg ga ab de eh j).N_nonneg) (Finset.mem_univ i)
    exact ⟨by linarith [hb.2.2.1],by linarith [hb.2.1.1,hb.2.2.2.1]⟩
  have hordinary (i : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained Q) :
      OrdinaryAngleConcavity.mixedBlock R (p i) (q i)
        (blocks C hg ga ab de eh i).P (blocks C hg ga ab de eh i).N≤
        PositiveTD.actualPairIncrement (blocks C hg ga ab de eh i) P := by
    have hcoef := block_coefficients C hg ga ab de eh i
    have hminor := PositiveTD.actual_block_minorant hy hP hq
      (show 0≤(blocks C hg ga ab de eh i).p by rw [hcoef.1]; exact (coefficients i).1.le)
      (hbudget i).1 (hbudget i).2
    simpa only [hcoef.1,hcoef.2] using hminor
  fin_cases i
  · simpa [block,PositiveTD.Hybrid.block,actualBlocks] using hordinary 0 hHy (hc H)
  · simpa [block,PositiveTD.Hybrid.block,actualBlocks] using hordinary 1
      (P:=(C.point G).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G)
  · simpa [block,PositiveTD.Hybrid.block,actualBlocks] using hordinary 2
      (P:=(C.point B).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hc B)
  · cases hde : de
    · have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
      have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect) (k:=NegativeELargeA.k) (c:=c)
        (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
        (by simpa using hc D) hq (by norm_num [NegativeELargeA.k]) (by norm_num [NegativeELargeA.k,c])
        (original_error_bound hvar hn D)
      simpa [block,PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,p,q,aD,erase] using hh
    · simp [block,PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,p,q,erase]

end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.LargeE
