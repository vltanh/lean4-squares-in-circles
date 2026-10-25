module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELargeAScalars
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELowAStress

/-!
# The actual large-A negative-E stress and its retained variation

Uncompiled source collection for nonpositive TD2. The DE multiplier is
its own secant; EH keeps multiplier one. The exact D support change is
charged once, and its removed ordinary D argument is zero. All remaining
H/G/B/D arguments are the actual source arguments with only designated
primary arguments deleted. Both original A primaries may have either sign.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELargeA.Source
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks
open NegativePrimary (erase)
open PairedE

abbrev aTotal := LowA.aTotal
abbrev magnitude := NegativeELowA.magnitude

def negativeTotal (C : SignedCycle) (de eh : Bool) : ℝ :=
  magnitude C D de+magnitude C E eh-delta C.theta T

def owners (hg ga ab de eh : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,
    2,2,if de then 3 else 2,if eh then 1 else 0]

def weights (C : SignedCycle) (de : Bool) : Vertex→ℝ :=
  ![k,l,l,c,c/Real.cos (delta C.theta T),if de then 1/Real.cos (delta C.theta D) else 1,1]

def stress (C : SignedCycle) (hg ga ab de eh : Bool) : ℝ :=
  ∑i,weights C de i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab de eh i))

def blocks (C : SignedCycle) (hg ga ab de eh : Bool) : Fin 4→Block :=
  ![⟨k,1,erase (!hg) (delta C.theta H),erase eh (delta C.theta E)⟩,
    ⟨k,l,erase hg (delta C.theta H),erase ga (delta C.theta G)⟩,
    ⟨l,c,erase ab (delta C.theta A),delta C.theta B⟩,
    ⟨k,1,erase de (delta C.theta D),0⟩]

def actualBlocks (C : SignedCycle) (hg ga ab de eh : Bool) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab de eh 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh 2) (C.point B).reflect,
    if de then 0 else PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect]

def deGain (C : SignedCycle) (de : Bool) : ℝ :=
  if de then (edgeWidth (delta C.theta D)-(7/12)*Real.sin (delta C.theta D))/
    Real.cos (delta C.theta D)-1-
      ((C.point D).a/Real.cos (delta C.theta D)+c*(-(C.point D).y)-clippedSupport 1 c)
  else 0

def ehGain (C : SignedCycle) (eh : Bool) : ℝ :=
  if eh then edgeWidth (delta C.theta E)-1-
    ((C.point E).a*Real.sin (delta C.theta E)+(C.point E).y*(Real.cos (delta C.theta E)-1))
  else 0

def tGain (C : SignedCycle) : ℝ :=
  c*(edgeWidth (delta C.theta T)-Real.cos (delta C.theta T)-
    (C.point T).a*Real.sin (delta C.theta T)-
    (1-Real.cos (delta C.theta T))*(-(C.point D).y))/Real.cos (delta C.theta T)

private theorem r79_eH (C : SignedCycle) (j : Fin 4) :
    C.edge H j=zeroProjection (C.point H) (C.point G) (delta C.theta H) j := by
  simp only [SignedCycle.edge,word,H,G,next]; rfl
private theorem r79_eG (C : SignedCycle) (j : Fin 4) :
    C.edge G j=quarterProjection (C.point G) (C.point A) (delta C.theta G) j := by
  simp only [SignedCycle.edge,word,G,A,next]; rfl
private theorem r79_eA (C : SignedCycle) (j : Fin 4) :
    C.edge A j=zeroProjection (C.point A) (C.point B) (delta C.theta A) j := by
  simp only [SignedCycle.edge,word,A,B,next]; rfl
private theorem r79_eB (C : SignedCycle) (j : Fin 4) :
    C.edge B j=quarterProjection (C.point B) (C.point T) (delta C.theta B) j := by
  simp only [SignedCycle.edge,word,B,T,next]; rfl
private theorem r79_eT (C : SignedCycle) (j : Fin 4) :
    C.edge T j=zeroProjection (C.point T) (C.point D) (delta C.theta T) j := by
  simp only [SignedCycle.edge,word,T,D,next]; rfl
private theorem r79_eD (C : SignedCycle) (j : Fin 4) :
    C.edge D j=quarterProjection (C.point D) (C.point E) (delta C.theta D) j := by
  simp only [SignedCycle.edge,word,D,E,next]; rfl
private theorem r79_eE (C : SignedCycle) (j : Fin 4) :
    C.edge E j=quarterProjection (C.point E) (C.point H) (delta C.theta E) j := by
  simp only [SignedCycle.edge,word,E,H,next]; rfl

theorem decomposition (C : SignedCycle) (hg ga ab de eh : Bool)
    (hflat : (C.point E).a=7/12)
    (hT : Real.cos (delta C.theta T)≠0) (hD : Real.cos (delta C.theta D)≠0) :
    stress C hg ga ab de eh=base+(∑i,actualBlocks C hg ga ab de eh i)+
      l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
      deGain C de+ehGain C eh+tGain C := by
  have h1 : stress C hg ga ab de eh=
      k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))+
      l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))+
      l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))+
      c*(edgeWidth (delta C.theta B)-C.edge B 2)+
      c/Real.cos (delta C.theta T)*(edgeWidth (delta C.theta T)-C.edge T 2)+
      (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))+
      1*(edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0)) := by
    simp only [stress,Fin.sum_univ_seven,weights,owners,Matrix.cons_val,H,G,A,B,T,D,E]
  have h2 : (∑i,actualBlocks C hg ga ab de eh i)=
      PositiveTD.actualPairIncrement ⟨k,1,erase (!hg) (delta C.theta H),erase eh (delta C.theta E)⟩
        (C.point H)+
      PositiveTD.actualPairIncrement ⟨k,l,erase hg (delta C.theta H),erase ga (delta C.theta G)⟩
        (C.point G).reflect+
      PositiveTD.actualPairIncrement ⟨l,c,erase ab (delta C.theta A),delta C.theta B⟩
        (C.point B).reflect+
      (if de then 0 else PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect) := by
    simp only [Fin.sum_univ_four,actualBlocks,blocks,Matrix.cons_val]
  have hsep0 : PositiveTD.actualPairIncrement ⟨k,1,erase (!hg) (delta C.theta H),
        erase eh (delta C.theta E)⟩ (C.point H)=
      PositiveTD.actualPairIncrement ⟨k,1,erase (!hg) (delta C.theta H),
        erase false (delta C.theta E)⟩ (C.point H)+
      PositiveTD.actualPairIncrement ⟨k,1,erase (!false) (delta C.theta H),
        erase eh (delta C.theta E)⟩ (C.point H)-
      PositiveTD.actualPairIncrement ⟨k,1,erase (!false) (delta C.theta H),
        erase false (delta C.theta E)⟩ (C.point H) := by
    simp only [PositiveTD.actualPairIncrement,pairF,pairG]
    ring
  have hsep1 : PositiveTD.actualPairIncrement ⟨k,l,erase hg (delta C.theta H),
        erase ga (delta C.theta G)⟩ (C.point G).reflect=
      PositiveTD.actualPairIncrement ⟨k,l,erase hg (delta C.theta H),
        erase false (delta C.theta G)⟩ (C.point G).reflect+
      PositiveTD.actualPairIncrement ⟨k,l,erase false (delta C.theta H),
        erase ga (delta C.theta G)⟩ (C.point G).reflect-
      PositiveTD.actualPairIncrement ⟨k,l,erase false (delta C.theta H),
        erase false (delta C.theta G)⟩ (C.point G).reflect := by
    simp only [PositiveTD.actualPairIncrement,pairF,pairG]
    ring
  have hH : k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))=
      k*(edgeWidth (delta C.theta H)-C.edge H 0)+
      (PositiveTD.actualPairIncrement ⟨k,1,erase (!hg) (delta C.theta H),
        erase false (delta C.theta E)⟩ (C.point H)-
       PositiveTD.actualPairIncrement ⟨k,1,erase (!false) (delta C.theta H),
        erase false (delta C.theta E)⟩ (C.point H))+
      (PositiveTD.actualPairIncrement ⟨k,l,erase hg (delta C.theta H),
        erase false (delta C.theta G)⟩ (C.point G).reflect-
       PositiveTD.actualPairIncrement ⟨k,l,erase false (delta C.theta H),
        erase false (delta C.theta G)⟩ (C.point G).reflect) := by
    cases hg
    · simp
    · simp only [PositiveTD.actualPairIncrement,pairF,pairG,erase,Bool.not_false,Bool.not_true,
        Bool.false_eq_true,↓reduceIte,r79_eH,zeroProjection,Matrix.cons_val,SignedPoint.reflect,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hG : l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))=
      l*(edgeWidth (delta C.theta G)-C.edge G 2)+
      (PositiveTD.actualPairIncrement ⟨k,l,erase false (delta C.theta H),
        erase ga (delta C.theta G)⟩ (C.point G).reflect-
       PositiveTD.actualPairIncrement ⟨k,l,erase false (delta C.theta H),
        erase false (delta C.theta G)⟩ (C.point G).reflect)+
      l*(if ga then edgeWidth (delta C.theta G)-1-((C.point A).a*Real.sin (delta C.theta G)+
        (C.point A).y*(1-Real.cos (delta C.theta G))) else 0) := by
    cases ga
    · simp
    · simp only [PositiveTD.actualPairIncrement,pairF,pairG,erase,Bool.false_eq_true,↓reduceIte,
        r79_eG,quarterProjection,Matrix.cons_val,SignedPoint.reflect,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero]
      ring
  have hA : l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))=
      l*(edgeWidth (delta C.theta A)-C.edge A 0)+
      (PositiveTD.actualPairIncrement ⟨l,c,erase ab (delta C.theta A),delta C.theta B⟩
        (C.point B).reflect-
       PositiveTD.actualPairIncrement ⟨l,c,erase false (delta C.theta A),delta C.theta B⟩
        (C.point B).reflect)+
      l*(if ab then edgeWidth (delta C.theta A)-1-((C.point A).a*Real.sin (delta C.theta A)+
        (C.point A).y*(Real.cos (delta C.theta A)-1)) else 0) := by
    cases ab
    · simp
    · simp only [PositiveTD.actualPairIncrement,pairF,pairG,erase,Bool.false_eq_true,↓reduceIte,
        r79_eA,zeroProjection,Matrix.cons_val,SignedPoint.reflect,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero]
      ring
  have hD' : (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))=
      (edgeWidth (delta C.theta D)-C.edge D 2)+
      ((if de then 0 else PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect)-
        PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect)+deGain C de := by
    cases de
    · simp [deGain]
    · simp only [deGain,PositiveTD.actualDIncrement,Bool.false_eq_true,↓reduceIte,r79_eD,
        quarterProjection,Matrix.cons_val,SignedPoint.reflect,hflat]
      field_simp
      ring
  have hE' : 1*(edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0))=
      (edgeWidth (delta C.theta E)-C.edge E 0)+
      (PositiveTD.actualPairIncrement ⟨k,1,erase (!false) (delta C.theta H),
        erase eh (delta C.theta E)⟩ (C.point H)-
       PositiveTD.actualPairIncrement ⟨k,1,erase (!false) (delta C.theta H),
        erase false (delta C.theta E)⟩ (C.point H))+ehGain C eh := by
    cases eh
    · simp [ehGain]
    · simp only [PositiveTD.actualPairIncrement,pairF,pairG,erase,ehGain,Bool.not_false,
        Bool.false_eq_true,↓reduceIte,r79_eE,quarterProjection,Matrix.cons_val,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hc1 : clippedSupport 1 c=(1+c)*GlobalGA.Secondary.diagonal := by
    simp only [clippedSupport,diagonalSupport,c]
    rw [if_pos (by norm_num)]
  have hbase : k*(edgeWidth (delta C.theta H)-C.edge H 0)+
      l*(edgeWidth (delta C.theta G)-C.edge G 2)+
      l*(edgeWidth (delta C.theta A)-C.edge A 0)+
      c*(edgeWidth (delta C.theta B)-C.edge B 2)+
      c/Real.cos (delta C.theta T)*(edgeWidth (delta C.theta T)-C.edge T 2)+
      (edgeWidth (delta C.theta D)-C.edge D 2)+
      (edgeWidth (delta C.theta E)-C.edge E 0)=
      base+PositiveTD.actualPairIncrement ⟨k,1,erase (!false) (delta C.theta H),
        erase false (delta C.theta E)⟩ (C.point H)+
      PositiveTD.actualPairIncrement ⟨k,l,erase false (delta C.theta H),
        erase false (delta C.theta G)⟩ (C.point G).reflect+
      PositiveTD.actualPairIncrement ⟨l,c,erase false (delta C.theta A),delta C.theta B⟩
        (C.point B).reflect+
      PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect+tGain C := by
    simp only [PositiveTD.actualPairIncrement,PositiveTD.actualDIncrement,hc1,pairF,pairG,erase,
      Bool.not_false,Bool.false_eq_true,↓reduceIte,base,tGain,r79_eH,r79_eG,r79_eA,r79_eB,r79_eT,
      r79_eD,r79_eE,zeroProjection,quarterProjection,Matrix.cons_val,SignedPoint.reflect,
      Real.sin_zero,Real.cos_zero,edgeWidth_zero]
    field_simp
    ring
  rw [h1,h2]
  simp only [primaryGain]
  linear_combination hH+hG+hA+hD'+hE'+hbase-hsep0-hsep1

def selectedA (C : SignedCycle) (ga ab : Bool) (f : ℝ→ℝ) : ℝ :=
  selected ga (f (delta C.theta G))+selected ab (f (delta C.theta A))

def selectedNegative (C : SignedCycle) (de eh : Bool) (f : ℝ→ℝ) : ℝ :=
  f (delta C.theta T)+selected de (f (delta C.theta D))+selected eh (f (delta C.theta E))

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
  cases ga <;> cases ab <;> simp [selectedA,aTotal,LowA.aTotal,total,selected] <;> linarith

theorem selectedA_nonnegative (C : SignedCycle) (ga ab : Bool) (f : ℝ→ℝ)
    (hf : ∀x,0≤f x) : 0≤ selectedA C ga ab f := by
  have hG := hf (delta C.theta G)
  have hA := hf (delta C.theta A)
  cases ga <;> cases ab <;> simp [selectedA,selected] <;> positivity

theorem selectedNegative_parts {C : SignedCycle} (de eh : Bool)
    (ht : delta C.theta T≤0) (hd : de=true→delta C.theta D≤0)
    (he : eh=true→delta C.theta E≤0) :
    selectedNegative C de eh positivePart=0 ∧
    selectedNegative C de eh negativePart=negativeTotal C de eh ∧
    0≤negativeTotal C de eh := by
  have hT0 : positivePart (delta C.theta T)=0 := max_eq_right ht
  have hTN : negativePart (delta C.theta T)= -delta C.theta T := max_eq_left (neg_nonneg.mpr ht)
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
    have hT := negativePart_nonneg (delta C.theta T)
    have hD := negativePart_nonneg (delta C.theta D)
    have hE := negativePart_nonneg (delta C.theta E)
    cases de <;> cases eh <;> simp [selectedNegative,selected]
    all_goals positivity
  have hpos : selectedNegative C de eh positivePart=0 := by
    simp [selectedNegative,hT0,hDE0,hEH0]
  have hneg : selectedNegative C de eh negativePart=negativeTotal C de eh := by
    rw [selectedNegative,hTN,hDEN,hEHN]
    dsimp [negativeTotal]
    ring
  exact ⟨hpos,hneg,by rw [← hneg]; exact hneg0⟩

theorem budgets {C : SignedCycle} (hg ga ab de eh : Bool)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (ht : delta C.theta T≤0) (hd : de=true→delta C.theta D≤0)
    (he : eh=true→delta C.theta E≤0) :
    aTotal C ga ab∈Icc 0 frameCap ∧ negativeTotal C de eh∈Icc 0 frameCap ∧
    (∑i,(blocks C hg ga ab de eh i).P)≤frameCap-aTotal C ga ab ∧
    (∑i,(blocks C hg ga ab de eh i).N)≤frameCap-negativeTotal C de eh ∧
    (∑i,(blocks C hg ga ab de eh i).N)-(∑i,(blocks C hg ga ab de eh i).P)=
      aTotal C ga ab-negativeTotal C de eh := by
  have hp := sum_parts C hg ga ab de eh positivePart positivePart_zero
  have hn := sum_parts C hg ga ab de eh negativePart negativePart_zero
  have hparts := selectedNegative_parts de eh ht hd he
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
  fin_cases i <;> norm_num [blocks,Block.p,Block.q,p,q,k,l,c]

theorem actual_blocks_lower {Q : ℝ} {C : SignedCycle} (hg ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hq : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (ht : delta C.theta T≤0) (hd : de=true→delta C.theta D≤0)
    (he : eh=true→delta C.theta E≤0) (i : Fin 4) :
    block i (blocks C hg ga ab de eh i).P (blocks C hg ga ab de eh i).N≤
      actualBlocks C hg ga ab de eh i := by
  have hb := budgets hg ga ab de eh hvar ha ht hd he
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
      have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect) (k:=k) (c:=c)
        (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
        (by simpa using hc D) hq (by norm_num [k]) (by norm_num [k,c])
        (original_error_bound hvar hn D)
      simpa [block,PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,p,q,aD,erase] using hh
    · simp [block,PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,p,q,erase]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELargeA.Source
