module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.ELowAStress
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3DEnvelopeGeometry

/-!
# Eight squares: the negative-DE / positive-TD2 scalar inequality at the original cycle

The selected A arguments may have opposite signs. Their
signed total is used only after the actual primary gains have been
bounded. The DE secant stays in the original D support, and every
ordinary block retains its original positive and negative masses.
-/

section
/-!
## The large-A negative-E stress and its variation

The DE multiplier is its own secant; EH keeps multiplier one. The change of the D support is
charged once, and its removed ordinary D argument is zero. All other H, G, B, D arguments are those
of the cycle, with only the selected primary arguments deleted (`decomposition`). Both A primaries
may have either sign.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeELargeA.Source
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
    · simp only [deGain,PositiveTD.actualDIncrement,↓reduceIte,r79_eD,
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
    rw [ite_eq_left (by norm_num)]
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

end SquaresInCircles.Eight.GlobalGA.NegativeELargeA.Source
end
end
end

section
/-!
## The original negative-DE3 / positive-TD2 stress data

DE carries its own
secant, EH keeps multiplier one, and both selected A primaries retain
their original signs.  Only the selected A arguments, TD and DE are
deleted from the three actual H/G/B circle blocks.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks PairedE
open NegativePrimary (erase)

abbrev aTotal := LowA.aTotal
abbrev selectedA := NegativeELargeA.Source.selectedA

def total (C : SignedCycle) (ga ab : Bool) : ℝ := aTotal C ga ab+delta C.theta T
def magnitude (C : SignedCycle) : ℝ := -delta C.theta D

def owners (hg ga ab : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,2,2,3,0]
def weights (C : SignedCycle) (k l c : ℝ) : Vertex→ℝ :=
  ![k,l,l,PositiveTD.tilted c (delta C.theta T),c,1/Real.cos (delta C.theta D),1]
def stress (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ) : ℝ :=
  ∑i,weights C k l c i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

def blocks (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ) : Fin 3→Block :=
  ![⟨k,1,erase (!hg) (delta C.theta H),delta C.theta E⟩,
    ⟨k,l,erase hg (delta C.theta H),erase ga (delta C.theta G)⟩,
    ⟨l,PositiveTD.tilted c (delta C.theta T),erase ab (delta C.theta A),delta C.theta B⟩]
def actualBlocks (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ) : Fin 3→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 2) (C.point B).reflect]

def deCorrection (C : SignedCycle) : ℝ :=
  (edgeWidth (delta C.theta D)-(7/12)*Real.sin (delta C.theta D))/
    Real.cos (delta C.theta D)-1/Real.cos (delta C.theta D)
def base (C : SignedCycle) (k l c : ℝ) : ℝ :=
  k+2*l+PositiveTD.tilted c (delta C.theta T)+c*edgeWidth (delta C.theta T)+
    1/Real.cos (delta C.theta D)+1-c*PositiveTD.sigma*Real.sin (delta C.theta T)-
    fullSupport 1 k-fullSupport l k-fullSupport (PositiveTD.tilted c (delta C.theta T)) l-
    clippedSupport (1/Real.cos (delta C.theta D)) c+deCorrection C
def dReserve (C : SignedCycle) (c : ℝ) : ℝ :=
  clippedSupport (1/Real.cos (delta C.theta D)) c-
    ((C.point D).a/Real.cos (delta C.theta D)+c*(-(C.point D).y))

theorem decomposition (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ)
    (hflat : (C.point E).a=7/12) (hcos : Real.cos (delta C.theta D)≠0) :
    stress C hg ga ab k l c=base C k l c+(∑i,actualBlocks C hg ga ab k l c i)+
      l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
      PositiveTD.tReserve C c+dReserve C c := by
  have hf : (C.point 6).a=7/12 := hflat
  have hu : Real.cos (C.theta 6-C.theta 5)*(Real.cos (C.theta 6-C.theta 5))⁻¹=1 :=
    mul_inv_cancel₀ hcos
  cases hg <;> cases ga <;> cases ab <;>
    simp [stress,weights,owners,blocks,actualBlocks,base,deCorrection,dReserve,
      PositiveTD.actualPairIncrement,PositiveTD.tReserve,PositiveTD.tilted,pairF,pairG,
      primaryGain,erase,hf,SignedCycle.edge,zeroProjection,quarterProjection,
      Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,SignedPoint.reflect] <;>
    linear_combination (C.point 6).y*hu

theorem sum_parts (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab k l c i).u+f (blocks C hg ga ab k l c i).v))=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-
        f (delta C.theta T)-f (delta C.theta D) := by
  cases hg <;> cases ga <;> cases ab <;>
    simp [blocks,erase,selectedA,NegativeELargeA.Source.selectedA,selected,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

structure Budgets (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ) : Prop where
  total_domain : total C ga ab∈Icc 0 frameCap
  a_domain : aTotal C ga ab∈Icc 0 (total C ga ab)
  td_domain : delta C.theta T∈Icc 0 (total C ga ab)
  de_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l c i).P)≤frameCap-total C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l c i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l c i).N)-(∑i,(blocks C hg ga ab k l c i).P)=
    total C ga ab-magnitude C

theorem budgets {C : SignedCycle} (hg ga ab : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0) : Budgets C hg ga ab k l c := by
  have hp := sum_parts C hg ga ab k l c positivePart positivePart_zero
  have hn := sum_parts C hg ga ab k l c negativePart negativePart_zero
  have hA := NegativeELargeA.Source.selectedA_signed C ga ab
  have hAP := NegativeELargeA.Source.selectedA_nonnegative C ga ab positivePart positivePart_nonneg
  have hAN := NegativeELargeA.Source.selectedA_nonnegative C ga ab negativePart negativePart_nonneg
  have hzP : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hzN : negativePart (delta C.theta T)=0 := max_eq_right (by linarith)
  have hsP : positivePart (delta C.theta D)=0 := max_eq_right hs
  have hsN : negativePart (delta C.theta D)=magnitude C := max_eq_left (neg_nonneg.mpr hs)
  have hP : (∑i,(blocks C hg ga ab k l c i).P)=
      positiveVariation C.theta-selectedA C ga ab positivePart-delta C.theta T := by
    simpa only [Block.P,hzP,hsP,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab k l c i).N)=
      negativeVariation C.theta-selectedA C ga ab negativePart-magnitude C := by
    simpa only [Block.N,hzN,hsN,sub_zero,negativeVariation] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l c i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l c i).N_nonneg)
  have heq := variations_equal C.theta
  have hs0 : 0≤ magnitude C := neg_nonneg.mpr hs
  change selectedA C ga ab positivePart-selectedA C ga ab negativePart=aTotal C ga ab at hA
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [total]; exact ⟨add_nonneg ha hz,by linarith⟩
  · dsimp [total]; exact ⟨ha,by linarith⟩
  · dsimp [total]; exact ⟨hz,by linarith⟩
  · exact ⟨hs0,by linarith⟩
  · dsimp [total]; linarith
  · linarith
  · dsimp [total]; linarith

theorem block_coefficients {C : SignedCycle} (hg ga ab : Bool) {k l c : ℝ}
    (hk : k≤1) (hl : k≤l) (i : Fin 3) :
    (blocks C hg ga ab k l c i).p=(![k,k,min l (PositiveTD.tilted c (delta C.theta T))] : Fin 3→ℝ) i ∧
    (blocks C hg ga ab k l c i).q=(![1,l,max l (PositiveTD.tilted c (delta C.theta T))] : Fin 3→ℝ) i := by
  fin_cases i <;> simp [blocks,Block.p,Block.q,min_eq_left hk,max_eq_right hk,
    min_eq_left hl,max_eq_right hl]

theorem family_coefficients (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f)) (hz : z∈Icc 0 θ) :
    Explicit.k f θ≤1 ∧ Explicit.k f θ≤Explicit.l f θ ∧
      (∀i,0<Explicit.p f θ z i ∧ Explicit.p f θ z i≤Explicit.q f θ z i ∧
        Explicit.q f θ z i≤2*Explicit.p f θ z i) := by
  cases f
  · have hr := Explicit.low_ranges hθ
    have hm := Explicit.low_tilted hθ hz
    have hk : 0<Explicit.k .low θ := by linarith [hr.1]
    have hl : 0<Explicit.l .low θ := by linarith [hr.2.2.1]
    have hlm : Explicit.l .low θ≤Explicit.m .low θ z := hr.2.2.2.2.2.2.1.trans hm.1
    refine ⟨by linarith [hr.2.1],by linarith [hr.2.1,hr.2.2.1],?_⟩
    intro i
    fin_cases i
    · show 0<Explicit.k .low θ ∧ Explicit.k .low θ≤1 ∧ 1≤2*Explicit.k .low θ
      exact ⟨hk,by linarith [hr.2.1],by linarith [hr.1]⟩
    · show 0<Explicit.k .low θ ∧ Explicit.k .low θ≤Explicit.l .low θ ∧
        Explicit.l .low θ≤2*Explicit.k .low θ
      exact ⟨hk,by linarith [hr.2.1,hr.2.2.1],hr.2.2.2.2.2.2.2.le⟩
    · show 0 < min (Explicit.l .low θ) (Explicit.m .low θ z) ∧
        min (Explicit.l .low θ) (Explicit.m .low θ z) ≤ max (Explicit.l .low θ) (Explicit.m .low θ z) ∧
        max (Explicit.l .low θ) (Explicit.m .low θ z) ≤ 2*min (Explicit.l .low θ) (Explicit.m .low θ z)
      rw [min_eq_left hlm,max_eq_right hlm]
      exact ⟨hl,hlm,by linarith [hm.2]⟩
  · have hr := Explicit.high_ranges hθ
    refine ⟨by linarith [hr.2.1],by linarith [hr.2.1,hr.2.2.1],?_⟩
    intro i
    have hh := Explicit.high_pairs hθ hz i
    exact ⟨hh.1,hh.2.1,by linarith [hh.2.2.1]⟩

theorem family_block_coefficients {C : SignedCycle} (hg ga ab : Bool) (f : Family)
    (hθ : total C ga ab∈Icc (Explicit.left f) (Explicit.right f))
    (hz : delta C.theta T∈Icc 0 (total C ga ab)) (i : Fin 3) :
    (blocks C hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
      (Explicit.c f (total C ga ab)) i).p=Explicit.p f (total C ga ab) (delta C.theta T) i ∧
    (blocks C hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
      (Explicit.c f (total C ga ab)) i).q=Explicit.q f (total C ga ab) (delta C.theta T) i := by
  have hh := family_coefficients f hθ hz
  simpa only [Explicit.p,Explicit.q,Explicit.m,Explicit.eta,PositiveTD.tilted,PositiveTD.eta]
    using block_coefficients hg ga ab (c:=Explicit.c f (total C ga ab)) hh.1 hh.2.1 i

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Source
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks PairedE SignedStress PositiveBT3

/-- The width identity at the actual negative DE error, including zero. -/
theorem deCorrection_identity {C : SignedCycle}
    (hs : magnitude C∈Icc 0 frameCap) :
    deCorrection C=Explicit.K*Real.tan (magnitude C)-
      (Explicit.secant (magnitude C)-1)/2 := by
  have hcos : Real.cos (magnitude C)≠0 :=
    (show 0<Real.cos (magnitude C) by linarith [(transport_trig hs).1]).ne'
  have hd : delta C.theta D= -magnitude C := by simp [magnitude]
  rw [deCorrection,hd,edgeWidth_negative_formula hs,Real.sin_neg,Real.cos_neg]
  dsimp [Explicit.K,Explicit.secant]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]
  ring

/-- This is an identity, not a change of the actual A/TD split. -/
theorem baseline_identity {C : SignedCycle} (ga ab : Bool) (f : Family)
    (hs : magnitude C∈Icc 0 frameCap) :
    base C (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
        (Explicit.c f (total C ga ab))+
      Explicit.l f (total C ga ab)*TwoPositive.ASupport.charge (aTotal C ga ab)=
      Explicit.baseline f (aTotal C ga ab) (delta C.theta T) (magnitude C) := by
  have hd : Real.cos (delta C.theta D)=Real.cos (magnitude C) := by
    simp [magnitude]
  rw [base,deCorrection_identity hs,hd]
  dsimp [Explicit.baseline,total,Explicit.m,Explicit.eta,Explicit.sigma,
    Explicit.secant,PositiveTD.tilted,PositiveTD.eta,PositiveTD.sigma]
  ring

/-- The full-circle high baseline is a lower bound for the actual sorted D baseline. -/
theorem fullBaseline_le (f : Family) (a z s : ℝ) :
    Explicit.fullBaseline f a z s≤Explicit.baseline f a z s := by
  have hclip : clippedSupport (Explicit.secant s) (Explicit.c f (a+z))≤
      fullSupport (Explicit.secant s) (Explicit.c f (a+z)) := by
    by_cases h : Explicit.secant s≤Explicit.c f (a+z)
    · rw [clippedSupport,ite_eq_left h]
      have hh := raw_full_support (a:=GlobalGA.Secondary.diagonal) (b:=GlobalGA.Secondary.diagonal)
        (f:=Explicit.secant s) (g:=Explicit.c f (a+z))
        (show (GlobalGA.Secondary.diagonal+1/2)^2+(GlobalGA.Secondary.diagonal+1/2)^2≤qCap by nlinarith [diagonal_circle])
      simpa [diagonalSupport,add_mul] using hh
    · simp [clippedSupport,h]
  dsimp [Explicit.fullBaseline]
  linarith

theorem dReserve_nonnegative {Q c : ℝ} {C : SignedCycle}
    (hsorted : (C.point D).Sorted) (hy : (C.point D).y≤0)
    (hcontained : (C.point D).Contained Q) (hQ : Q≤qCap)
    (hc : 0≤c) (hs : magnitude C∈Icc 0 frameCap) : 0≤dReserve C c := by
  have hcos : 0<Real.cos (delta C.theta D) := by
    simpa [magnitude] using (show 0<Real.cos (magnitude C) by
      linarith [(transport_trig hs).1])
  have hcircle : ((C.point D).a+1/2)^2+(-(C.point D).y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hy]
      using hcontained.trans hQ
  have horder : -(C.point D).y≤(C.point D).a := by
    simpa [abs_of_nonpos hy] using hsorted.2
  have hh := raw_clipped_support (f:=1/Real.cos (delta C.theta D)) (g:=c)
    hcircle horder (by linarith [hsorted.1])
    (add_nonneg (div_nonneg (by norm_num) hcos.le) hc)
  dsimp [dReserve]
  have he : (C.point D).a/Real.cos (delta C.theta D)=
      (1/Real.cos (delta C.theta D))*(C.point D).a := by ring
  rw [he]
  linarith

/-- TD2 has direction (1,-eta), exactly as in the original stress. -/
theorem tReserve_nonnegative {Q c : ℝ} {C : SignedCycle}
    (hsorted : (C.point T).Sorted) (hcontained : (C.point T).Contained Q)
    (hQ : Q≤qCap) (hc : 0≤c) (hz : delta C.theta T∈Icc 0 frameCap) :
    0≤PositiveTD.tReserve C c :=
  PositiveTD.tReserve_nonneg hsorted hcontained hQ hc hz

theorem actual_blocks_lower {Q : ℝ} {C : SignedCycle}
    (hg ga ab : Bool) (f : Family)
    (_hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hθ : total C ga ab∈Icc (Explicit.left f) (Explicit.right f)) (i : Fin 3) :
    mixedBlock R (Explicit.p f (total C ga ab) (delta C.theta T) i)
      (Explicit.q f (total C ga ab) (delta C.theta T) i)
      (blocks C hg ga ab (Explicit.k f (total C ga ab))
        (Explicit.l f (total C ga ab)) (Explicit.c f (total C ga ab)) i).P
      (blocks C hg ga ab (Explicit.k f (total C ga ab))
        (Explicit.l f (total C ga ab)) (Explicit.c f (total C ga ab)) i).N≤
      actualBlocks C hg ga ab (Explicit.k f (total C ga ab))
        (Explicit.l f (total C ga ab)) (Explicit.c f (total C ga ab)) i := by
  let k := Explicit.k f (total C ga ab)
  let l := Explicit.l f (total C ga ab)
  let c := Explicit.c f (total C ga ab)
  have hb := budgets hg ga ab k l c hvar ha hz hs
  have hp := family_coefficients f hθ hb.td_domain
  have hcoef := family_block_coefficients hg ga ab f hθ hb.td_domain i
  have hP := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l c j).P_nonneg) (Finset.mem_univ i)
  have hN := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l c j).N_nonneg) (Finset.mem_univ i)
  have hPb : (blocks C hg ga ab k l c i).P≤frameCap := by
    linarith [hb.positive_bound,hb.total_domain.1]
  have hNb : (blocks C hg ga ab k l c i).N≤frameCap := by
    linarith [hb.negative_bound,hb.de_domain.1]
  have hsmall : 0≤(blocks C hg ga ab k l c i).p := by
    rw [hcoef.1]
    exact (hp.2.2 i).1.le
  have hminor {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained Q) :=
    PositiveTD.actual_block_minorant hy hP hQ hsmall hPb hNb
  rw [←hcoef.1,←hcoef.2]
  fin_cases i
  · simpa [actualBlocks,k,l,c] using hminor hHy (hcontained H)
  · simpa [actualBlocks,k,l,c] using hminor (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hcontained G)
  · simpa [actualBlocks,k,l,c] using hminor (P:=(C.point B).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hcontained B)

theorem stress_nonpositive {C : SignedCycle} (hg ga ab : Bool) {k l c : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c)
    (hz : delta C.theta T∈Icc 0 frameCap) (hs : magnitude C∈Icc 0 frameCap)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : stress C hg ga ab k l c≤0 := by
  have hm := PositiveTD.tilted_pos hc hz
  have hcos : 0<Real.cos (delta C.theta D) := by
    simpa [magnitude] using (show 0<Real.cos (magnitude C) by
      linarith [(transport_trig hs).1])
  have hw (i : Vertex) : 0≤weights C k l c i := by
    fin_cases i
    · exact hk
    · exact hl
    · exact hl
    · exact hm.le
    · exact hc.le
    · exact (one_div_pos.mpr hcos).le
    · exact zero_le_one
  apply Finset.sum_nonpos
  intro i _
  have hi : edgeWidth (delta C.theta i)≤C.edge i (owners hg ga ab i) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,sub_nonneg] using hfeasible i
  exact mul_nonpos_of_nonneg_of_nonpos (hw i) (sub_nonpos.mpr hi)

/-- The complete scalar necessary inequality, with no substituted angles
or new feasibility assumptions. Its remaining task is scalar positivity. -/
theorem scalar_nonpositive {Q : ℝ} {C : SignedCycle}
    (hg ga ab : Bool) (f : Family)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0)
    (hflat : (C.point E).a=7/12)
    (hθ : total C ga ab∈Icc (Explicit.left f) (Explicit.right f))
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) :
    Explicit.baseline f (aTotal C ga ab) (delta C.theta T) (magnitude C)+
      ∑i,mixedBlock R (Explicit.p f (total C ga ab) (delta C.theta T) i)
        (Explicit.q f (total C ga ab) (delta C.theta T) i)
        (blocks C hg ga ab (Explicit.k f (total C ga ab))
          (Explicit.l f (total C ga ab)) (Explicit.c f (total C ga ab)) i).P
        (blocks C hg ga ab (Explicit.k f (total C ga ab))
          (Explicit.l f (total C ga ab)) (Explicit.c f (total C ga ab)) i).N≤0 := by
  let k := Explicit.k f (total C ga ab)
  let l := Explicit.l f (total C ga ab)
  let c := Explicit.c f (total C ga ab)
  have hb := budgets hg ga ab k l c hvar ha hz hs
  have hp := Explicit.family_positive f hθ hb.td_domain
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hA := PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
    (original_error_bound hvar hn G) (original_error_bound hvar hn A)
    (show aTotal C ga ab∈Icc 0 frameCap from
      ⟨ha,hb.a_domain.2.trans hb.total_domain.2⟩)
  change TwoPositive.ASupport.charge (aTotal C ga ab)≤
    primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A) at hA
  have hAg := mul_le_mul_of_nonneg_left hA hp.2.1.le
  have hzframe : delta C.theta T∈Icc 0 frameCap :=
    ⟨hz,hb.td_domain.2.trans hb.total_domain.2⟩
  have hT := tReserve_nonnegative (hsorted T) (hcontained T) hQ hp.2.2.1.le hzframe
  have hD := dReserve_nonnegative (hsorted D) hDy (hcontained D) hQ hp.2.2.1.le hb.de_domain
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    actual_blocks_lower hg ga ab f hsorted hcontained hQ hHy hGy hBy hvar ha hz hs hθ i)
  have hcos : Real.cos (delta C.theta D)≠0 := by
    have hh := (transport_trig hb.de_domain).1
    simpa [magnitude] using (show Real.cos (magnitude C)≠0 by linarith)
  have hidentity := decomposition C hg ga ab k l c hflat hcos
  have hbase := baseline_identity (C:=C) ga ab f hb.de_domain
  have hupper := stress_nonpositive hg ga ab hp.1.le hp.2.1.le hp.2.2.1
    hzframe hb.de_domain hfeasible
  change Explicit.baseline f (aTotal C ga ab) (delta C.theta T) (magnitude C)+_≤0
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Source
end
end
end
