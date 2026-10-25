module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDESecantSupport
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHSecantSupport
public import SquaresInCircles.Eight.TableFree.GlobalGAPairedELowASource

/-!
# Actual small-A stress with negative flat-core E primaries

Uncompiled source join of Sections 4 and 6 of the two negative-E
secant-support notes. Both original A primary errors are retained with
arbitrary individual signs and a nonnegative total at most 1/6.
Each negative E primary and a selected nonpositive TD2 carry their
own positive secant multiplier. The E tangent cancels exactly.

The source theorem below includes secondary E edges at arbitrary
signed errors, and simultaneous negative DE3/EH1 when present.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELowA
open Candidate Secondary NegativePrimary PairedE

abbrev k : ℝ := PositiveATD0.lowK
abbrev l : ℝ := PositiveATD0.lowL
abbrev c : ℝ := PositiveATD0.lowC
abbrev L : ℝ := PositiveATD0.charge

def owners (hg ga ab td de eh : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,
    2,if td then 2 else 0,if de then 3 else 2,if eh then 1 else 0]

def weights (C : SignedCycle) (td de eh : Bool) : Vertex→ℝ :=
  ![k,l,l,c,if td then c/Real.cos (delta C.theta T) else c,
    if de then 1/Real.cos (delta C.theta D) else 1,
    if eh then 1/Real.cos (delta C.theta E) else 1]

def stress (C : SignedCycle) (hg ga ab td de eh : Bool) : ℝ :=
  ∑i,weights C td de eh i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab td de eh i))

def hSecantIncrement (u v : ℝ) (H : SignedPoint) : ℝ :=
  k*(edgeWidth v-1)-((u+k*Real.sin v)*H.a+k*Real.cos v*H.y)+fullSupport u k+L*v

def dSecantIncrement (u z : ℝ) (D : SignedPoint) : ℝ :=
  c*edgeWidth z+u-((u+c*Real.sin z)*D.a+c*Real.cos z*D.y)+L*z-
    (u+c)*(1-GlobalGA.Secondary.diagonal)

def hIncrement (C : SignedCycle) (hg eh : Bool) : ℝ :=
  if eh then hSecantIncrement (1/Real.cos (delta C.theta E))
    (erase (!hg) (delta C.theta H)) (C.point H)
  else PositiveATD0.pairIncrement k 1 (erase (!hg) (delta C.theta H))
    (delta C.theta E) (C.point H)

def dIncrement (C : SignedCycle) (td de : Bool) : ℝ :=
  if de then dSecantIncrement (1/Real.cos (delta C.theta D))
    (erase td (delta C.theta T)) (C.point D).reflect
  else PositiveATD0.Source.dIncrement (erase td (delta C.theta T))
    (delta C.theta D) (C.point D).reflect

def reference (C : SignedCycle) (hg ga ab td de eh : Bool) : ℝ :=
  PositiveATD0.lowBaseline+hIncrement C hg eh+
    PositiveATD0.pairIncrement k l (erase hg (delta C.theta H))
      (erase ga (delta C.theta G)) (C.point G).reflect+
    PositiveATD0.pairIncrement l c (erase ab (delta C.theta A))
      (delta C.theta B) (C.point B).reflect+dIncrement C td de

/-- The width form makes the exact collection independent of a sign
rewrite. Signs enter only in the proved scalar lower bounds. -/
def rawE (d : ℝ) : ℝ :=
  (edgeWidth d-1-(7/12)*Real.sin d)/Real.cos d

def deGain (C : SignedCycle) (de : Bool) : ℝ :=
  if de then rawE (delta C.theta D)+(1/Real.cos (delta C.theta D)-1)*(1-GlobalGA.Secondary.diagonal) else 0

def ehGain (C : SignedCycle) (eh : Bool) : ℝ :=
  if eh then rawE (delta C.theta E)+(1/Real.cos (delta C.theta E)-1)-
    (fullSupport (1/Real.cos (delta C.theta E)) k-fullSupport 1 k) else 0

def tGain (C : SignedCycle) (td : Bool) : ℝ :=
  if td then c*(edgeWidth (delta C.theta T)-Real.cos (delta C.theta T)-
    (C.point T).a*Real.sin (delta C.theta T)-
    (1-Real.cos (delta C.theta T))*(-(C.point D).y))/Real.cos (delta C.theta T) else 0

def magnitude (C : SignedCycle) (i : Vertex) (b : Bool) : ℝ :=
  -selected b (delta C.theta i)

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

private theorem r79_delta_sum (C : SignedCycle) :
    delta C.theta H+delta C.theta G+delta C.theta A+delta C.theta B+
      delta C.theta T+delta C.theta D+delta C.theta E=0 := by
  simp only [delta,next,H,G,A,B,T,D,E]
  norm_num

theorem decomposition (C : SignedCycle) (hg ga ab td de eh : Bool)
    (hflat : (C.point E).a=7/12)
    (hT : Real.cos (delta C.theta T)≠0)
    (hD : Real.cos (delta C.theta D)≠0)
    (hE : Real.cos (delta C.theta E)≠0) :
    stress C hg ga ab td de eh=reference C hg ga ab td de eh+
      L*(LowA.aTotal C ga ab-magnitude C D de-magnitude C E eh-magnitude C T td)+
      l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
      deGain C de+ehGain C eh+tGain C td := by
  have hsum := r79_delta_sum C
  have h1 : stress C hg ga ab td de eh=
      k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))+
      l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))+
      l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))+
      c*(edgeWidth (delta C.theta B)-C.edge B 2)+
      (if td then c/Real.cos (delta C.theta T) else c)*
        (edgeWidth (delta C.theta T)-C.edge T (if td then 2 else 0))+
      (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))+
      (if eh then 1/Real.cos (delta C.theta E) else 1)*
        (edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0)) := by
    simp only [stress,Fin.sum_univ_seven,weights,owners,Matrix.cons_val,H,G,A,B,T,D,E]
  -- separability of the coupled reference blocks
  have hHsep : hIncrement C hg eh=hIncrement C hg false+hIncrement C false eh-
      hIncrement C false false := by
    cases eh
    · simp only [hIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.pairIncrement,
        pairF,pairG,erase,Bool.not_false]
      ring
    · simp only [hIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.pairIncrement,
        hSecantIncrement,pairF,pairG,erase,Bool.not_false]
      ring
  have hGsep : PositiveATD0.pairIncrement k l (erase hg (delta C.theta H))
        (erase ga (delta C.theta G)) (C.point G).reflect=
      PositiveATD0.pairIncrement k l (erase hg (delta C.theta H))
        (erase false (delta C.theta G)) (C.point G).reflect+
      PositiveATD0.pairIncrement k l (erase false (delta C.theta H))
        (erase ga (delta C.theta G)) (C.point G).reflect-
      PositiveATD0.pairIncrement k l (erase false (delta C.theta H))
        (erase false (delta C.theta G)) (C.point G).reflect := by
    simp only [PositiveATD0.pairIncrement,pairF,pairG]
    ring
  have hDsep : dIncrement C td de=dIncrement C td false+dIncrement C false de-
      dIncrement C false false := by
    cases de
    · simp only [dIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.Source.dIncrement,
        PositiveATD0.dF,PositiveATD0.dG,erase]
      ring
    · simp only [dIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.Source.dIncrement,
        dSecantIncrement,PositiveATD0.dF,PositiveATD0.dG,erase]
      ring
  -- one flag at a time
  have hH : k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))=
      k*(edgeWidth (delta C.theta H)-C.edge H 0)+
      (hIncrement C hg false-hIncrement C false false)+
      (PositiveATD0.pairIncrement k l (erase hg (delta C.theta H))
        (erase false (delta C.theta G)) (C.point G).reflect-
       PositiveATD0.pairIncrement k l (erase false (delta C.theta H))
        (erase false (delta C.theta G)) (C.point G).reflect) := by
    cases hg
    · simp
    · simp only [hIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.pairIncrement,pairF,pairG,
        erase,Bool.not_false,Bool.not_true,r79_eH,zeroProjection,Matrix.cons_val,
        SignedPoint.reflect,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hG : l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))=
      l*(edgeWidth (delta C.theta G)-C.edge G 2)+
      (PositiveATD0.pairIncrement k l (erase false (delta C.theta H))
        (erase ga (delta C.theta G)) (C.point G).reflect-
       PositiveATD0.pairIncrement k l (erase false (delta C.theta H))
        (erase false (delta C.theta G)) (C.point G).reflect)+
      L*selected ga (delta C.theta G)+
      l*(if ga then edgeWidth (delta C.theta G)-1-((C.point A).a*Real.sin (delta C.theta G)+
        (C.point A).y*(1-Real.cos (delta C.theta G))) else 0) := by
    cases ga
    · simp [selected]
    · simp only [PositiveATD0.pairIncrement,pairF,pairG,erase,selected,↓reduceIte,
        Bool.false_eq_true,r79_eG,quarterProjection,Matrix.cons_val,
        SignedPoint.reflect,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hA : l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))=
      l*(edgeWidth (delta C.theta A)-C.edge A 0)+
      (PositiveATD0.pairIncrement l c (erase ab (delta C.theta A))
        (delta C.theta B) (C.point B).reflect-
       PositiveATD0.pairIncrement l c (erase false (delta C.theta A))
        (delta C.theta B) (C.point B).reflect)+
      L*selected ab (delta C.theta A)+
      l*(if ab then edgeWidth (delta C.theta A)-1-((C.point A).a*Real.sin (delta C.theta A)+
        (C.point A).y*(Real.cos (delta C.theta A)-1)) else 0) := by
    cases ab
    · simp [selected]
    · simp only [PositiveATD0.pairIncrement,pairF,pairG,erase,selected,↓reduceIte,
        Bool.false_eq_true,r79_eA,zeroProjection,Matrix.cons_val,
        SignedPoint.reflect,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hT' : (if td then c/Real.cos (delta C.theta T) else c)*
        (edgeWidth (delta C.theta T)-C.edge T (if td then 2 else 0))=
      c*(edgeWidth (delta C.theta T)-C.edge T 0)+
      (dIncrement C td false-dIncrement C false false)-
      L*magnitude C T td+tGain C td := by
    cases td
    · simp [magnitude,selected,tGain]
    · simp only [dIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.Source.dIncrement,
        PositiveATD0.dF,PositiveATD0.dG,erase,magnitude,selected,tGain,r79_eT,
        zeroProjection,Matrix.cons_val,SignedPoint.reflect,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero]
      field_simp
      ring
  have hD : (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))=
      (edgeWidth (delta C.theta D)-C.edge D 2)+
      (dIncrement C false de-dIncrement C false false)-
      L*magnitude C D de+deGain C de := by
    cases de
    · simp [magnitude,selected,deGain]
    · simp only [dIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.Source.dIncrement,
        dSecantIncrement,PositiveATD0.dF,PositiveATD0.dG,erase,magnitude,selected,deGain,rawE,
        r79_eD,quarterProjection,Matrix.cons_val,SignedPoint.reflect,hflat]
      field_simp
      ring
  have hE' : (if eh then 1/Real.cos (delta C.theta E) else 1)*
        (edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0))=
      (edgeWidth (delta C.theta E)-C.edge E 0)+
      (hIncrement C false eh-hIncrement C false false)-
      L*magnitude C E eh+ehGain C eh := by
    cases eh
    · simp [magnitude,selected,ehGain]
    · simp only [hIncrement,Bool.false_eq_true,↓reduceIte,PositiveATD0.pairIncrement,
        hSecantIncrement,pairF,pairG,erase,Bool.not_false,magnitude,selected,ehGain,rawE,
        r79_eE,quarterProjection,Matrix.cons_val,hflat,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero]
      field_simp
      ring
  have hbase : k*(edgeWidth (delta C.theta H)-C.edge H 0)+
      l*(edgeWidth (delta C.theta G)-C.edge G 2)+
      l*(edgeWidth (delta C.theta A)-C.edge A 0)+
      c*(edgeWidth (delta C.theta B)-C.edge B 2)+
      c*(edgeWidth (delta C.theta T)-C.edge T 0)+
      (edgeWidth (delta C.theta D)-C.edge D 2)+
      (edgeWidth (delta C.theta E)-C.edge E 0)=
      PositiveATD0.lowBaseline+hIncrement C false false+
      PositiveATD0.pairIncrement k l (erase false (delta C.theta H))
        (erase false (delta C.theta G)) (C.point G).reflect+
      PositiveATD0.pairIncrement l c (erase false (delta C.theta A))
        (delta C.theta B) (C.point B).reflect+
      dIncrement C false false := by
    simp only [hIncrement,dIncrement,Bool.false_eq_true,↓reduceIte,Bool.not_false,
      PositiveATD0.pairIncrement,PositiveATD0.Source.dIncrement,PositiveATD0.dF,PositiveATD0.dG,
      pairF,pairG,erase,PositiveATD0.lowBaseline,r79_eH,r79_eG,r79_eA,r79_eB,r79_eT,r79_eD,
      r79_eE,zeroProjection,quarterProjection,Matrix.cons_val,SignedPoint.reflect,
      Real.sin_zero,Real.cos_zero,edgeWidth_zero]
    linear_combination (-PositiveATD0.charge)*hsum
  rw [h1]
  simp only [reference,LowA.aTotal,total,primaryGain]
  linear_combination hH+hG+hA+hT'+hD+hE'+hbase-hHsep-hGsep-hDsep

theorem hIncrement_nonneg {q : ℝ} {C : SignedCycle} (hg eh : Bool)
    (hc : (C.point H).Contained q) (hq : q≤qCap) (hHy : 0≤(C.point H).y)
    (hvar : positiveVariation C.theta≤frameCap)
    (heh : eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ)) :
    0≤hIncrement C hg eh := by
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  cases he : eh
  · have hb := erased_pair_budgets (i := H) (j := E) hvar hn (by norm_num [H,E]) (!hg) false
    simp only [erase_false] at hb
    have hh := PositiveATD0.actual_fixed_pair_nonneg 1 hHy hc hq hb.1 hb.2
    simpa [hIncrement,PositiveATD0.coefficientP,PositiveATD0.coefficientQ,k] using hh
  · have hsec := NegativeESecant.eh_secant_range (heh he)
    simp only [Real.cos_neg] at hsec
    have hh := NegativeEHSecant.actual_lower hHy hc hq hsec
      (erase_abs_bound (!hg) (original_error_bound hvar hn H))
    dsimp [NegativeEHSecant.k,NegativeEHSecant.L] at hh
    dsimp [hIncrement,hSecantIncrement,k,L,PositiveATD0.lowK,PositiveATD0.charge]
    linarith

theorem dIncrement_nonneg {q : ℝ} {C : SignedCycle} (td de : Bool)
    (hs : (C.point D).Sorted) (hc : (C.point D).Contained q)
    (hq : q≤qCap) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hde : de=true→delta C.theta D≤0) : 0≤dIncrement C td de := by
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  cases hd : de
  · have hb := erased_pair_budgets (i := T) (j := D) hvar hn (by norm_num [T,D]) td false
    simp only [erase_false] at hb
    have he := pair_error_bounds hb.1 hb.2
    have hh := PositiveATD0.actual_D_lower (P := (C.point D).reflect)
      (by simpa using hs) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc) hq he.1 he.2.1 he.2.2
    simpa [dIncrement,PositiveATD0.Source.dIncrement,sub_nonneg] using hh
  · have hsD : -delta C.theta D∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr (hde hd),(neg_le_abs _).trans (original_error_bound hvar hn D)⟩
    have hsec := NegativeESecant.de_secant_range hsD
    simp only [Real.cos_neg] at hsec
    have hh := NegativeDESecant.actual_lower (D := (C.point D).reflect)
      (by simpa using hs) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc) hq hsec (erase_abs_bound td (original_error_bound hvar hn T))
    dsimp [NegativeDESecant.baseline,NegativeDESecant.c,NegativeDESecant.L] at hh
    dsimp [dIncrement,dSecantIncrement,c,L,PositiveATD0.lowC,PositiveATD0.charge]
    linarith

theorem reference_lower {q : ℝ} {C : SignedCycle} (hg ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ)) :
    PositiveATD0.lowBaseline≤reference C hg ga ab td de eh := by
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hgb := erased_pair_budgets (i := H) (j := G) hvar hn (by norm_num [H,G]) hg ga
  have hbb := erased_pair_budgets (i := A) (j := B) hvar hn (by norm_num [A,B]) ab false
  simp only [erase_false] at hbb
  have hG := PositiveATD0.actual_fixed_pair_nonneg 0 (P := (C.point G).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
    (by simpa using hc G) hq hgb.1 hgb.2
  have hB := PositiveATD0.actual_fixed_pair_nonneg 2 (P := (C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  have hH := hIncrement_nonneg hg eh (hc H) hq hHy hvar heh
  have hD := dIncrement_nonneg td de (hs D) (hc D) hq hDy hvar hde
  simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,Matrix.cons_val] at hG hB
  dsimp [reference,k,l,c]
  linarith

theorem raw_DE_identity {s : ℝ} (hs : s∈Icc 0 frameCap) :
    rawE (-s)+(1/Real.cos (-s)-1)*(1-GlobalGA.Secondary.diagonal)=
      NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) s := by
  rw [rawE,edgeWidth_negative_formula hs]
  simp only [Real.cos_neg,Real.sin_neg]
  dsimp [NegativeESecant.gain,NegativeESecant.K]
  field_simp [(NegativeESecant.cos_pos hs).ne']
  ring

theorem raw_EH_identity {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    rawE (-s)+(1/Real.cos (-s)-1)-
      (fullSupport (1/Real.cos (-s)) k-fullSupport 1 k)=
      secantGain qCap k s := by
  have hsi := NegativeESecant.eh_short_subset hs
  have he := secantGain_eq_secant_expression qCap k (NegativeESecant.cos_pos hsi)
  rw [he,rawE,edgeWidth_negative_formula hsi]
  simp only [Real.cos_neg,Real.sin_neg,Real.tan_eq_sin_div_cos]
  dsimp [fullSupport]
  norm_num
  field_simp [(NegativeESecant.cos_pos hsi).ne']
  ring

theorem e_gain_lower {C : SignedCycle} (de eh : Bool)
    (hsmall : ∀i,|delta C.theta i|≤frameCap)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ)) :
    L*(magnitude C D de+magnitude C E eh)≤deGain C de+ehGain C eh := by
  have hD : L*magnitude C D de≤deGain C de := by
    cases hd : de
    · simp [magnitude,selected,deGain]
    · have hs : -delta C.theta D∈Icc 0 frameCap :=
        ⟨neg_nonneg.mpr (hde hd),(neg_le_abs _).trans (hsmall D)⟩
      have hgain := NegativeESecant.de_gain_lower
        (show GlobalGA.Secondary.diagonal-1/2≤2/5 by linarith [diagonal_bounds.2]) hs
      have hid := raw_DE_identity hs
      simp only [neg_neg] at hid
      dsimp [deGain,magnitude,selected,L,PositiveATD0.charge]
      rw [hid]
      nlinarith [hs.1]
  have hH : L*magnitude C E eh≤ehGain C eh := by
    cases he : eh
    · simp [magnitude,selected,ehGain]
    · have hs := heh he
      have hgain := NegativeESecant.eh_gain_lower hs
      have hid := raw_EH_identity hs
      simp only [neg_neg] at hid
      dsimp [ehGain,magnitude,selected,L,PositiveATD0.charge]
      rw [hid]
      change ((103/100:ℝ)+1/625)*(-delta C.theta E) ≤ secantGain qCap k (-delta C.theta E) at hgain
      nlinarith [hs.1]
  linarith

theorem t_gain_lower {q : ℝ} {C : SignedCycle} (td : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcore : (C.point T).AvoidsCore) (hq : q≤qCap) (hDy : (C.point D).y≤0)
    (hsmall : |delta C.theta T|≤frameCap) (htd : td=true→delta C.theta T≤0) :
    (9/10)*c*magnitude C T td≤tGain C td := by
  cases ht : td
  · simp [magnitude,selected,tGain]
  · have hz : -delta C.theta T∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr (htd ht),(neg_le_abs _).trans hsmall⟩
    have hgain := PositiveANegativeTD.actual_gain_lower (hs T) hcore (hc T)
      (hs D) hDy (hc D) hq (show 0≤c by norm_num [c,PositiveATD0.lowC]) hz
    have hwidth := edgeWidth_negative_formula hz
    simp only [neg_neg,Real.cos_neg,Real.sin_neg] at hwidth
    have hid : tGain C true=PositiveANegativeTD.gain c (-delta C.theta T)
        (C.point T).a (-(C.point D).y) := by
      dsimp [tGain,PositiveANegativeTD.gain]
      simp only [Real.cos_neg,Real.sin_neg]
      rw [hwidth]
      ring
    simpa [hid,magnitude,selected] using hgain

/-- Every weight is nonnegative and multiplies an actual weak original
separator. The contradiction uses the proved complete scalar reserves. -/
theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hflat : (C.point E).a=7/12) (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : LowA.aTotal C ga ab∈Icc 0 (1/6:ℝ))
    (htd : td=true→delta C.theta T≤0)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ)) : False := by
  obtain ⟨hg,hHG⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hcos (i : Vertex) := NegativePrimary.cos_pos (hsmall i)
  have hTpos := hcos T
  have hDpos := hcos D
  have hEpos := hcos E
  have hweights (i : Vertex) : 0≤weights C td de eh i := by
    cases td <;> cases de <;> cases eh <;> fin_cases i <;>
      simp [weights,k,l,c,PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowC]
    all_goals positivity
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab td de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hu : stress C hg ga ab td de eh≤0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hh := hf i
    change 0≤C.edge i (owners hg ga ab td de eh i)-edgeWidth (delta C.theta i) at hh
    exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (by linarith)
  have hreference := reference_lower hg ga ab td de eh hs hc hq hHy hGy hBy hDy hvar hde heh
  have hAmem : LowA.aTotal C ga ab∈Icc 0 frameCap :=
    ⟨ha.1,ha.2.trans (by norm_num [frameCap])⟩
  have hA := selected_charge ga ab (hs A) (hc A) hq (hsmall G) (hsmall A) hAmem
  have hAweighted := mul_le_mul_of_nonneg_left hA (show 0≤l by norm_num [l,PositiveATD0.lowL])
  have hscalar := PositiveATD0.low_scalar_positive ha
  have hE := e_gain_lower de eh hsmall hde heh
  have hT := t_gain_lower td hs hc hcoreT hq hDy (hsmall T) htd
  have ht0 : 0 ≤ magnitude C T td := by
    cases ht : td
    · simp [magnitude,selected]
    · simpa [magnitude,selected] using neg_nonneg.mpr (htd ht)
  rw [decomposition C hg ga ab td de eh hflat (hcos T).ne' (hcos D).ne' (hcos E).ne'] at hu
  change l*TwoPositive.ASupport.charge (LowA.aTotal C ga ab)≤_ at hAweighted
  dsimp only [L,c,l,PositiveATD0.charge,PositiveATD0.lowC,PositiveATD0.lowL] at hu hE hT hscalar hAweighted
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELowA
